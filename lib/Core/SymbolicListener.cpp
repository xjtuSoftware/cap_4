/*
 * SymbolicListener.cpp
 *
 *  Created on: 2015年11月13日
 *      Author: zhy
 */

#include "SymbolicListener.h"

#include <llvm/ADT/StringRef.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/User.h>
#include <llvm/IR/Value.h>
#include <llvm/Support/CallSite.h>
#include <llvm/Support/Casting.h>
#include <algorithm>
#include <cassert>
#include <iostream>
#include <iterator>
#include <map>
#include <string>
#include <utility>
#include <vector>

#include "../../include/klee/Expr.h"
#include "../../include/klee/Internal/Module/Cell.h"
#include "../../include/klee/Internal/Module/InstructionInfoTable.h"
#include "../../include/klee/Internal/Module/KModule.h"
#include "../../include/klee/util/Ref.h"
#include "AddressSpace.h"
#include "Event.h"
#include "Memory.h"
#include "Thread.h"
#include "Trace.h"


using namespace std;
using namespace llvm;

#define EVENTS_DEBUG 0
#define PTR 0
#define DEBUGSTRCPY 0
#define DEBUGSYMBOLIC 0
#define COND_DEBUG 0

namespace klee {

SymbolicListener::SymbolicListener(Executor* executor, RuntimeDataManager* rdManager) :
		BitcodeListener(), executor(executor), runtimeData(rdManager) {
	Kind = SymbolicListenerKind;
	kleeBr = false;
}

SymbolicListener::~SymbolicListener() {
	// TODO Auto-generated destructor stub

}

//消息响应函数，在被测程序解释执行之前调用
void SymbolicListener::beforeRunMethodAsMain(ExecutionState &initialState) {

	//收集全局变量初始化值
	Trace* trace = runtimeData->getCurrentTrace();
	currentEvent = trace->path.begin();
	endEvent = trace->path.end();
	//收集assert
	for (std::vector<KFunction*>::iterator i =
			executor->kmodule->functions.begin(), e =
			executor->kmodule->functions.end(); i != e; ++i) {
		KInstruction **instructions = (*i)->instructions;
		for (unsigned j = 0; j < (*i)->numInstructions; j++) {
			KInstruction *ki = instructions[j];
			Instruction* inst = ki->inst;
//			instructions[j]->inst->dump();
			if (inst->getOpcode() == Instruction::Call) {
				CallSite cs(inst);
				Value *fp = cs.getCalledValue();
				Function *f = executor->getTargetFunction(fp, initialState);
				if (f && f->getName().str() == "__assert_fail") {
					string fileName = ki->info->file;
					unsigned line = ki->info->line;
					assertMap[fileName].push_back(line);
//					printf("fileName : %s, line : %d\n",fileName.c_str(),line);
//					std::cerr << "call name : " << f->getName().str() << "\n";
				}
			}
		}
	}
}


void SymbolicListener::executeInstruction(ExecutionState &state, KInstruction *ki) {
	Trace* trace = runtimeData->getCurrentTrace();
	if ((*currentEvent)) {
		Instruction* inst = ki->inst;
		Thread* thread = state.currentThread;
//		cerr << "event name : " << (*currentEvent)->eventName << " ";
//		cerr << "thread
//		cerr << "thread id : " << (*currentEvent)->threadId ;
//		(*currentEvent)->inst->inst->dump();
		switch (inst->getOpcode()) {
		case Instruction::Load: {
			ref<Expr> address = executor->eval(ki, 0, thread).value;
			if (address->getKind() == Expr::Concat) {
				ref<Expr> value = symbolicMap[filter.getGlobalName(address)];
				if (value->getKind() != Expr::Constant) {
					assert(0 && "load symbolic print");
				}
				executor->evalAgainst(ki, 0, thread, value);
			}
			break;
		}
		case Instruction::Store: {
			ref<Expr> address = executor->eval(ki, 1, thread).value;
			if (address->getKind() == Expr::Concat) {
				ref<Expr> value = symbolicMap[filter.getGlobalName(address)];
				if (value->getKind() != Expr::Constant) {
					assert(0 && "store address is symbolic");
				}
				executor->evalAgainst(ki, 1, thread, value);
			}

			ref<Expr> value = executor->eval(ki, 0, thread).value;
			ref<Expr> base = executor->eval(ki, 1, thread).value;
			Type::TypeID id = ki->inst->getOperand(0)->getType()->getTypeID();
//			cerr << "store value : " << value << std::endl;
//			cerr << "store base : " << base << std::endl;
//			cerr << "value->getKind() : " << value->getKind() << std::endl;
//			cerr << "TypeID id : " << id << std::endl;
			bool isFloat = 0;
			if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
				isFloat = 1;
			}
			if ((*currentEvent)->isGlobal) {
				if (isFloat || id == Type::IntegerTyID || id == Type::PointerTyID) {
					Expr::Width size = executor->getWidthForLLVMType(ki->inst->getOperand(0)->getType());
					ref<Expr> address = executor->eval(ki, 1, thread).value;
					ref<Expr> symbolic = manualMakeSymbolic(state,
							(*currentEvent)->globalName, size, isFloat);
					ref<Expr> constraint = EqExpr::create(value, symbolic);
					trace->storeSymbolicExpr.push_back(constraint);
//					cerr << "event name : " << (*currentEvent)->eventName << "\n";
//					cerr << "store constraint : " << constraint << "\n";
					if (value->getKind() == Expr::Constant) {

					} else if (value->getKind() == Expr::Concat || value->getKind() == Expr::Read) {
						ref<Expr> svalue = symbolicMap[filter.getGlobalName(value)];
						if (svalue->getKind() != Expr::Constant) {
							assert(0 && "store value is symbolic");
						} else if (id == Type::PointerTyID && value->getKind() == Expr::Read) {
							assert (0 && "pointer is expr::read");
						}
						executor->evalAgainst(ki, 0, thread, svalue);
					} else {
						ref<Expr> svalue = (*currentEvent)->instParameter.back();
						if (svalue->getKind() != Expr::Constant) {
							assert(0 && "store value is symbolic");
						} else 	if (id == Type::PointerTyID) {
							assert (0 && "pointer is other symbolic");
						}
						executor->evalAgainst(ki, 0, thread, svalue);
					}
				} else {
					if (value->getKind() != Expr::Constant) {
						assert(0 && "store value is symbolic and type is other");
					}
				}
			} else {
				//会丢失指针的一些关系约束，但是不影响。
				if (id == Type::PointerTyID && PTR) {
					if (value->getKind() == Expr::Concat){
						ref<Expr> svalue = symbolicMap[filter.getGlobalName(value)];
						if (svalue->getKind() != Expr::Constant) {
							assert(0 && "store pointer is symbolic");
						}
						executor->evalAgainst(ki, 0, thread, svalue);
						ref<Expr> address = executor->eval(ki, 1, thread).value;
						addressSymbolicMap[address] = value;
//						cerr << "address : " << address << " value : " << value << "\n";
					} else if (value->getKind() == Expr::Read) {
						assert (0 && "pointer is expr::read");
					} else {
						ref<Expr> address = executor->eval(ki, 1, thread).value;
						addressSymbolicMap[address] = value;
//						cerr << "address : " << address << " value : " << value << "\n";
					}
				} else if (isFloat || id == Type::IntegerTyID) {
					//局部非指针变量内存中可能存储符号值。
				} else {
					if (value->getKind() != Expr::Constant) {
						assert(0 && "store value is symbolic and type is other");
					}
				}
			}
			break;
		}
		case Instruction::Br: {
			BranchInst *bi = dyn_cast<BranchInst>(inst);
			if (!bi->isUnconditional()) {
				unsigned isAssert = 0;
				string fileName = ki->info->file;
				std::map<string, std::vector<unsigned> >::iterator it =
						assertMap.find(fileName);
				unsigned line = ki->info->line;
				if (it != assertMap.end()) {
					if (find(assertMap[fileName].begin(), assertMap[fileName].end(), line)
							!= assertMap[fileName].end()) {
						isAssert = 1;
					}
				}
				ref<Expr> value1 = executor->eval(ki, 0, thread).value;
				if (value1->getKind() != Expr::Constant) {
					Expr::Width width = value1->getWidth();
					ref<Expr> value2;
					if ((*currentEvent)->brCondition == true) {
						value2 = ConstantExpr::create(true, width);
					} else {
						value2 = ConstantExpr::create(false, width);
					}
					ref<Expr> constraint = EqExpr::create(value1, value2);
					if (isAssert) {
//						cerr << "event name : " << (*currentEvent)->eventName << "\n";
//						cerr << "assert constraint : " << constraint << "\n";
						trace->assertSymbolicExpr.push_back(constraint);
						trace->assertEvent.push_back((*currentEvent));
					} else if (kleeBr == false) {
//						cerr << "event name : " << (*currentEvent)->eventName << "\n";
//						cerr << "br constraint : " << constraint << "\n";
						trace->brSymbolicExpr.push_back(constraint);
						trace->brEvent.push_back((*currentEvent));
					}
					executor->evalAgainst(ki, 0, thread, value2);
				}
				if (kleeBr == true) {
					kleeBr = false;
				}
			}
			break;
		}
		case Instruction::Select: {

			break;
		}
		case Instruction::Call: {
			CallSite cs(inst);
			Function *f = (*currentEvent)->calledFunction;
			ref<Expr> function = executor->eval(ki, 0, thread).value;
			if (function->getKind() == Expr::Concat) {
				ref<Expr> value = symbolicMap[filter.getGlobalName(function)];
				if (value->getKind() != Expr::Constant) {
					assert(0 && "call function is symbolic");
				}
				executor->evalAgainst(ki, 0, thread, value);
			}
//			std::cerr<<"isFunctionWithSourceCode : ";
//					(*currentEvent)->inst->inst->dump();
//			std::cerr<<"isFunctionWithSourceCode : ";
//					inst->dump();
//			std::cerr<<"isFunctionWithSourceCode : "<<(*currentEvent)->isFunctionWithSourceCode<<"\n";
			if (!(*currentEvent)->isFunctionWithSourceCode) {
				unsigned numArgs = cs.arg_size();
				for (unsigned j = numArgs; j > 0; j--) {
					ref<Expr> value = executor->eval(ki, j, thread).value;
					Type::TypeID id = cs.getArgument(j-1)->getType()->getTypeID();
//					cerr << "value->getKind() : " << value->getKind() << std::endl;
//					cerr << "TypeID id : " << id << std::endl;
//		    		cerr<<"value : " << value << "\n";
					bool isFloat = 0;
					if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
						isFloat = 1;
					}
					if (isFloat || id == Type::IntegerTyID || id == Type::PointerTyID) {
						if (value->getKind() == Expr::Constant) {

						} else if (value->getKind() == Expr::Concat || value->getKind() == Expr::Read) {
							ref<Expr> svalue = symbolicMap[filter.getGlobalName(value)];
							if (svalue->getKind() != Expr::Constant) {
								assert(0 && "store value is symbolic");
							} else if (id == Type::PointerTyID && value->getKind() == Expr::Read) {
								assert (0 && "pointer is expr::read");
							}
							executor->evalAgainst(ki, j, thread, svalue);
						} else {
							ref<Expr> svalue = (*currentEvent)->instParameter[j-1];
							if (svalue->getKind() != Expr::Constant) {
								assert(0 && "store value is symbolic");
							} else 	if (id == Type::PointerTyID) {
								if (f->getName().str() == "pthread_create") {

								} else {
									assert (0 && "pointer is other symbolic");
								}
							}
							executor->evalAgainst(ki, j, thread, svalue);
						}
					} else {
						if (value->getKind() != Expr::Constant) {
							assert(0 && "store value is symbolic and type is other");
						}
					}
				}
			}
			break;
		}
		case Instruction::GetElementPtr: {
			KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
			ref<Expr> base = executor->eval(ki, 0, thread).value;
			if (base->getKind() == Expr::Concat) {
				ref<Expr> value = symbolicMap[filter.getGlobalName(base)];
				if (value->getKind() != Expr::Constant) {
					assert(0 && "GetElementPtr symbolic print");
				}
				executor->evalAgainst(ki, 0, thread, value);
			} else if (base->getKind() == Expr::Read) {
				assert (0 && "pointer is expr::read");
			}
//			std::cerr << "kgepi->base : " << base << std::endl;
			std::vector<ref<klee::Expr> >::iterator first = (*currentEvent)->instParameter.begin();
			for (std::vector<std::pair<unsigned, uint64_t> >::iterator
					it = kgepi->indices.begin(), ie = kgepi->indices.end();
					it != ie; ++it) {
				ref<Expr> index = executor->eval(ki, it->first, thread).value;
//				std::cerr << "kgepi->index : " << index << std::endl;
//				std::cerr << "first : " << *first << std::endl;
				if (index->getKind() != Expr::Constant) {
					executor->evalAgainst(ki, it->first, thread, *first);
					ref<Expr> constraint = EqExpr::create(index, *first);
//					cerr << "event name : " << (*currentEvent)->eventName << "\n";
//					cerr << "constraint : " << constraint << "\n";
					trace->brSymbolicExpr.push_back(constraint);
					trace->brEvent.push_back((*currentEvent));
				} else {
					if (index != *first) {
						assert(0 && "index != first");
					}
				}
				++first;
			}
			if (kgepi->offset) {
//				std::cerr<<"kgepi->offset : "<<kgepi->offset<<std::endl;
				//目前没有这种情况...
//				assert(0 &&"kgepi->offset");
			}
			break;
		}
		case Instruction::Switch: {
//			SwitchInst *si = cast<SwitchInst>(inst);
			ref<Expr> cond1 = executor->eval(ki, 0, thread).value;
			if (cond1->getKind() != Expr::Constant) {
				ref<Expr> cond2 = (*currentEvent)->instParameter.back();
				ref<Expr> constraint = EqExpr::create(cond1, cond2);
				trace->brSymbolicExpr.push_back(constraint);
				trace->brEvent.push_back((*currentEvent));
				executor->evalAgainst(ki, 0, thread, cond2);
			}
			break;
		}
		case Instruction::PtrToInt: {
//			CastInst *ci = cast<CastInst>(inst);
//			Expr::Width iType = executor->getWidthForLLVMType(ci->getType());
			ref<Expr> arg = executor->eval(ki, 0, thread).value;
			if (arg->getKind() == Expr::Concat) {
				ref<Expr> value = symbolicMap[filter.getGlobalName(arg)];
				if (value->getKind() != Expr::Constant) {
					assert(0 && "GetElementPtr symbolic print");
				}
				executor->evalAgainst(ki, 0, thread, value);
			} else if (arg->getKind() == Expr::Read) {
				assert (0 && "pointer is expr::read");
			}
			break;
		}
		default: {
			break;
		}
		}
	}

	Instruction *i = ki->inst;
	Thread* thread = state.currentThread;
//	cerr << "thread id : " << thread->threadId << " ";
//	i->dump();
	switch (i->getOpcode()) {
	// Control flow
	case Instruction::Ret: {
		ReturnInst *ri = cast<ReturnInst>(i);
		KInstIterator kcaller = thread->stackk.back().caller;
		Instruction *caller = kcaller ? kcaller->inst : 0;
		bool isVoidReturn = (ri->getNumOperands() == 0);
		ref<Expr> result = ConstantExpr::alloc(0, Expr::Bool);

		if (!isVoidReturn) {
			result = eval(ki, 0, thread).value;
		}

		if (thread->stackk.size() <= 1) {
			assert(!caller && "caller set on initial stack frame");
			//recover join thread
			map<unsigned, vector<unsigned> >::iterator ji = state.joinRecord.find(
					thread->threadId);
			if (ji != state.joinRecord.end()) {
				for (vector<unsigned>::iterator bi = ji->second.begin(), be =
						ji->second.end(); bi != be; bi++) {
					state.swapInThread(*bi, true, false);

					//vector clock : join
					Thread *tthread = state.findThreadById(*bi);
					for (unsigned i = 0; i < thread->vectorClock.size(); i++) {
						if (tthread->vectorClock[i] < thread->vectorClock[i]) {
							tthread->vectorClock[i] = thread->vectorClock[i];
						}
					}

				}
			}
			state.swapOutThread(thread, false, false, false, true);
			//terminateStateOnExit(state);
		} else {
			thread->popFrame();

			if (statsTracker)
				statsTracker->framePopped(state);

			if (InvokeInst *ii = dyn_cast<InvokeInst>(caller)) {
				transferToBasicBlock(ii->getNormalDest(), caller->getParent(),
						state);
			} else {
				thread->pc = kcaller;
				++thread->pc;
			}

			if (!isVoidReturn) {
				LLVM_TYPE_Q Type *t = caller->getType();
				if (t != Type::getVoidTy(getGlobalContext())) {
					// may need to do coercion due to bitcasts
					Expr::Width from = result->getWidth();
					Expr::Width to = getWidthForLLVMType(t);

					if (from != to) {
						CallSite cs = (
								isa<InvokeInst>(caller) ?
										CallSite(cast<InvokeInst>(caller)) :
										CallSite(cast<CallInst>(caller)));

						// XXX need to check other param attrs ?
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
						bool isSExt = cs.paramHasAttr(0, llvm::Attribute::SExt);
#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
						bool isSExt = cs.paramHasAttr(0, llvm::Attributes::SExt);
#else
						bool isSExt = cs.paramHasAttr(0, llvm::Attribute::SExt);
#endif
						if (isSExt) {
							result = SExtExpr::create(result, to);
						} else {
							result = ZExtExpr::create(result, to);
						}
					}

					bindLocal(kcaller, thread, result);
				}
			} else {
				// We check that the return value has no users instead of
				// checking the type, since C defaults to returning int for
				// undeclared functions.
				if (!caller->use_empty()) {
					terminateStateOnExecError(state,
							"return void when caller expected a result");
				}
			}
		}

		break;
	}
	case Instruction::Br: {
		BranchInst *bi = cast<BranchInst>(i);
		if (bi->isUnconditional()) {
			transferToBasicBlock(bi->getSuccessor(0), bi->getParent(), state);
		} else {
			// FIXME: Find a way that we don't have this hidden dependency.
			assert(
					bi->getCondition() == bi->getOperand(0)
							&& "Wrong operand index!");
			ref<Expr> cond = eval(ki, 0, thread).value;
			Executor::StatePair branches = fork(state, cond, false);

			// NOTE: There is a hidden dependency here, markBranchVisited
			// requires that we still be in the context of the branch
			// instruction (it reuses its statistic id). Should be cleaned
			// up with convenient instruction specific data.
			if (statsTracker && thread->stackk.back().kf->trackCoverage)
				statsTracker->markBranchVisited(branches.first,
						branches.second);

			if (branches.first)
				transferToBasicBlock(bi->getSuccessor(0), bi->getParent(),
						*branches.first);
			if (branches.second)
				transferToBasicBlock(bi->getSuccessor(1), bi->getParent(),
						*branches.second);
		}
		break;
	}
	case Instruction::Switch: {
		SwitchInst *si = cast<SwitchInst>(i);
		ref<Expr> cond = eval(ki, 0, thread).value;
		BasicBlock *bb = si->getParent();

		cond = toUnique(state, cond);
		if (ConstantExpr *CE = dyn_cast<ConstantExpr>(cond)) {
			// Somewhat gross to create these all the time, but fine till we
			// switch to an internal rep.
			LLVM_TYPE_Q llvm::IntegerType *Ty = cast<IntegerType>(
					si->getCondition()->getType());
			ConstantInt *ci = ConstantInt::get(Ty, CE->getZExtValue());
			unsigned index = si->findCaseValue(ci).getSuccessorIndex();
			transferToBasicBlock(si->getSuccessor(index), si->getParent(),
					state);
		} else {
			std::map<BasicBlock*, ref<Expr> > targets;
			ref<Expr> isDefault = ConstantExpr::alloc(1, Expr::Bool);
			for (SwitchInst::CaseIt i = si->case_begin(), e = si->case_end();
					i != e; ++i) {
				ref<Expr> value = evalConstant(i.getCaseValue());
				ref<Expr> match = EqExpr::create(cond, value);
				isDefault = AndExpr::create(isDefault,
						Expr::createIsZero(match));
				bool result;
				bool success = solver->mayBeTrue(state, match, result);
				assert(success && "FIXME: Unhandled solver failure");
				(void) success;
				if (result) {
					BasicBlock *caseSuccessor = i.getCaseSuccessor();
					std::map<BasicBlock*, ref<Expr> >::iterator it =
							targets.insert(
									std::make_pair(caseSuccessor,
											ConstantExpr::alloc(0, Expr::Bool))).first;

					it->second = OrExpr::create(match, it->second);
				}
			}
			bool res;
			bool success = solver->mayBeTrue(state, isDefault, res);
			assert(success && "FIXME: Unhandled solver failure");
			(void) success;
			if (res)
				targets.insert(std::make_pair(si->getDefaultDest(), isDefault));

			std::vector<ref<Expr> > conditions;
			for (std::map<BasicBlock*, ref<Expr> >::iterator it =
					targets.begin(), ie = targets.end(); it != ie; ++it)
				conditions.push_back(it->second);

			std::vector<ExecutionState*> branches;
			branch(state, conditions, branches);

			std::vector<ExecutionState*>::iterator bit = branches.begin();
			for (std::map<BasicBlock*, ref<Expr> >::iterator it =
					targets.begin(), ie = targets.end(); it != ie; ++it) {
				ExecutionState *es = *bit;
				if (es)
					transferToBasicBlock(it->first, bb, *es);
				++bit;
			}
		}
		break;
	}
	case Instruction::Unreachable:
		// Note that this is not necessarily an internal bug, llvm will
		// generate unreachable instructions in cases where it knows the
		// program will crash. So it is effectively a SEGV or internal
		// error.
//		terminateStateOnExecError(state, "reached \"unreachable\" instruction");
		break;

	case Instruction::Invoke:
	case Instruction::Call: {
		CallSite cs(i);

		unsigned numArgs = cs.arg_size();
		Value *fp = cs.getCalledValue();
		Function *f = getTargetFunction(fp, state);

		// Skip debug intrinsics, we can't evaluate their metadata arguments.
		if (f && isDebugIntrinsic(f, kmodule))
			break;

		if (isa<InlineAsm>(fp)) {
			terminateStateOnExecError(state, "inline assembly is unsupported");
			break;
		}
		// evaluate arguments
		std::vector<ref<Expr> > arguments;
		arguments.reserve(numArgs);

		for (unsigned j = 0; j < numArgs; ++j) {
			arguments.push_back(eval(ki, j + 1, thread).value);
		}

		if (f) {
			const FunctionType *fType = dyn_cast<FunctionType>(
					cast<PointerType>(f->getType())->getElementType());
			const FunctionType *fpType = dyn_cast<FunctionType>(
					cast<PointerType>(fp->getType())->getElementType());

			// special case the call with a bitcast case
			if (fType != fpType) {
				assert(fType && fpType && "unable to get function type");

				// XXX check result coercion

				// XXX this really needs thought and validation
				unsigned i = 0;
				for (std::vector<ref<Expr> >::iterator ai = arguments.begin(),
						ie = arguments.end(); ai != ie; ++ai) {
					Expr::Width to, from = (*ai)->getWidth();

					if (i < fType->getNumParams()) {
						to = getWidthForLLVMType(fType->getParamType(i));

						if (from != to) {
							// XXX need to check other param attrs ?
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
							bool isSExt = cs.paramHasAttr(i + 1,
									llvm::Attribute::SExt);
#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
							bool isSExt = cs.paramHasAttr(i+1, llvm::Attributes::SExt);
#else
							bool isSExt = cs.paramHasAttr(i+1, llvm::Attribute::SExt);
#endif
							if (isSExt) {
								arguments[i] = SExtExpr::create(arguments[i],
										to);
							} else {
								arguments[i] = ZExtExpr::create(arguments[i],
										to);
							}
						}
					}

					i++;
				}
			}

			executeCall(state, ki, f, arguments);
		} else {
			ref<Expr> v = eval(ki, 0, thread).value;

			ExecutionState *free = &state;
			bool hasInvalid = false, first = true;

			/* XXX This is wasteful, no need to do a full evaluate since we
			 have already got a value. But in the end the caches should
			 handle it for us, albeit with some overhead. */
			do {
				ref<ConstantExpr> value;
				bool success = solver->getValue(*free, v, value);
				assert(success && "FIXME: Unhandled solver failure");
				(void) success;
				StatePair res = fork(*free, EqExpr::create(v, value), true);
				if (res.first) {
#if CONSTANT
					std::cerr << "instruction of call start\n";
#endif
					uint64_t addr = value->getZExtValue();
#if CONSTANT
					std::cerr << "instruction of call start\n";
#endif
					if (legalFunctions.count(addr)) {
						f = (Function*) addr;

						// Don't give warning on unique resolution
						if (res.second || !first)
							klee_warning_once((void*) (unsigned long) addr,
									"resolved symbolic function pointer to: %s",
									f->getName().data());

						executeCall(*res.first, ki, f, arguments);
					} else {
						if (!hasInvalid) {
							terminateStateOnExecError(state,
									"invalid function pointer");
							hasInvalid = true;
						}
					}
				}

				first = false;
				free = res.second;
			} while (free);
		}
		break;
	}
	case Instruction::PHI: {
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 0)
		ref<Expr> result = eval(ki, thread->incomingBBIndex, thread).value;
#else
		ref<Expr> result = eval(ki, thread->incomingBBIndex * 2, thread).value;
#endif
		bindLocal(ki, thread, result);
		break;
	}

		// Special instructions
	case Instruction::Select: {
		SelectInst *SI = cast<SelectInst>(ki->inst);
		assert(
				SI->getCondition() == SI->getOperand(0)
						&& "Wrong operand index!");
		ref<Expr> cond = eval(ki, 0, thread).value;
		ref<Expr> tExpr = eval(ki, 1, thread).value;
		ref<Expr> fExpr = eval(ki, 2, thread).value;
		ref<Expr> result = SelectExpr::create(cond, tExpr, fExpr);
		bindLocal(ki, thread, result);
		break;
	}

	case Instruction::VAArg:
		terminateStateOnExecError(state, "unexpected VAArg instruction");
		break;

		// Arithmetic / logical

	case Instruction::Add: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		bindLocal(ki, thread, AddExpr::create(left, right));
		break;
	}

	case Instruction::Sub: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		bindLocal(ki, thread, SubExpr::create(left, right));
		break;
	}

	case Instruction::Mul: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		bindLocal(ki, thread, MulExpr::create(left, right));
		break;
	}

	case Instruction::UDiv: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		ref<Expr> result = UDivExpr::create(left, right);
		bindLocal(ki, thread, result);
		break;
	}

	case Instruction::SDiv: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		ref<Expr> result = SDivExpr::create(left, right);
		bindLocal(ki, thread, result);
		break;
	}

	case Instruction::URem: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		ref<Expr> result = URemExpr::create(left, right);
		bindLocal(ki, thread, result);
		break;
	}

	case Instruction::SRem: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		ref<Expr> result = SRemExpr::create(left, right);
		bindLocal(ki, thread, result);
		break;
	}

	case Instruction::And: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		ref<Expr> result = AndExpr::create(left, right);
		bindLocal(ki, thread, result);
		break;
	}

	case Instruction::Or: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		ref<Expr> result = OrExpr::create(left, right);
		bindLocal(ki, thread, result);
		break;
	}

	case Instruction::Xor: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		ref<Expr> result = XorExpr::create(left, right);
		bindLocal(ki, thread, result);
		break;
	}

	case Instruction::Shl: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		ref<Expr> result = ShlExpr::create(left, right);
		bindLocal(ki, thread, result);
		break;
	}

	case Instruction::LShr: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		ref<Expr> result = LShrExpr::create(left, right);
		bindLocal(ki, thread, result);
		break;
	}

	case Instruction::AShr: {
		ref<Expr> left = eval(ki, 0, thread).value;
		ref<Expr> right = eval(ki, 1, thread).value;
		ref<Expr> result = AShrExpr::create(left, right);
		bindLocal(ki, thread, result);
		break;
	}

		// Compare

	case Instruction::ICmp: {
		CmpInst *ci = cast<CmpInst>(i);
		ICmpInst *ii = cast<ICmpInst>(ci);

		switch (ii->getPredicate()) {
		case ICmpInst::ICMP_EQ: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = EqExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case ICmpInst::ICMP_NE: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = NeExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case ICmpInst::ICMP_UGT: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = UgtExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case ICmpInst::ICMP_UGE: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = UgeExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case ICmpInst::ICMP_ULT: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = UltExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case ICmpInst::ICMP_ULE: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = UleExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case ICmpInst::ICMP_SGT: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = SgtExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case ICmpInst::ICMP_SGE: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = SgeExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case ICmpInst::ICMP_SLT: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = SltExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		case ICmpInst::ICMP_SLE: {
			ref<Expr> left = eval(ki, 0, thread).value;
			ref<Expr> right = eval(ki, 1, thread).value;
			ref<Expr> result = SleExpr::create(left, right);
			bindLocal(ki, thread, result);
			break;
		}

		default:
			terminateStateOnExecError(state, "invalid ICmp predicate");
		}
		break;
	}

		// Memory instructions...
	case Instruction::Alloca: {
		AllocaInst *ai = cast<AllocaInst>(i);
		unsigned elementSize = kmodule->targetData->getTypeStoreSize(
				ai->getAllocatedType());
		ref<Expr> size = Expr::createPointer(elementSize);
		if (ai->isArrayAllocation()) {
			ref<Expr> count = eval(ki, 0, thread).value;
			count = Expr::createZExtToPointerWidth(count);
			size = MulExpr::create(size, count);
		}
		bool isLocal = i->getOpcode() == Instruction::Alloca;
		executeAlloc(state, size, isLocal, ki);
		//handle local mutex, cond and barrier
		ref<Expr> result = getDestCell(thread, ki).value;
		uint64_t startAddress =
				(dyn_cast<ConstantExpr>(result.get()))->getZExtValue();
		createSpecialElement(state, ai->getAllocatedType(), startAddress,
				false);
		break;
	}

	case Instruction::Load: {

		ref<Expr> base = eval(ki, 0, thread).value;
		executeMemoryOperation(state, false, base, 0, ki);
		break;
	}

	case Instruction::Store: {

		ref<Expr> base = eval(ki, 1, thread).value;
		ref<Expr> value = eval(ki, 0, thread).value;
		executeMemoryOperation(state, true, base, value, 0);

		//handle mutex and condition created by malloc
		Type* valueTy = ki->inst->getOperand(0)->getType();
		////handle mutex, cond and barrier allocated by malloc
		if (valueTy->isPointerTy()) {
			valueTy = valueTy->getPointerElementType();
			uint64_t startAddress =
					(dyn_cast<ConstantExpr>(value.get()))->getZExtValue();
			createSpecialElement(state, valueTy, startAddress, false);
		}
//    if (ptrTy->isStructTy()) {
//    	if (ptrTy->getStructName() == "union.pthread_mutex_t") {
//    		// handle mutex
//    		ConstantExpr* mutexAddress = dyn_cast<ConstantExpr>(value.get());
//    		string errorMsg;
//    		if (mutexAddress) {
//    			cerr << "add mutex " << mutexAddress->getZExtValue();
//    			mutexManager.addMutex(Transfer::int64toString(mutexAddress->getZExtValue()), errorMsg);
//    		} else {
//    			assert(0 && "mutex address is not const");
//    		}
//    	}
//
//    	if (ptrTy->getStructName() == "union.pthread_cond_t") {
//    		//handle condition
//    		ConstantExpr* condAddress = dyn_cast<ConstantExpr>(value.get());
//    		string errorMsg;
//    		if (condAddress) {
//    			condManager.addCondition(Transfer::int64toString(condAddress->getZExtValue()), errorMsg);
//    		} else {
//    			assert(0 && "condition address is not const");
//    		}
//    	}
//    }
		break;
	}

	case Instruction::GetElementPtr: {
		KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);
		ref<Expr> base = eval(ki, 0, thread).value;
		for (std::vector<std::pair<unsigned, uint64_t> >::iterator it =
				kgepi->indices.begin(), ie = kgepi->indices.end(); it != ie;
				++it) {
			uint64_t elementSize = it->second;
			ref<Expr> index = eval(ki, it->first, thread).value;
			base = AddExpr::create(base,
					MulExpr::create(Expr::createSExtToPointerWidth(index),
							Expr::createPointer(elementSize)));
		}
		if (kgepi->offset) {
			base = AddExpr::create(base, Expr::createPointer(kgepi->offset));
		}
		bindLocal(ki, thread, base);
		break;
	}

		// Conversion
	case Instruction::Trunc: {
		CastInst *ci = cast<CastInst>(i);
		ref<Expr> result = ExtractExpr::create(eval(ki, 0, thread).value, 0,
				getWidthForLLVMType(ci->getType()));
		bindLocal(ki, thread, result);
		break;
	}
	case Instruction::ZExt: {
		CastInst *ci = cast<CastInst>(i);
		ref<Expr> result = ZExtExpr::create(eval(ki, 0, thread).value,
				getWidthForLLVMType(ci->getType()));
		bindLocal(ki, thread, result);
		break;
	}
	case Instruction::SExt: {
		CastInst *ci = cast<CastInst>(i);
		ref<Expr> result = SExtExpr::create(eval(ki, 0, thread).value,
				getWidthForLLVMType(ci->getType()));
		bindLocal(ki, thread, result);
		break;
	}

	case Instruction::IntToPtr: {
		CastInst *ci = cast<CastInst>(i);
		Expr::Width pType = getWidthForLLVMType(ci->getType());
		ref<Expr> arg = eval(ki, 0, thread).value;
		bindLocal(ki, thread, ZExtExpr::create(arg, pType));
		break;
	}
	case Instruction::PtrToInt: {
		CastInst *ci = cast<CastInst>(i);
		Expr::Width iType = getWidthForLLVMType(ci->getType());
		ref<Expr> arg = eval(ki, 0, thread).value;
		bindLocal(ki, thread, ZExtExpr::create(arg, iType));
		break;
	}

	case Instruction::BitCast: {
		ref<Expr> result = eval(ki, 0, thread).value;
		bindLocal(ki, thread, result);
		break;
	}

		// Floating point instructions

	case Instruction::FAdd: {

		ref<Expr> originLeft = eval(ki, 0, thread).value;
		ref<Expr> originRight = eval(ki, 1, thread).value;

		ConstantExpr *leftCE = dyn_cast<ConstantExpr>(originLeft);
		ConstantExpr *rightCE = dyn_cast<ConstantExpr>(originRight);
		if (leftCE != NULL && rightCE != NULL) {
			ref<ConstantExpr> left = toConstant(state,
					eval(ki, 0, thread).value, "floating point");
			ref<ConstantExpr> right = toConstant(state,
					eval(ki, 1, thread).value, "floating point");
			if (!fpWidthToSemantics(left->getWidth())
					|| !fpWidthToSemantics(right->getWidth()))
				return terminateStateOnExecError(state,
						"Unsupported FAdd operation");

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
			llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
					left->getAPValue());
			Res.add(
					APFloat(*fpWidthToSemantics(right->getWidth()),
							right->getAPValue()), APFloat::rmNearestTiesToEven);
#else
			llvm::APFloat Res(left->getAPValue());
			Res.add(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
#endif
			ref<Expr> result = ConstantExpr::alloc(Res.bitcastToAPInt());
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
//    bindLocal(ki, thread, ConstantExpr::alloc(Res.bitcastToAPInt()));
		} else {
			ref<Expr> res = AddExpr::create(originLeft, originRight);
			res.get()->isFloat = true;
			bindLocal(ki, thread, res);
		}
		break;
	}

	case Instruction::FSub: {
		ref<Expr> originLeft = eval(ki, 0, thread).value;
		ref<Expr> originRight = eval(ki, 1, thread).value;

		ConstantExpr *leftCE = dyn_cast<ConstantExpr>(originLeft);
		ConstantExpr *rightCE = dyn_cast<ConstantExpr>(originRight);
		if (leftCE != NULL && rightCE != NULL) {
			ref<ConstantExpr> left = toConstant(state,
					eval(ki, 0, thread).value, "floating point");
			ref<ConstantExpr> right = toConstant(state,
					eval(ki, 1, thread).value, "floating point");
			if (!fpWidthToSemantics(left->getWidth())
					|| !fpWidthToSemantics(right->getWidth()))
				return terminateStateOnExecError(state,
						"Unsupported FSub operation");
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
			llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
					left->getAPValue());
			Res.subtract(
					APFloat(*fpWidthToSemantics(right->getWidth()),
							right->getAPValue()), APFloat::rmNearestTiesToEven);
#else
			llvm::APFloat Res(left->getAPValue());
			Res.subtract(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
#endif
			ref<Expr> result = ConstantExpr::alloc(Res.bitcastToAPInt());
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
		} else {
			originLeft.get()->isFloat = true;
			originRight.get()->isFloat = true;
			ref<Expr> res = SubExpr::create(originLeft, originRight);
			res.get()->isFloat = true;
			bindLocal(ki, thread, res);
		}
		break;
	}

	case Instruction::FMul: {
		ref<Expr> originLeft = eval(ki, 0, thread).value;
		ref<Expr> originRight = eval(ki, 1, thread).value;

		ConstantExpr *leftCE = dyn_cast<ConstantExpr>(originLeft);
		ConstantExpr *rightCE = dyn_cast<ConstantExpr>(originRight);
		if (leftCE != NULL && rightCE != NULL) {
			ref<ConstantExpr> left = toConstant(state,
					eval(ki, 0, thread).value, "floating point");
			ref<ConstantExpr> right = toConstant(state,
					eval(ki, 1, thread).value, "floating point");
			if (!fpWidthToSemantics(left->getWidth())
					|| !fpWidthToSemantics(right->getWidth()))
				return terminateStateOnExecError(state,
						"Unsupported FMul operation");

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
			llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
					left->getAPValue());
			Res.multiply(
					APFloat(*fpWidthToSemantics(right->getWidth()),
							right->getAPValue()), APFloat::rmNearestTiesToEven);
#else
			llvm::APFloat Res(left->getAPValue());
			Res.multiply(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
#endif
			ref<Expr> result = ConstantExpr::alloc(Res.bitcastToAPInt());
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
//    bindLocal(ki, thread, ConstantExpr::alloc(Res.bitcastToAPInt()));
		} else {
			originLeft.get()->isFloat = true;
			originRight.get()->isFloat = true;
//			cerr << "MulExpr : "<< originLeft << " * "<< originRight << "\n";
			ref<Expr> res = MulExpr::create(originLeft, originRight);
//			cerr << "MulExpr : "<< res << "\n";
			res.get()->isFloat = true;
			bindLocal(ki, thread, res);
		}
		break;
	}

	case Instruction::FDiv: {
		ref<Expr> originLeft = eval(ki, 0, thread).value;
		ref<Expr> originRight = eval(ki, 1, thread).value;

		ConstantExpr *leftCE = dyn_cast<ConstantExpr>(originLeft);
		ConstantExpr *rightCE = dyn_cast<ConstantExpr>(originRight);
		if (leftCE != NULL && rightCE != NULL) {
			ref<ConstantExpr> left = toConstant(state,
					eval(ki, 0, thread).value, "floating point");
			ref<ConstantExpr> right = toConstant(state,
					eval(ki, 1, thread).value, "floating point");
			if (!fpWidthToSemantics(left->getWidth())
					|| !fpWidthToSemantics(right->getWidth()))
				return terminateStateOnExecError(state,
						"Unsupported FDiv operation");

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
			llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
					left->getAPValue());
			Res.divide(
					APFloat(*fpWidthToSemantics(right->getWidth()),
							right->getAPValue()), APFloat::rmNearestTiesToEven);
#else
			llvm::APFloat Res(left->getAPValue());
			Res.divide(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
#endif
			ref<Expr> result = ConstantExpr::alloc(Res.bitcastToAPInt());
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
//    bindLocal(ki, thread, ConstantExpr::alloc(Res.bitcastToAPInt()));
		} else {
			originLeft.get()->isFloat = true;
			originRight.get()->isFloat = true;
			ref<Expr> result = SDivExpr::create(originLeft, originRight);
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
		}
		break;
	}

	case Instruction::FRem: {
		ref<Expr> originLeft = eval(ki, 0, thread).value;
		ref<Expr> originRight = eval(ki, 1, thread).value;

		ConstantExpr *leftCE = dyn_cast<ConstantExpr>(originLeft);
		ConstantExpr *rightCE = dyn_cast<ConstantExpr>(originRight);
		if (leftCE != NULL && rightCE != NULL) {
			ref<ConstantExpr> left = toConstant(state,
					eval(ki, 0, thread).value, "floating point");
			ref<ConstantExpr> right = toConstant(state,
					eval(ki, 1, thread).value, "floating point");
			if (!fpWidthToSemantics(left->getWidth())
					|| !fpWidthToSemantics(right->getWidth()))
				return terminateStateOnExecError(state,
						"Unsupported FRem operation");
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
			llvm::APFloat Res(*fpWidthToSemantics(left->getWidth()),
					left->getAPValue());
			Res.remainder(
					APFloat(*fpWidthToSemantics(right->getWidth()),
							right->getAPValue()));
#else
			llvm::APFloat Res(left->getAPValue());
			Res.mod(APFloat(right->getAPValue()), APFloat::rmNearestTiesToEven);
#endif
			ref<Expr> result = ConstantExpr::alloc(Res.bitcastToAPInt());
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
//    bindLocal(ki, thread, ConstantExpr::alloc(Res.bitcastToAPInt()));
		} else {
			ref<Expr> result = SRemExpr::create(originLeft, originRight);
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
		}
		break;
	}

	case Instruction::FPTrunc: {

		FPTruncInst *fi = cast<FPTruncInst>(i);
		ref<Expr> srcExpr = eval(ki, 0, thread).value;
		ConstantExpr *srcCons = dyn_cast<ConstantExpr>(srcExpr);
		if (srcCons != NULL) {
//	  FPTruncInst *fi = cast<FPTruncInst>(i);
			Expr::Width resultType = getWidthForLLVMType(fi->getType());
			ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, thread).value,
					"floating point");
			if (!fpWidthToSemantics(arg->getWidth())
					|| resultType > arg->getWidth())
				return terminateStateOnExecError(state,
						"Unsupported FPTrunc operation");

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
			llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()),
					arg->getAPValue());
#else
			llvm::APFloat Res(arg->getAPValue());
#endif
			bool losesInfo = false;
			Res.convert(*fpWidthToSemantics(resultType),
					llvm::APFloat::rmNearestTiesToEven, &losesInfo);
			ref<Expr> result = ConstantExpr::alloc(Res);
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
//    bindLocal(ki, thread, ConstantExpr::alloc(Res));
		} else {
			ref<Expr> result = ExtractExpr::create(eval(ki, 0, thread).value, 0,
					getWidthForLLVMType(fi->getType()));
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
		}
		break;
	}

	case Instruction::FPExt: {
		FPExtInst *fi = cast<FPExtInst>(i);
		ref<Expr> srcExpr = eval(ki, 0, thread).value;
		ConstantExpr *srcCons = dyn_cast<ConstantExpr>(srcExpr);
		if (srcCons != NULL) {
//    FPExtInst *fi = cast<FPExtInst>(i);
			Expr::Width resultType = getWidthForLLVMType(fi->getType());
			ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, thread).value,
					"floating point");
			if (!fpWidthToSemantics(arg->getWidth())
					|| arg->getWidth() > resultType)
				return terminateStateOnExecError(state,
						"Unsupported FPExt operation");
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
			llvm::APFloat Res(*fpWidthToSemantics(arg->getWidth()),
					arg->getAPValue());
#else
			llvm::APFloat Res(arg->getAPValue());
#endif
			bool losesInfo = false;
			Res.convert(*fpWidthToSemantics(resultType),
					llvm::APFloat::rmNearestTiesToEven, &losesInfo);
			ref<Expr> result = ConstantExpr::alloc(Res);
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
		} else {
			ref<Expr> result = SExtExpr::create(eval(ki, 0, thread).value,
					getWidthForLLVMType(fi->getType()));
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
		}
		break;
	}

	case Instruction::FPToUI: {
		FPToUIInst *fi = cast<FPToUIInst>(i);
		ref<Expr> srcExpr = eval(ki, 0, thread).value;
		ConstantExpr *srcCons = dyn_cast<ConstantExpr>(srcExpr);
		if (srcCons != NULL) {
//    FPToUIInst *fi = cast<FPToUIInst>(i);
			Expr::Width resultType = getWidthForLLVMType(fi->getType());
			ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, thread).value,
					"floating point");
			if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
				return terminateStateOnExecError(state,
						"Unsupported FPToUI operation");

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
			llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()),
					arg->getAPValue());
#else
			llvm::APFloat Arg(arg->getAPValue());
#endif
			uint64_t value = 0;
			bool isExact = true;
			Arg.convertToInteger(&value, resultType, false,
					llvm::APFloat::rmTowardZero, &isExact);
			bindLocal(ki, thread, ConstantExpr::alloc(value, resultType));
		} else {
			ref<Expr> result = ExtractExpr::alloc(eval(ki, 0, thread).value, 0,
					getWidthForLLVMType(fi->getType()));
			result.get()->isFloat = false;
			bindLocal(ki, thread, result);
		}
		break;
	}

	case Instruction::FPToSI: {

		FPToSIInst *fi = cast<FPToSIInst>(i);
		ref<Expr> srcExpr = eval(ki, 0, thread).value;
		ConstantExpr *srcCons = dyn_cast<ConstantExpr>(srcExpr);
		if (srcCons != NULL) {
//	  FPToSIInst *fi = cast<FPToSIInst>(i);
			Expr::Width resultType = getWidthForLLVMType(fi->getType());
			ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, thread).value,
					"floating point");
			if (!fpWidthToSemantics(arg->getWidth()) || resultType > 64)
				return terminateStateOnExecError(state,
						"Unsupported FPToSI operation");
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
			llvm::APFloat Arg(*fpWidthToSemantics(arg->getWidth()),
					arg->getAPValue());
#else
			llvm::APFloat Arg(arg->getAPValue());

#endif
			uint64_t value = 0;
			bool isExact = true;
			Arg.convertToInteger(&value, resultType, true,
					llvm::APFloat::rmTowardZero, &isExact);
			bindLocal(ki, thread, ConstantExpr::alloc(value, resultType));
		} else {
			ref<Expr> result = ExtractExpr::alloc(eval(ki, 0, thread).value, 0,
					getWidthForLLVMType(fi->getType()));
			result.get()->isFloat = false;
//			std::cerr << "fptosi in exe ";
//			std::cerr << result.get()->getKind() << "\n";
//			result.get()->dump();
			bindLocal(ki, thread, result);
		}
		break;
	}

	case Instruction::UIToFP: {
		UIToFPInst *fi = cast<UIToFPInst>(i);
		ref<Expr> srcExpr = eval(ki, 0, thread).value;
		ConstantExpr *srcCons = dyn_cast<ConstantExpr>(srcExpr);
		if (srcCons != NULL) {
//    UIToFPInst *fi = cast<UIToFPInst>(i);
			Expr::Width resultType = getWidthForLLVMType(fi->getType());
			ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, thread).value,
					"floating point");
			const llvm::fltSemantics *semantics = fpWidthToSemantics(
					resultType);
			if (!semantics)
				return terminateStateOnExecError(state,
						"Unsupported UIToFP operation");
			llvm::APFloat f(*semantics, 0);
			f.convertFromAPInt(arg->getAPValue(), false,
					llvm::APFloat::rmNearestTiesToEven);

			ref<Expr> result = ConstantExpr::alloc(f);
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
		} else {
			ref<Expr> result = SExtExpr::alloc(eval(ki, 0, thread).value,
					getWidthForLLVMType(fi->getType()));
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
		}
		break;
	}

	case Instruction::SIToFP: {
		SIToFPInst *fi = cast<SIToFPInst>(i);

		ref<Expr> srcExpr = eval(ki, 0, thread).value;
		ConstantExpr *srcCons = dyn_cast<ConstantExpr>(srcExpr);
		if (srcCons != NULL) {
//	  SIToFPInst *fi = cast<SIToFPInst>(i);
			Expr::Width resultType = getWidthForLLVMType(fi->getType());
			ref<ConstantExpr> arg = toConstant(state, eval(ki, 0, thread).value,
					"floating point");
			const llvm::fltSemantics *semantics = fpWidthToSemantics(
					resultType);
			if (!semantics)
				return terminateStateOnExecError(state,
						"Unsupported SIToFP operation");
			llvm::APFloat f(*semantics, 0);
			f.convertFromAPInt(arg->getAPValue(), true,
					llvm::APFloat::rmNearestTiesToEven);

			ref<Expr> result = ConstantExpr::alloc(f);
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
		} else {
			ref<Expr> result = SExtExpr::alloc(eval(ki, 0, thread).value,
					getWidthForLLVMType(fi->getType()));
			result.get()->isFloat = true;
			bindLocal(ki, thread, result);
		}
		break;
	}

	case Instruction::FCmp: {
		FCmpInst *fi = cast<FCmpInst>(i);
		ref<Expr> originLeft = eval(ki, 0, thread).value;
		ref<Expr> originRight = eval(ki, 1, thread).value;
		ConstantExpr *leftCE = dyn_cast<ConstantExpr>(originLeft);
		ConstantExpr *rightCE = dyn_cast<ConstantExpr>(originRight);
		if (leftCE != NULL && rightCE != NULL) {
//    FCmpInst *fi = cast<FCmpInst>(i);
			ref<ConstantExpr> left = toConstant(state,
					eval(ki, 0, thread).value, "floating point");
			ref<ConstantExpr> right = toConstant(state,
					eval(ki, 1, thread).value, "floating point");
			if (!fpWidthToSemantics(left->getWidth())
					|| !fpWidthToSemantics(right->getWidth()))
				return terminateStateOnExecError(state,
						"Unsupported FCmp operation");

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
			APFloat LHS(*fpWidthToSemantics(left->getWidth()),
					left->getAPValue());
			APFloat RHS(*fpWidthToSemantics(right->getWidth()),
					right->getAPValue());
#else
			APFloat LHS(left->getAPValue());
			APFloat RHS(right->getAPValue());
#endif
			APFloat::cmpResult CmpRes = LHS.compare(RHS);

			bool Result = false;
			switch (fi->getPredicate()) {
			// Predicates which only care about whether or not the operands are NaNs.
			case FCmpInst::FCMP_ORD:
				Result = CmpRes != APFloat::cmpUnordered;
				break;

			case FCmpInst::FCMP_UNO:
				Result = CmpRes == APFloat::cmpUnordered;
				break;

				// Ordered comparisons return false if either operand is NaN.  Unordered
				// comparisons return true if either operand is NaN.
			case FCmpInst::FCMP_UEQ:
				if (CmpRes == APFloat::cmpUnordered) {
					Result = true;
					break;
				}
			case FCmpInst::FCMP_OEQ:
				Result = CmpRes == APFloat::cmpEqual;
				break;

			case FCmpInst::FCMP_UGT:
				if (CmpRes == APFloat::cmpUnordered) {
					Result = true;
					break;
				}
			case FCmpInst::FCMP_OGT:
				Result = CmpRes == APFloat::cmpGreaterThan;
				break;

			case FCmpInst::FCMP_UGE:
				if (CmpRes == APFloat::cmpUnordered) {
					Result = true;
					break;
				}
			case FCmpInst::FCMP_OGE:
				Result = CmpRes == APFloat::cmpGreaterThan
						|| CmpRes == APFloat::cmpEqual;
				break;

			case FCmpInst::FCMP_ULT:
				if (CmpRes == APFloat::cmpUnordered) {
					Result = true;
					break;
				}
			case FCmpInst::FCMP_OLT:
				Result = CmpRes == APFloat::cmpLessThan;
				break;

			case FCmpInst::FCMP_ULE:
				if (CmpRes == APFloat::cmpUnordered) {
					Result = true;
					break;
				}
			case FCmpInst::FCMP_OLE:
				Result = CmpRes == APFloat::cmpLessThan
						|| CmpRes == APFloat::cmpEqual;
				break;

			case FCmpInst::FCMP_UNE:
				Result = CmpRes == APFloat::cmpUnordered
						|| CmpRes != APFloat::cmpEqual;
				break;
			case FCmpInst::FCMP_ONE:
				Result = CmpRes != APFloat::cmpUnordered
						&& CmpRes != APFloat::cmpEqual;
				break;

			default:
				assert(0 && "Invalid FCMP predicate!");
			case FCmpInst::FCMP_FALSE:
				Result = false;
				break;
			case FCmpInst::FCMP_TRUE:
				Result = true;
				break;
			}
			bindLocal(ki, thread, ConstantExpr::alloc(Result, Expr::Bool));
		} else {
			switch (fi->getPredicate()) {
			case FCmpInst::FCMP_ORD:
				break;
			case FCmpInst::FCMP_UNO:
				break;
			case FCmpInst::FCMP_UEQ:
				bindLocal(ki, thread, EqExpr::alloc(originLeft, originRight));
				break;
			case FCmpInst::FCMP_OEQ:
				bindLocal(ki, thread, EqExpr::alloc(originLeft, originRight));
				break;
			case FCmpInst::FCMP_UGT:
				bindLocal(ki, thread, SltExpr::alloc(originRight, originLeft));
				break;
			case FCmpInst::FCMP_OGT:
				bindLocal(ki, thread, SltExpr::alloc(originRight, originLeft));
				break;
			case FCmpInst::FCMP_UGE:
				bindLocal(ki, thread, SleExpr::alloc(originRight, originLeft));
				break;
			case FCmpInst::FCMP_OGE:
				bindLocal(ki, thread, SleExpr::alloc(originRight, originLeft));
				break;
			case FCmpInst::FCMP_ULT:
				bindLocal(ki, thread, SltExpr::alloc(originLeft, originRight));
				break;
			case FCmpInst::FCMP_OLT:
				bindLocal(ki, thread, SltExpr::alloc(originLeft, originRight));
				break;
			case FCmpInst::FCMP_ULE:
				bindLocal(ki, thread, SleExpr::alloc(originLeft, originRight));
				break;
			case FCmpInst::FCMP_OLE:
				bindLocal(ki, thread, SleExpr::alloc(originLeft, originRight));
				break;
			case FCmpInst::FCMP_UNE:
				bindLocal(ki, thread, NeExpr::alloc(originLeft, originRight));
				break;
			case FCmpInst::FCMP_ONE:
				bindLocal(ki, thread, NeExpr::alloc(originLeft, originRight));
				break;
			case FCmpInst::FCMP_FALSE:
				bindLocal(ki, thread, ConstantExpr::alloc(0, 1));
			case FCmpInst::FCMP_TRUE:
				bindLocal(ki, thread, ConstantExpr::alloc(1, 1));
				break;
			default:
				assert(0 && "Invalid FCMP predicate!");
				break;
			}
		}
		break;
	}
	case Instruction::InsertValue: {
		KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

		ref<Expr> agg = eval(ki, 0, thread).value;
		ref<Expr> val = eval(ki, 1, thread).value;

		ref<Expr> l = NULL, r = NULL;
		unsigned lOffset = kgepi->offset * 8, rOffset = kgepi->offset * 8
				+ val->getWidth();

		if (lOffset > 0)
			l = ExtractExpr::create(agg, 0, lOffset);
		if (rOffset < agg->getWidth())
			r = ExtractExpr::create(agg, rOffset, agg->getWidth() - rOffset);

		ref<Expr> result;
		if (!l.isNull() && !r.isNull())
			result = ConcatExpr::create(r, ConcatExpr::create(val, l));
		else if (!l.isNull())
			result = ConcatExpr::create(val, l);
		else if (!r.isNull())
			result = ConcatExpr::create(r, val);
		else
			result = val;

		bindLocal(ki, thread, result);
		break;
	}
	case Instruction::ExtractValue: {
		KGEPInstruction *kgepi = static_cast<KGEPInstruction*>(ki);

		ref<Expr> agg = eval(ki, 0, thread).value;

		ref<Expr> result = ExtractExpr::create(agg, kgepi->offset * 8,
				getWidthForLLVMType(i->getType()));

		bindLocal(ki, thread, result);
		break;
	}

		// Other instructions...
		// Unhandled
	case Instruction::ExtractElement:
	case Instruction::InsertElement:
	case Instruction::ShuffleVector:
		terminateStateOnError(state, "XXX vector instructions unhandled",
				"xxx.err");
		break;

	default:
		terminateStateOnExecError(state, "illegal instruction");
		break;
	}









}

void SymbolicListener::instructionExecuted(ExecutionState &state, KInstruction *ki) {
	Trace* trace = runtimeData->getCurrentTrace();
	if ((*currentEvent)) {
		Instruction* inst = ki->inst;
		Thread* thread = state.currentThread;
		switch (inst->getOpcode()) {
		case Instruction::Load: {
			ref<Expr> value = executor->getDestCell(state.currentThread, ki).value;
//			cerr << "value : " << value << "\n";
			bool isFloat = 0;
			Type::TypeID id = ki->inst->getType()->getTypeID();
			if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
				isFloat = 1;
			}
			if ((*currentEvent)->isGlobal) {

				//指针！！！
#if PTR
				if (isFloat || id == Type::IntegerTyID || id == Type::PointerTyID) {
#else
				if (isFloat || id == Type::IntegerTyID) {
#endif

					Expr::Width size = executor->getWidthForLLVMType(ki->inst->getType());
					ref<Expr> address = executor->eval(ki, 0, thread).value;
					ref<Expr> value = executor->getDestCell(thread, ki).value;
					ref<Expr> symbolic = manualMakeSymbolic(state,
							(*currentEvent)->globalName, size, isFloat);
					executor->setDestCell(thread, ki, symbolic);
					symbolicMap[(*currentEvent)->globalName] = value;
//					cerr << "load globalVarFullName : " << (*currentEvent)->globalVarFullName << "\n";
//					cerr << "load value : " << value << "\n";
					ref<Expr> constraint = EqExpr::create(value, symbolic);
//					cerr << "rwSymbolicExpr : " << constraint << "\n";
					trace->rwSymbolicExpr.push_back(constraint);
					trace->rwEvent.push_back(*currentEvent);
				}
			} else {
				//会丢失指针的一些关系约束，但是不影响。
				if (id == Type::PointerTyID && PTR) {
					ref<Expr> address = executor->eval(ki, 0, thread).value;
					for (std::map<ref<Expr>, ref<Expr> >::iterator it = addressSymbolicMap.begin(), ie =
							addressSymbolicMap.end(); it != ie; ++it) {
						if (it->first == address){
//							cerr << "it->first : " << it->first << " it->second : " << it->second << "\n";
							executor->setDestCell(state.currentThread, ki, it->second);
							break;
						}
					}
				} else {

				}
			}
			if (isFloat) {
				thread->stackk.back().locals[ki->dest].value.get()->isFloat =
						true;
			}
			break;
		}

		case Instruction::Store: {
			break;
		}
		case Instruction::Call: {
			CallSite cs(inst);
			Function *f = (*currentEvent)->calledFunction;
			//可能存在未知错误
//			Value *fp = cs.getCalledValue();
//			Function *f = executor->getTargetFunction(fp, state);
//			if (!f) {
//				ref<Expr> expr = executor->eval(ki, 0, thread).value;
//				ConstantExpr* constExpr = dyn_cast<ConstantExpr>(expr.get());
//				uint64_t functionPtr = constExpr->getZExtValue();
//				f = (Function*) functionPtr;
//			}

			//有待考证
//			if (!f->getName().startswith("klee") && !executor->kmodule->functionMap[f]) {
			if (!(*currentEvent)->isFunctionWithSourceCode) {
				ref<Expr> returnValue = executor->getDestCell(state.currentThread, ki).value;
				bool isFloat = 0;
				Type::TypeID id = inst->getType()->getTypeID();
				if ((id >= Type::HalfTyID) && (id <= Type::DoubleTyID)) {
					isFloat = 1;
				}
				if (isFloat) {
					returnValue.get()->isFloat = true;
				}
				executor->setDestCell(state.currentThread, ki, returnValue);
			}
//			if (!executor->kmodule->functionMap[f] && !inst->getType()->isVoidTy()) {
//				ref<Expr> value = executor->getDestCell(state.currentThread, ki).value;
//				cerr << "value : " << value << "\n";
//			}

			//需要添加Map操作
			if (f->getName().startswith("klee_div_zero_check")) {
				kleeBr = true;
			} else if (f->getName().startswith("klee_overshift_check")) {
				kleeBr = true;
//			} else if (f->getName() == "strcpy") {
//				//地址可能还有问题
//				ref<Expr> destAddress = executor->eval(ki, 1, state.currentThread).value;
////				ref<Expr> scrAddress = executor->eval(ki, 0,
////						state.currentThread).value;
////				ObjectPair scrop;
//				ObjectPair destop;
////				getMemoryObject(scrop, state, scrAddress);
//				executor->getMemoryObject(destop, state, destAddress);
//				const ObjectState* destos = destop.second;
//				const MemoryObject* destmo = destop.first;
////				std::cerr<<destAddress<<std::endl;
////				std::cerr<<destmo->address<<std::endl;
////				std::cerr<<"destmo->size : "<<destmo->size<<std::endl;
//				Expr::Width size = 8;
//				for (unsigned i = 0; i < (*currentEvent)->implicitGlobalVar.size(); i++) {
////					std::cerr<<"dest"<<std::endl;
//					ref<Expr> address = AddExpr::create(destAddress, ConstantExpr::create(i, BIT_WIDTH));
//					ref<Expr> value = destos->read(destmo->getOffsetExpr(address), size);
////					std::cerr<<"value : "<<value<<std::endl;
////					std::cerr<<"value : "<<value<<std::endl;
//					if (executor->isGlobalMO(destmo)) {
//						ref<Expr> value2 = manualMakeSymbolic(state,
//								(*currentEvent)->implicitGlobalVar[i], size, false);
//						ref<Expr> value1 = value;
//						ref<Expr> constraint = EqExpr::create(value1, value2);
//						trace->storeSymbolicExpr.push_back(constraint);
////						cerr << "constraint : " << constraint << "\n";
////						cerr << "Store Map varName : " << (*currentEvent)->varName << "\n";
////						cerr << "Store Map value : " << value << "\n";
//					}
//					if (value->isZero()) {
//						break;
//					}
//				}
			} else if (f->getName() == "pthread_create") {
				ref<Expr> pthreadAddress = executor->eval(ki, 1, state.currentThread).value;
				ObjectPair pthreadop;
				executor->getMemoryObject(pthreadop, state, pthreadAddress);
				const ObjectState* pthreados = pthreadop.second;
				const MemoryObject* pthreadmo = pthreadop.first;
				Expr::Width size = BIT_WIDTH;
				ref<Expr> value = pthreados->read(0, size);
				if (executor->isGlobalMO(pthreadmo)) {
					string globalVarFullName = (*currentEvent)->globalName;
//					cerr << "globalVarFullName : " << globalVarFullName << "\n";
					symbolicMap[globalVarFullName] = value;
				}
//				cerr << "pthread id : " << value << "\n";
			}
			break;
		}
		case Instruction::PHI: {
//			ref<Expr> result = executor->eval(ki, thread->incomingBBIndex, thread).value;
//			cerr << "PHI : " << result << "\n";
			break;
		}
		case Instruction::GetElementPtr: {
//			ref<Expr> value = executor->getDestCell(state.currentThread, ki).value;
//			cerr << "value : " << value << "\n";
			break;
		}
		case Instruction::SExt: {
//			ref<Expr> value = executor->getDestCell(state.currentThread, ki).value;
//			cerr << "value : " << value << "\n";
			break;
		}
		default: {

			break;
		}

		}
	}
	if (currentEvent != endEvent)
		currentEvent++;
}


//消息响应函数，在被测程序解释执行之后调用
void SymbolicListener::afterRunMethodAsMain() {
	symbolicMap.clear();
	addressSymbolicMap.clear();
	assertMap.clear();

	cerr << "######################本条路径为新路径####################\n";
#if EVENTS_DEBUG
	//true: output to file; false: output to terminal
	runtimeData.printCurrentTrace(true);
	//			encode.showInitTrace();//need to be modified
#endif
}


//消息相应函数，在创建了新线程之后调用
void SymbolicListener::createThread(ExecutionState &state, Thread* thread) {

}


//消息相应函数，在前缀执行出错之后程序推出之前调用
void SymbolicListener::executionFailed(ExecutionState &state, KInstruction *ki) {
	runtimeData->getCurrentTrace()->traceType = Trace::FAILED;
}

ref<Expr> SymbolicListener::manualMakeSymbolic(ExecutionState& state,
		std::string name, unsigned size, bool isFloat) {

	//添加新的符号变量
	const Array *array = new Array(name, size, isFloat);
	ObjectState *os = new ObjectState(size, array);
	ref<Expr> offset = ConstantExpr::create(0, BIT_WIDTH);
	ref<Expr> result = os->read(offset, size);
	if (isFloat) {
		result.get()->isFloat = true;
	}
#if DEBUGSYMBOLIC
	cerr << "Event name : " << (*currentEvent)->eventName << "\n";
	cerr << "make symboic:" << name << std::endl;
	cerr << "is float:" << isFloat << std::endl;
	std::cerr << "result : ";
	result->dump();
#endif
	return result;
}

ref<Expr> SymbolicListener::readExpr(ExecutionState &state, ref<Expr> address,
		Expr::Width size) {
	ObjectPair op;
	executor->getMemoryObject(op, state, address);
	const MemoryObject *mo = op.first;
	ref<Expr> offset = mo->getOffsetExpr(address);
	const ObjectState *os = op.second;
	ref<Expr> result = os->read(offset, size);
	return result;
}

void SymbolicListener::storeZeroToExpr(ExecutionState& state, ref<Expr> address,
		Expr::Width size) {

	ref<Expr> value = ConstantExpr::create(0, size);
	executor->executeMemoryOperation(state, true, address, value, 0);
}

}


