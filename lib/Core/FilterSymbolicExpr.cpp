#ifndef LIB_CORE_FILTERSYMBOLICEXPR_C_
#define LIB_CORE_FILTERSYMBOLICEXPR_C_

#include "FilterSymbolicExpr.h"

#include <llvm/IR/Constant.h>
#include <llvm/IR/Instruction.h>
#include <llvm/Support/Casting.h>
#include <cassert>
#include <iostream>
#include <iterator>
#include <map>
#include <sstream>
#include <utility>

#include "../../include/klee/Internal/Module/KInstruction.h"
#include "Event.h"

#define DEBUG 0
#define OPTIMIZATION1 1

namespace klee {

std::string FilterSymbolicExpr::getName(ref<klee::Expr> value) {
	std::string globalName = getGlobalName(value);
	std::string name = getName(globalName);
	return name;
}

std::string FilterSymbolicExpr::getName(std::string globalName) {
	std::stringstream name;
	name.str("");
	unsigned int i = 0;
	while ((globalName.at(i) != 'S') && (globalName.at(i) != 'L')) {
		name << globalName.at(i);
		i++;
	}
	return name.str();
}

std::string FilterSymbolicExpr::getGlobalName(ref<klee::Expr> value) {

	ReadExpr *revalue;
	if (value->getKind() == Expr::Concat) {
		ConcatExpr *ccvalue = cast<ConcatExpr>(value);
		revalue = cast<ReadExpr>(ccvalue->getKid(0));
	} else if (value->getKind() == Expr::Read) {
		revalue = cast<ReadExpr>(value);
	} else {
		assert(0 && "getGlobalName");
	}
	std::string globalName = revalue->updates.root->name;
	return globalName;
}

void FilterSymbolicExpr::resolveSymbolicExpr(ref<klee::Expr> symbolicExpr, std::set<std::string> &relatedSymbolicExpr) {
	if (symbolicExpr->getKind() == Expr::Read) {
		std::string name = getName(symbolicExpr);
		if (relatedSymbolicExpr.find(name) == relatedSymbolicExpr.end()) {
			relatedSymbolicExpr.insert(name);
		}
		return;
	} else {
		unsigned kidsNum = symbolicExpr->getNumKids();
		if (kidsNum == 2 && symbolicExpr->getKid(0) == symbolicExpr->getKid(1)) {
			resolveSymbolicExpr(symbolicExpr->getKid(0), relatedSymbolicExpr);
		} else {
			for (unsigned int i = 0; i < kidsNum; i++) {
				resolveSymbolicExpr(symbolicExpr->getKid(i), relatedSymbolicExpr);
			}
		}
	}
}

void FilterSymbolicExpr::resolveTaintExpr(ref<klee::Expr> taintExpr, std::vector<ref<klee::Expr> > &relatedTaintExpr,
		bool &isTaint) {
	if (taintExpr->getKind() == Expr::Concat || taintExpr->getKind() == Expr::Read) {
		unsigned i;
		for (i = 0; i < relatedTaintExpr.size(); i++) {
			if (relatedTaintExpr[i] == taintExpr) {
				break;
			}
		}
		if (i == relatedTaintExpr.size()) {
			relatedTaintExpr.push_back(taintExpr);
			if (taintExpr->isTaint) {
				isTaint = true;
			}
		}
		return;
	} else if (taintExpr->getKind() == Expr::Constant) {
		if (taintExpr->isTaint) {
			isTaint = true;
		}
	} else {
		unsigned kidsNum = taintExpr->getNumKids();
		if (kidsNum == 2 && taintExpr->getKid(0) == taintExpr->getKid(1)) {
			resolveTaintExpr(taintExpr->getKid(0), relatedTaintExpr, isTaint);
		} else {
			for (unsigned int i = 0; i < kidsNum; i++) {
				resolveTaintExpr(taintExpr->getKid(i), relatedTaintExpr, isTaint);
			}
		}
	}
}

void FilterSymbolicExpr::addExprToSet(std::set<std::string> *Expr, std::set<std::string> *relatedSymbolicExpr) {

	for (std::set<std::string>::iterator it = Expr->begin(), ie = Expr->end(); it != ie; ++it) {
		std::string name = *it;
		if (relatedSymbolicExpr->find(name) == relatedSymbolicExpr->end()) {
			relatedSymbolicExpr->insert(name);
		}
	}
}

void FilterSymbolicExpr::addExprToVector(std::vector<std::string> *Expr,
		std::vector<std::string> *relatedSymbolicExpr) {
	for (std::vector<std::string>::iterator it = Expr->begin(), ie = Expr->end(); it != ie; ++it) {
		std::string nvarName = *it;
		bool isFind = false;
		for (std::vector<std::string>::iterator itt = relatedSymbolicExpr->begin(), iee = relatedSymbolicExpr->end();
				itt != iee; ++itt) {
			if (*itt == nvarName) {
				isFind = true;
			}
		}
		if (!isFind) {
			relatedSymbolicExpr->push_back(nvarName);
		}
	}
}

void FilterSymbolicExpr::addExprToVector(std::set<std::string> *Expr, std::vector<std::string> *relatedSymbolicExpr) {

	for (std::set<std::string>::iterator it = Expr->begin(), ie = Expr->end(); it != ie; ++it) {
		std::string varName = *it;
		bool isFind = false;
		for (std::vector<std::string>::iterator itt = relatedSymbolicExpr->begin(), iee = relatedSymbolicExpr->end();
				itt != iee; ++itt) {
			if (*itt == varName) {
				isFind = true;
			}
		}
		if (!isFind) {
			relatedSymbolicExpr->push_back(varName);
		}
	}
}

bool FilterSymbolicExpr::isRelated(std::string varName) {
	if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
		return true;
	} else {
		return false;
	}
}

void FilterSymbolicExpr::fillterTrace(Trace* trace, std::set<std::string> RelatedSymbolicExpr) {
	std::string name;

	//PathCondition
	std::vector<ref<klee::Expr> > &pathCondition = trace->pathCondition;
	std::vector<ref<klee::Expr> > &pathConditionRelatedToBranch = trace->pathConditionRelatedToBranch;
	pathConditionRelatedToBranch.clear();
	for (std::vector<ref<Expr> >::iterator it = pathCondition.begin(), ie = pathCondition.end(); it != ie; ++it) {
		name = getName(it->get()->getKid(1));
		if (RelatedSymbolicExpr.find(name) != RelatedSymbolicExpr.end() || !OPTIMIZATION1) {
			pathConditionRelatedToBranch.push_back(*it);
		}
	}

	//readSet
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	std::map<std::string, std::vector<Event *> > &readSetRelatedToBranch = trace->readSetRelatedToBranch;
	readSetRelatedToBranch.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit = readSet.begin(), nie = readSet.end(); nit != nie;
			++nit) {
		name = nit->first;
		if (RelatedSymbolicExpr.find(name) != RelatedSymbolicExpr.end() || !OPTIMIZATION1) {
			readSetRelatedToBranch.insert(*nit);
		}
	}

	//writeSet
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	std::map<std::string, std::vector<Event *> > &writeSetRelatedToBranch = trace->writeSetRelatedToBranch;
	writeSetRelatedToBranch.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit = writeSet.begin(), nie = writeSet.end();
			nit != nie; ++nit) {
		name = nit->first;
		if (RelatedSymbolicExpr.find(name) != RelatedSymbolicExpr.end() || !OPTIMIZATION1) {
			writeSetRelatedToBranch.insert(*nit);
		}
	}

	//global_variable_initializer
	std::map<std::string, llvm::Constant*> &global_variable_initializer = trace->global_variable_initializer;
	std::map<std::string, llvm::Constant*> &global_variable_initisalizer_RelatedToBranch =
			trace->global_variable_initializer_RelatedToBranch;
	global_variable_initisalizer_RelatedToBranch.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit = global_variable_initializer.begin(), nie =
			global_variable_initializer.end(); nit != nie; ++nit) {
		name = nit->first;
		if (RelatedSymbolicExpr.find(name) != RelatedSymbolicExpr.end() || !OPTIMIZATION1) {
			global_variable_initisalizer_RelatedToBranch.insert(*nit);
		}
	}

	//event
	for (std::vector<Event*>::iterator currentEvent = trace->path.begin(), endEvent = trace->path.end();
			currentEvent != endEvent; currentEvent++) {
		if ((*currentEvent)->isGlobal == true) {
			if ((*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Load
					|| (*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Store) {
				if (RelatedSymbolicExpr.find((*currentEvent)->name) == RelatedSymbolicExpr.end() && OPTIMIZATION1) {
					(*currentEvent)->isEventRelatedToBranch = false;
				} else {
					(*currentEvent)->isEventRelatedToBranch = true;
				}
			}
		}
	}
}

void FilterSymbolicExpr::filterUseless(Trace* trace) {

	std::string varName;
	std::vector<std::string> remainingExprVarName;
	std::vector<ref<klee::Expr> > remainingExpr;
	allRelatedSymbolicExpr.clear();
	remainingExprVarName.clear();
	remainingExpr.clear();
	std::vector<ref<klee::Expr> > &storeSymbolicExpr = trace->storeSymbolicExpr;
	for (std::vector<ref<Expr> >::iterator it = storeSymbolicExpr.begin(), ie = storeSymbolicExpr.end(); it != ie;
			++it) {
		varName = getName(it->get()->getKid(1));
		remainingExprVarName.push_back(varName);
		remainingExpr.push_back(it->get());
	}
#if DEBUG
	std::cerr << "\n storeSymbolicExpr " << std::endl;
	for (std::vector<ref<Expr> >::iterator it = storeSymbolicExpr.begin(),
			ie = storeSymbolicExpr.end(); it != ie; ++it) {
		std::cerr << *it << std::endl;
	}
#endif

	//br
	std::vector<ref<klee::Expr> > &brSymbolicExpr = trace->brSymbolicExpr;
	std::vector<std::set<std::string>*> &brRelatedSymbolicExpr = trace->brRelatedSymbolicExpr;
	for (std::vector<ref<Expr> >::iterator it = brSymbolicExpr.begin(), ie = brSymbolicExpr.end(); it != ie; ++it) {
		std::set<std::string> *tempSymbolicExpr = new std::set<std::string>;
		resolveSymbolicExpr(it->get(), *tempSymbolicExpr);
		brRelatedSymbolicExpr.push_back(tempSymbolicExpr);
		addExprToSet(tempSymbolicExpr, &allRelatedSymbolicExpr);
#if DEBUG
		std::cerr << "\n" << *it << "\n brRelatedSymbolicExpr " << std::endl;
		for (std::set<std::string>::iterator it = tempSymbolicExpr->begin(),
				ie = tempSymbolicExpr->end(); it != ie; ++it) {
			std::cerr << *it << std::endl;
		}
#endif
	}

	//assert
	std::vector<ref<klee::Expr> > &assertSymbolicExpr = trace->assertSymbolicExpr;
	std::vector<std::set<std::string>*> &assertRelatedSymbolicExpr = trace->assertRelatedSymbolicExpr;
	for (std::vector<ref<Expr> >::iterator it = assertSymbolicExpr.begin(), ie = assertSymbolicExpr.end(); it != ie;
			++it) {
		std::set<std::string> *tempSymbolicExpr = new std::set<std::string>;
		resolveSymbolicExpr(it->get(), *tempSymbolicExpr);
		assertRelatedSymbolicExpr.push_back(tempSymbolicExpr);
		addExprToSet(tempSymbolicExpr, &allRelatedSymbolicExpr);
#if DEBUG
		std::cerr << "\n" << *it << "\n assertRelatedSymbolicExpr " << std::endl;
		for (std::set<std::string>::iterator it = tempSymbolicExpr->begin(),
				ie = tempSymbolicExpr->end(); it != ie; ++it) {
			std::cerr << *it << std::endl;
		}
#endif
	}

#if DEBUG
	std::cerr << "\n allRelatedSymbolicExpr " << std::endl;
	for (std::set<std::string>::iterator it = allRelatedSymbolicExpr.begin(),
			ie = allRelatedSymbolicExpr.end(); it != ie; ++it) {
		std::cerr << *it << std::endl;
	}
#endif

	std::vector<ref<klee::Expr> > &kQueryExpr = trace->pathCondition;
	std::map<std::string, std::set<std::string>*> &varRelatedSymbolicExpr = trace->varRelatedSymbolicExpr;
	for (std::set<std::string>::iterator nit = allRelatedSymbolicExpr.begin(); nit != allRelatedSymbolicExpr.end();
			++nit) {
		varName = *nit;
		std::vector<ref<Expr> >::iterator itt = remainingExpr.begin();
		for (std::vector<std::string>::iterator it = remainingExprVarName.begin(), ie = remainingExprVarName.end();
				it != ie;) {
			if (varName == *it) {
				remainingExprVarName.erase(it);
				--ie;
				kQueryExpr.push_back(*itt);

				std::set<std::string> *tempSymbolicExpr = new std::set<std::string>;
				resolveSymbolicExpr(itt->get(), *tempSymbolicExpr);
				if (varRelatedSymbolicExpr.find(varName) != varRelatedSymbolicExpr.end()) {
					addExprToSet(tempSymbolicExpr, varRelatedSymbolicExpr[varName]);
				} else {
					varRelatedSymbolicExpr[varName] = tempSymbolicExpr;
				}
				addExprToSet(tempSymbolicExpr, &allRelatedSymbolicExpr);
#if DEBUG
				std::cerr << "\n" << name << "\n varRelatedSymbolicExpr " << std::endl;
				std::cerr << *itt << "\n";
				for (std::set<std::string>::iterator it = tempSymbolicExpr->begin(),
						ie = tempSymbolicExpr->end(); it != ie; ++it) {
					std::cerr << *it << std::endl;
				}
#endif
				remainingExpr.erase(itt);
			} else {
				++it;
				++itt;
			}
		}
	}

#if DEBUG
	std::cerr << "\n" << name << "\n varRelatedSymbolicExpr " << std::endl;
	for (std::map<std::string, std::set<std::string>* >::iterator nit = varRelatedSymbolicExpr.begin();
			nit != varRelatedSymbolicExpr.end(); ++nit) {
		std::cerr << "name : " << (*nit).first << "\n";
		for (std::set<std::string>::iterator it = (*nit).second->begin(),
				ie = (*nit).second->end(); it != ie; ++it) {
			std::cerr << *it << std::endl;
		}
	}
#endif

	std::map<std::string, long> &varThread = trace->varThread;

	std::map<std::string, std::vector<Event *> > usefulReadSet;
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	std::map<std::string, std::vector<Event *> > &allReadSet = trace->allReadSet;
	usefulReadSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit = readSet.begin(), nie = readSet.end(); nit != nie;
			++nit) {
		allReadSet.insert(*nit);
		varName = nit->first;
//		std::cerr << "allReadSet varName : " << varName << "\n";
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end() || !OPTIMIZATION1) {
			usefulReadSet.insert(*nit);
			if (varThread.find(varName) == varThread.end()) {
				varThread[varName] = (*(nit->second.begin()))->threadId;
			}
			long id = varThread[varName];
			if (id != 0) {
				for (std::vector<Event *>::iterator it = nit->second.begin(), ie = nit->second.end(); it != ie; ++it) {
					if (id != (*it)->threadId) {
						varThread[varName] = 0;
						break;
					}
				}
			}

		}

	}
	readSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit = usefulReadSet.begin(), nie = usefulReadSet.end();
			nit != nie; ++nit) {
		readSet.insert(*nit);
	}

	std::map<std::string, std::vector<Event *> > usefulWriteSet;
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	std::map<std::string, std::vector<Event *> > &allWriteSet = trace->allWriteSet;
	usefulWriteSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit = writeSet.begin(), nie = writeSet.end();
			nit != nie; ++nit) {
		allWriteSet.insert(*nit);
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end() || !OPTIMIZATION1) {
			usefulWriteSet.insert(*nit);
			if (varThread.find(varName) == varThread.end()) {
				varThread[varName] = (*(nit->second.begin()))->threadId;
			}
			long id = varThread[varName];
			if (id != 0) {
				for (std::vector<Event *>::iterator it = nit->second.begin(), ie = nit->second.end(); it != ie; ++it) {
					if (id != (*it)->threadId) {
						varThread[varName] = 0;
						break;
					}
				}
			}
		}
	}
	writeSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit = usefulWriteSet.begin(), nie =
			usefulWriteSet.end(); nit != nie; ++nit) {
		writeSet.insert(*nit);
	}

	for (std::map<std::string, long>::iterator nit = varThread.begin(), nie = varThread.end(); nit != nie; ++nit) {
		if (usefulWriteSet.find((*nit).first) == usefulWriteSet.end()) {
			(*nit).second = -1;
		}
	}

#if DEBUG
	std::cerr << "varThread\n";
	for (std::map<std::string, long>::iterator nit =
			varThread.begin(), nie = varThread.end(); nit != nie; ++nit) {
		std::cerr << nit->first << " : " << nit->second << "\n";
	}
#endif

	std::map<std::string, llvm::Constant*> usefulGlobal_variable_initializer;
	std::map<std::string, llvm::Constant*> &global_variable_initializer = trace->global_variable_initializer;
	usefulGlobal_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit = global_variable_initializer.begin(), nie =
			global_variable_initializer.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end() || !OPTIMIZATION1) {
			usefulGlobal_variable_initializer.insert(*nit);
		}
	}
	global_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit = usefulGlobal_variable_initializer.begin(), nie =
			usefulGlobal_variable_initializer.end(); nit != nie; ++nit) {
		global_variable_initializer.insert(*nit);
	}

//	std::vector<std::vector<Event*>*> eventList = trace->eventList;
	for (std::vector<Event*>::iterator currentEvent = trace->path.begin(), endEvent = trace->path.end();
			currentEvent != endEvent; currentEvent++) {
		if ((*currentEvent)->isGlobal == true) {
			if ((*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Load
					|| (*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Store) {
				if (allRelatedSymbolicExpr.find((*currentEvent)->name) == allRelatedSymbolicExpr.end() && OPTIMIZATION1) {
//					(*currentEvent)->isGlobal = false;
					(*currentEvent)->isEventRelatedToBranch = false;
				} else {
					(*currentEvent)->isEventRelatedToBranch = true;
				}
			} else {
				(*currentEvent)->isEventRelatedToBranch = true;
			}
		}
	}

	std::vector<ref<klee::Expr> > usefulRwSymbolicExpr;
	std::vector<ref<klee::Expr> > &rwSymbolicExpr = trace->rwSymbolicExpr;
	usefulGlobal_variable_initializer.clear();
	for (std::vector<ref<klee::Expr> >::iterator nit = rwSymbolicExpr.begin(), nie = rwSymbolicExpr.end(); nit != nie;
			++nit) {
		varName = getName((*nit)->getKid(1));
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end() || !OPTIMIZATION1) {
			usefulRwSymbolicExpr.push_back(*nit);
		}
	}
	rwSymbolicExpr.clear();
	for (std::vector<ref<klee::Expr> >::iterator nit = usefulRwSymbolicExpr.begin(), nie = usefulRwSymbolicExpr.end();
			nit != nie; ++nit) {
		rwSymbolicExpr.push_back(*nit);
	}

	fillterTrace(trace, allRelatedSymbolicExpr);

}

bool FilterSymbolicExpr::filterUselessWithSet(Trace* trace, std::set<std::string>* relatedSymbolicExpr) {
	bool branch = false;
	std::set<std::string> &RelatedSymbolicExpr = trace->RelatedSymbolicExpr;
	RelatedSymbolicExpr.clear();
#if DEBUG
	std::cerr << "\n relatedSymbolicExpr " << std::endl;
	for (std::set<std::string>::iterator it = relatedSymbolicExpr->begin(),
			ie = relatedSymbolicExpr->end(); it != ie; ++it) {
		std::cerr << *it << std::endl;
	}
#endif
	addExprToSet(relatedSymbolicExpr, &RelatedSymbolicExpr);

	std::string varName;
	std::map<std::string, std::set<std::string>*> &varRelatedSymbolicExpr = trace->varRelatedSymbolicExpr;
	for (std::set<std::string>::iterator nit = RelatedSymbolicExpr.begin(); nit != RelatedSymbolicExpr.end(); ++nit) {
		varName = *nit;
#if DEBUG
		std::cerr << "\n varName : " << name << std::endl;
#endif
		if (varRelatedSymbolicExpr.find(varName) != varRelatedSymbolicExpr.end()) {
			addExprToSet(varRelatedSymbolicExpr[varName], &RelatedSymbolicExpr);
		}
#if DEBUG
		std::cerr << "\n addExprToSet(relatedSymbolicExpr, &RelatedSymbolicExpr); " << std::endl;
#endif
	}
#if DEBUG
	std::cerr << "\n RelatedSymbolicExpr " << std::endl;
	for (std::set<std::string>::iterator it = RelatedSymbolicExpr.begin(),
			ie = RelatedSymbolicExpr.end(); it != ie; ++it) {
		std::cerr << *it << std::endl;
	}
#endif

	std::map<std::string, long> &varThread = trace->varThread;
	for (std::set<std::string>::iterator it = RelatedSymbolicExpr.begin(), ie = RelatedSymbolicExpr.end(); it != ie;
			++it) {
		if (varThread[*it] == 0) {
			branch = true;
			break;
		}
	}
	if (branch) {
//		fillterTrace(trace, RelatedSymbolicExpr);
		return true;
	} else {
		return false;
	}
}

void FilterSymbolicExpr::filterUselessByTaint(Trace* trace) {

	std::set<std::string> &taintSymbolicExpr = trace->taintSymbolicExpr;
	std::vector<std::string> taint;
	for (std::set<std::string>::iterator it = taintSymbolicExpr.begin(), ie = taintSymbolicExpr.end(); it != ie; it++) {
		taint.push_back(*it);
	}
	std::set<std::string> &unTaintSymbolicExpr = trace->unTaintSymbolicExpr;
	std::vector<std::string> unTaint;
	for (std::set<std::string>::iterator it = unTaintSymbolicExpr.begin(), ie = unTaintSymbolicExpr.end(); it != ie;
			it++) {
		unTaint.push_back(*it);
	}
	std::set<std::string> &potentialTaintSymbolicExpr = trace->potentialTaint;
	std::map<std::string, std::set<std::string>*> &varRelatedSymbolicExpr = trace->varRelatedSymbolicExpr;
	std::string varName;

	for (std::vector<std::string>::iterator it = taint.begin(); it != taint.end(); it++) {
		varName = *it;
		for (std::vector<std::string>::iterator itt = unTaint.begin(); itt != unTaint.end();) {
			if (varRelatedSymbolicExpr.find(*itt) == varRelatedSymbolicExpr.end()) {
				itt++;
			} else if (varRelatedSymbolicExpr[*itt]->find(varName) != varRelatedSymbolicExpr[*itt]->end()) {
				taint.push_back(*itt);
				unTaint.erase(itt);
			} else {
				itt++;
			}
		}
	}

	std::cerr << "filterUselessByTaint\n";
	for (std::vector<std::string>::iterator it = taint.begin(), ie = taint.end(); it != ie; it++) {
		varName = *it;
		std::cerr << "taint : " << varName << "\n";
		if (taintSymbolicExpr.find(varName) == taintSymbolicExpr.end()) {
			potentialTaintSymbolicExpr.insert(varName);
		}
	}

}

}

#endif /* LIB_CORE_FILTERSYMBOLICEXPR_C_ */
