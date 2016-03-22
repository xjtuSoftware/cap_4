//===-- ExecutionState.h ----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_EXECUTIONSTATE_H
#define KLEE_EXECUTIONSTATE_H

#include <iostream>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "../../lib/Core/AddressSpace.h"
#include "../../lib/Core/BarrierManager.h"
#include "../../lib/Core/CondManager.h"
#include "../../lib/Core/Memory.h"
#include "../../lib/Core/MutexManager.h"
#include "../../lib/Core/Prefix.h"
#include "../../lib/Core/Thread.h"
#include "../../lib/Core/ThreadList.h"
#include "../../lib/Core/ThreadScheduler.h"
#include "Constraints.h"
#include "Expr.h"
#include "Internal/ADT/TreeStream.h"
#include "Internal/Module/KModule.h"
#include "util/Ref.h"

namespace klee {

std::ostream &operator<<(std::ostream &os, const MemoryMap &mm);

//struct StackFrame {
//  KInstIterator caller;
//  KFunction *kf;
//  CallPathNode *callPathNode;
//
//  std::vector<const MemoryObject*> allocas;
//  Cell *locals;
//
//  /// Minimum distance to an uncovered instruction once the function
//  /// returns. This is not a good place for this but is used to
//  /// quickly compute the context sensitive minimum distance to an
//  /// uncovered instruction. This value is updated by the StatsTracker
//  /// periodically.
//  unsigned minDistToUncoveredOnReturn;
//
//  // For vararg functions: arguments not passed via parameter are
//  // stored (packed tightly) in a local (alloca) memory object. This
//  // is setup to match the way the front-end generates vaarg code (it
//  // does not pass vaarg through as expected). VACopy is lowered inside
//  // of intrinsic lowering.
//  MemoryObject *varargs;
//
//  StackFrame(KInstIterator caller, KFunction *kf);
//  StackFrame(const StackFrame &s);
//  ~StackFrame();
//};

class ExecutionState {
//public:
//  typedef std::vector<StackFrame> stack_ty;

	private:
		// unsupported, use copy constructor
		ExecutionState &operator=(const ExecutionState&);
		std::map<std::string, std::string> fnAliases;

	public:
		bool fakeState;
		// Are we currently underconstrained?  Hack: value is size to make fake
		// objects.
		unsigned underConstrained;
		unsigned depth;
		// pc - pointer to current instruction stream
//  KInstIterator pc, prevPC;
//  stack_ty stack;
		ConstraintManager constraints;
		mutable double queryCost;
		double weight;
		AddressSpace addressSpace;
		TreeOStream pathOS, symPathOS;
		unsigned instsSinceCovNew;
		bool coveredNew;

		/// Disables forking, set by user code.
		bool forkDisabled;

		std::map<const std::string*, std::set<unsigned> > coveredLines;
		//PTreeNode *ptreeNode;

		/// ordered list of symbolics: used to generate test cases.
		//
		// FIXME: Move to a shared list structure (not critical).
		typedef std::vector<std::pair<const MemoryObject*, const Array*> > symbolicList;
		std::vector<std::pair<const MemoryObject*, const Array*> > symbolics;

		/// Set of used array names.  Used to avoid collisions.
		std::set<std::string> arrayNames;

		// Used by the checkpoint/rollback methods for fake objects.
		// FIXME: not freeing things on branch deletion.
		MemoryMap shadowObjects;

		//unsigned incomingBBIndex;

		std::string getFnAlias(std::string fn);
		void addFnAlias(std::string old_fn, std::string new_fn);
		void removeFnAlias(std::string fn);

		//add by ylc to support pthread
//  unsigned threadId;
//  ExecutionState* parentThread;
//  enum ThreadState {
//	  INITIAL,
//	  RUNNABLE,
//	  RUNNING,
//	  BLOCKED,
//	  WAITING,
//	  TERMINATED,
//	  LOCKED
//  };
//
//  ThreadState threadState;
		unsigned nextThreadId;
		ThreadScheduler* threadScheduler;
		ThreadList threadList;
		Thread* currentThread;

		MutexManager mutexManager;
		CondManager condManager;
		BarrierManager barrierManager;
		std::map<unsigned, std::vector<unsigned> > joinRecord;

	public:
		ExecutionState(KFunction *kf);

		ExecutionState(KFunction *kf, Prefix* prefix);
		// XXX total hack, just used to make a state so solver can
		// use on structure
		ExecutionState(const std::vector<ref<Expr> > &assumptions);

		ExecutionState(const ExecutionState& state);

//  //add by ylc to support pthread
//  ExecutionState(KFunction* kf, ExecutionState& state);

		~ExecutionState();

		ExecutionState *branch();

//  void pushFrame(KInstIterator caller, KFunction *kf);
//  void popFrame();

		void addSymbolic(const MemoryObject *mo, const Array *array);
		void addConstraint(ref<Expr> e) {
			constraints.addConstraint(e);
		}

		bool merge(const ExecutionState &b);

		Thread* findThreadById(unsigned threadId);

		Thread* getNextThread();

		Thread* getCurrentThread();

		bool examineAllThreadFinalState();

		unsigned getNextThreadId();

		Thread* createThread(KFunction *kf);

		Thread* createThread(KFunction *kf, unsigned threadId);

		void swapOutThread(Thread* thread, bool isCondBlocked, bool isBarrierBlocked,
				bool isJoinBlocked, bool isTerminated);

		void swapInThread(Thread* thread, bool isRunnable, bool isMutexBlocked);

		void swapOutThread(unsigned threadId, bool isCondBlocked, bool isBarrierBlocked,
				bool isJoinBlocked, bool isTerminated);

		void swapInThread(unsigned threadId, bool isRunnable, bool isMutexBlocked);

		void switchThreadToMutexBlocked(Thread* thread);

		void switchThreadToMutexBlocked(unsigned threadId);

		void switchThreadToRunnable(Thread* thread);

		void switchThreadToRunnable(unsigned threadId);

		void reSchedule();

		void dumpStack(std::ostream &out) const;

};

}

#endif
