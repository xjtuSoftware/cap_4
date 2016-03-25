/*
 * Thread.h
 *
 *  Created on: 2015年1月5日
 *      Author: berserker
 */

#ifndef LIB_CORE_THREAD_H_
#define LIB_CORE_THREAD_H_

#include <vector>

#include "../../include/klee/Internal/Module/KInstIterator.h"
#include "../../include/klee/Internal/Module/KModule.h"
#include "AddressSpace.h"
#include "StackType.h"

namespace klee {



class Thread {
public:

		enum ThreadState {
	  RUNNABLE,
	  MUTEX_BLOCKED,
	  COND_BLOCKED,
	  BARRIER_BLOCKED,
	  JOIN_BLOCKED,
	  TERMINATED
  };
	KInstIterator pc, prevPC;
	unsigned incomingBBIndex;
	unsigned threadId;
	Thread* parentThread;
	ThreadState threadState;
	StackType stack;
	std::vector<unsigned> vectorClock;
public:
	Thread(unsigned threadId, Thread* parentThread, KFunction* kf);
	Thread(Thread& anotherThread);
	virtual ~Thread();


	bool isRunnable() {
		return threadState == RUNNABLE;
	}

	bool isMutexBlocked() {
		return threadState == MUTEX_BLOCKED;
	}

	bool isCondBlocked() {
		return threadState == COND_BLOCKED;
	}

	bool isBarrierBlocked() {
		return threadState == BARRIER_BLOCKED;
	}

	bool isJoinBlocked() {
		return threadState == JOIN_BLOCKED;
	}

	bool isTerminated() {
		return threadState == TERMINATED;
	}

	bool isSchedulable() {
		return isRunnable() || isMutexBlocked();
	}
};

} /* namespace klee */

#endif /* LIB_CORE_THREAD_H_ */
