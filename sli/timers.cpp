/* Very simple timer infrastructure, so that we can use SIGPROF for
   both profiling and timeouts. */
#include <sys/time.h>
#include <signal.h>

#include "timers.hpp"
#include "sli.h"

#define MAX_TIMERS 16
static Timer *pendingTimers[MAX_TIMERS];
static int nr_timers_pending;
static bool timers_suspended;
static bool lost_timer_event;

double
now()
{
	struct timeval tv;
	gettimeofday(&tv, NULL);
	return tv.tv_sec + tv.tv_usec * 1e-6;
}

static void
kill_timer(Timer *t)
{
	assert(timers_suspended);
	if (!t->inserted)
		return;

	int idx;
	for (idx = 0; idx < nr_timers_pending; idx++) {
		if (pendingTimers[idx] == t)
			break;
	}
	assert(idx != nr_timers_pending);
	memmove(pendingTimers + idx, pendingTimers + idx + 1,
		sizeof(pendingTimers[0]) * (nr_timers_pending - idx - 1));
	nr_timers_pending--;
	t->inserted = false;

	for (idx = 0; idx < nr_timers_pending; idx++) {
		if (pendingTimers[idx] == t) {
			abort();
		}
	}
}

static void
insert_timer(Timer *t)
{
	assert(timers_suspended);
	assert(!t->inserted);

	assert(nr_timers_pending < MAX_TIMERS);
	pendingTimers[nr_timers_pending] = t;
	nr_timers_pending++;
	t->inserted = true;
}

/* A memory barrier which is strong enough for synchronisation with
   signals.  i.e. prevent compiler reorderings, but not processor
   ones. */
static void
signal_memory_barrier()
{
	asm volatile ("":::"memory");
}

static void
run_timer_event(void)
{
	assert(timers_suspended);

	double n = now();
retry:
	if (nr_timers_pending == 0)
		return;
	double nextFire = pendingTimers[0]->nextDue;
	for (int idx = 0; idx < nr_timers_pending; idx++) {
		Timer *pt = pendingTimers[idx];
		if (!pt->inserted) {
			abort();
		}
		if (pt->nextDue <= n) {
			kill_timer(pt);
			if (pt->interval > 0) {
				pt->nextDue = n + pt->interval;
				insert_timer(pt);
			}

			pt->fired();
			goto retry;
		}
		if (pt->nextDue < nextFire)
			nextFire = pt->nextDue;
	}

	n = now();
	if (n >= nextFire)
		goto retry;
	struct itimerval itv;
	memset(&itv, 0, sizeof(itv));
	itv.it_value.tv_sec = nextFire - n;
	itv.it_value.tv_usec = (nextFire - n - itv.it_value.tv_sec) * 1e6;
	while (itv.it_value.tv_usec >= 1000000) {
		/* Shouldn't really happen, but might conceivably if
		   we're in a funny rounding mode.  Fix it up. */
		itv.it_value.tv_sec++;
		itv.it_value.tv_usec -= 1000000;
	}
	while (itv.it_value.tv_usec < 0) {
		/* Likewise. */
		itv.it_value.tv_sec--;
		itv.it_value.tv_usec += 1000000;
	}

	/* If the timer looks bad, just spin. */
	if (itv.it_value.tv_sec < 0 || /* Another sanity check on FP behaviour */
	    (itv.it_value.tv_sec == 0 && itv.it_value.tv_usec < 100)) { /* Avoid stupidly short timers */
		n = now();
		goto retry;
	}

	setitimer(ITIMER_PROF, &itv, NULL);
}

static void
signal_handler(int )
{
	if (timers_suspended) {
		lost_timer_event = true;
		return;
	}
	timers_suspended = true;
	run_timer_event();
	timers_suspended = false;
}

static void
suspend_timers(void)
{
	assert(!timers_suspended);
	timers_suspended = true;
	signal_memory_barrier();
}

static void
resume_timers(void)
{
	while (1) {
		signal_memory_barrier();
		assert(timers_suspended);
		timers_suspended = false;
		signal_memory_barrier();
		if (!lost_timer_event)
			return;

		/* If we got here then we dropped a timer signal
		 * because of the suspension.  Block timers and
		 * emulate signal delivery. */
		suspend_timers();
		lost_timer_event = false;
		run_timer_event();
	}
}

void
initialise_timers()
{
	signal(SIGPROF, signal_handler);
}

Timer::Timer()
	: inserted(false), interval(0), nextDue(0)
{}

Timer::~Timer()
{
	if (inserted)
		cancel();
}

void
Timer::schedule(void)
{
	assert(!inserted);
	assert(nextDue != 0);

	suspend_timers();
	insert_timer(this);
	run_timer_event();
	resume_timers();
}

void
Timer::cancel(void)
{
	suspend_timers();
	kill_timer(this);
	resume_timers();
}
