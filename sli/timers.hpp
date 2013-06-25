#ifndef TIMERS_HPP__
#define TIMERS_HPP__

#include <unistd.h>
#include <stdlib.h>

class TimerSet;

double now();

class Timer {
public:
	Timer();
	~Timer();
	void schedule();
	void cancel();

	virtual void fired() = 0;

	/* XXX this should really be private */
	bool inserted;

	double interval;
	double nextDue;
};

void initialise_timers();

class TimeoutTimer : public Timer {
	void fired() {
		if (reallyOff) {
			abort();
		}
		_exit(73);
	}
public:
	bool reallyOff;
	void timeoutAfterSeconds(double seconds) {
		if (reallyOff) {
			abort();
		}
		nextDue = now() + seconds;
		schedule();
	}
	TimeoutTimer()
		: Timer(), reallyOff(false)
	{}
};

class Stopwatch {
	double started;
public:
	Stopwatch()
		: started(now())
	{}
	double sample() {
		return now() - started;
	}
};

#endif /* !TIMERS_HPP__ */
