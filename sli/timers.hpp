#ifndef TIMERS_HPP__
#define TIMERS_HPP__

#include <unistd.h>

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
public:
	void fired() {
		_exit(1);
	}
	void timeoutAfterSeconds(double seconds) {
		nextDue = now() + seconds;
		schedule();
	}
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
