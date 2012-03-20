#ifndef TIMERS_HPP__
#define TIMERS_HPP__

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

#endif /* !TIMERS_HPP__ */
