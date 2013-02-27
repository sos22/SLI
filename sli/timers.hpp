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

extern volatile bool _timed_out;
class TimeoutTimer : public Timer {
public:
	void fired() {
		_timed_out = true;
	}
	void timeoutAfterSeconds(double seconds) {
		nextDue = now() + seconds;
		schedule();
	}
};

#endif /* !TIMERS_HPP__ */
