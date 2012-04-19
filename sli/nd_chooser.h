#ifndef ND_CHOOSER_H__
#define ND_CHOOSER_H__

#define ND_CHOOSER_STATS 0

#include <vector>
#include <stdlib.h>

#if ND_CHOOSER_STATS
#include <sys/time.h>
#endif

#include "profile.hpp"

class NdChooser {
	struct choicepoint {
		int current_value;
		int nr_options;
		choicepoint(int n)
			: current_value(0), nr_options(n)
		{}
		choicepoint() { abort(); }
	};

	std::vector<struct choicepoint> stack;
	unsigned current_stack_index;
	unsigned nr_branches;

#if ND_CHOOSER_STATS
	/* Stats for current stack */
	double cur_stack_start;
	double cur_stack_cont_recovery_end;

	/* Stats for execution as a whole */
	double exec_tot_recovery;
	double exec_tot_forward_progress;
	int nr_stacks;
	int nr_choice_points;

	static double now() {
		struct timeval tv;
		gettimeofday(&tv, NULL);
		return tv.tv_sec + tv.tv_usec * 1e-6;
	}
	void finish_stack() {
		double n = now();
		if (cur_stack_cont_recovery_end == 0)
			abort();
		exec_tot_forward_progress += n - cur_stack_cont_recovery_end;
		exec_tot_recovery += cur_stack_cont_recovery_end - cur_stack_start;
		nr_stacks++;
		if (stack.size() == 0)
			cur_stack_cont_recovery_end = n;
		else
			cur_stack_cont_recovery_end = 0;
		cur_stack_start = n;
	}

	/* Stats for program as a whole */
	static int nr_choosers;
	static int tot_nr_stacks;
	static int tot_nr_choice_points;
	static double tot_recovery;
	static double tot_forward_progress;
	static double start_of_day;
#else
	void finish_stack() {}
#endif

public:
	NdChooser()
		: stack(), current_stack_index(0), nr_branches(0)
#if ND_CHOOSER_STATS
		  , cur_stack_start(now()),
		  cur_stack_cont_recovery_end(cur_stack_start),
		  exec_tot_recovery(0), exec_tot_forward_progress(0),
		  nr_stacks(0), nr_choice_points(0)
#endif
	{
		start_profiling();
	}
	~NdChooser();

	int nd_choice(int nr_options, bool *isNew = NULL);
	bool advance(void);
};

#endif /* !ND_CHOOSER_H__ */
