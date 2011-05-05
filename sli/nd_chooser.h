#ifndef ND_CHOOSER_H__
#define ND_CHOOSER_H__

#include <vector>

#include <stdlib.h>

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
public:
	NdChooser() : stack(), current_stack_index(0), nr_branches(0) {}
	int nd_choice(int nr_options, bool *isNew = NULL);
	bool advance(void);
};

#endif /* !ND_CHOOSER_H__ */
