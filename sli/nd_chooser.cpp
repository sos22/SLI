/* Simple thing for emulating a non-deterministic computation.  The
   idea is that you have some program which occasionally calls
   nd_choice(N) to non-deterministically choose one of N options, and
   you want to turn that into a deterministic program which
   systematically explores every possible sequence of
   non-deterministic choices.  We assume that the sequence is finite.

   The client is expected to provide a driver which looks like this:

   NdChoice nd;
   do {
        nondeterministic_computation(nd);
   } while (nd.advance());

   which will enumerate every possible sequence of options.

   This can be thought of as a kind of graph exploration problem, with
   nodes representing the non-deterministic choices and edges
   representing the deterministic part of the computation.  We would
   like to explore this graph depth-first, but we can't really reify
   the nodes (as that would amount to capturing the current
   continuation, which is difficult in C++).  Instead, we use an
   almost iterative-deepening-like approach which involves rebuilding
   the intermediate states every time we need to change something.

   The key data structure is a stack of choice points, representing
   the path to the node which we're currently exploring, and an index
   representing how far through said path we've currently managed to
   get.  When someone calls nd_choice and the index is within the
   path, we just return the choice suggested by the relevant stack
   slot.  If you're outside the path, you push a new entry on the
   stack representing the current choice and then return zero.

   advance() is then quite simple: take the last entry on the stack
   and advance it so that next time around you take the next possible
   choice.  If that causes you to go past the end of the allowable
   choices at that point, pop it off the stack and move on.  If the
   stack underflows then the computation is complete. */
#include "nd_chooser.h"
#include <vector>
#include <stdlib.h>
#include <assert.h>

#include <stdio.h>

int
NdChooser::nd_choice(int nr_options, bool *isNew)
{
	int r;
	if (isNew)
		*isNew = false;
	if (current_stack_index == stack.size()) {
		stack.push_back(choicepoint(nr_options));
		r = 0;
		if (isNew)
			*isNew = true;
	} else {
		assert(current_stack_index < stack.size());
		assert(stack[current_stack_index].nr_options == nr_options);
		assert(stack[current_stack_index].current_value < nr_options);
		r = stack[current_stack_index].current_value;
	}
	current_stack_index++;
	return r;
}

bool
NdChooser::advance(void)
{
	assert(current_stack_index == stack.size());
	current_stack_index = 0;
	while (!stack.empty()) {
		choicepoint &cp(stack.back());
		/* Advance the last choice */
		cp.current_value++;
		if (cp.current_value < cp.nr_options) {
			nr_branches++;
			return true;
		}
		/* This choicepoint is exhausted, try another one. */
		stack.pop_back();
	}
	/* Ran out of nondeterminism. */
	return false;
}
