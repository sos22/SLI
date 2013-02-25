#if CONFIG_STACKED_CDF
#include <sys/fcntl.h>
#include <sys/time.h>
#include <errno.h>
#include <unistd.h>

#include "sli.h"

#include "stacked_cdf.hpp"

namespace stackedCdf {

/* Unconfuse emacs indent */
#if 0
}
#endif

struct node : public GarbageCollected<node, &ir_heap> {
	struct node *parent;
	struct node *headChild;
	struct node *nextSibling;
	stackedCdfBucket bucket;

	/* Only used for debugging */
	mutable bool reported;

	double time;

	void visit(HeapVisitor &hv) {
		hv(parent);
		hv(headChild);
		hv(nextSibling);
	}
	NAMED_CLASS
};

static VexPtr<node, &ir_heap> currentNode;
static struct : public GcCallback<&ir_heap> {
	struct node *content;
	void runGc(HeapVisitor &) {
		content = NULL;
	}
} nodeCache;

static const char *
name_event_tag(stackedCdfBucket t)
{
	switch (t) {
#define mk_case(name)				\
	case cdf_ ## name : return #name ;
		CdfKeys(mk_case)
#undef mk_case
	}
	abort();
}

static double
now()
{
	struct timeval n;
	gettimeofday(&n, NULL);
	return n.tv_sec + n.tv_usec * 1e-6;
}

static void
print_time_tree(const node *root, int depth, FILE *f)
{
	fprintf(f, "%*s%-30s%f\n", depth * 30, "", name_event_tag(root->bucket), root->time);
	for (auto child = root->headChild; child; child = child->nextSibling) {
		print_time_tree(child, depth + 1, f);
	}
}

static void
transfer_to_cache(const node *_root, bool allow_non_reported)
{
	node *root = const_cast<node *>(_root);
	assert(allow_non_reported || root->reported);
	root->nextSibling = nodeCache.content;
	node *cur;
	node *next;
	cur = root->headChild;
	while (cur) {
		next = cur->nextSibling;
		transfer_to_cache(cur, allow_non_reported);
		cur = next;
	}
	root->parent = (node *)0xbeef;
	root->headChild = (node *)0xd00d;
	root->bucket = (stackedCdfBucket)-1;
	root->time = -123456789e50;
}

/* Get the amount of time spent in one particular part of the space
 * for this tree.  Path should be terminated by cdf_root. */
static double
get_time_node(const node *root, ...)
{
	va_list args;
	va_start(args, root);
	while (1) {
		stackedCdfBucket desiredBucket = (stackedCdfBucket)va_arg(args, int);
		if (desiredBucket == cdf_root) {
			va_end(args);
			root->reported = true;
			return root->time;
		}
		const node *i;
		for (i = root->headChild;
		     i && i->bucket != desiredBucket;
		     i = i->nextSibling) {
			/**/
		}
		if (!i) {
			/* No samples for this path -> it took time
			   zero. */
			va_end(args);
			return 0;
		}
		root = i;
	}
}

static double
sum_time_nodes(const node *root, const std::set<unsigned> &offsets,
	       const std::vector<stackedCdfBucket> &path)
{
	double acc = 0;
	std::set<unsigned> newOffsets;
	for (auto it = offsets.begin(); it != offsets.end(); it++) {
		assert(*it < path.size());
		if (root->bucket == path[*it]) {
			if (*it == path.size() - 1) {
				root->reported = true;
				acc += root->time;
			} else {
				newOffsets.insert(*it + 1);
			}
		}
	}
	newOffsets.insert(0);
	for (auto it = root->headChild; it; it = it->nextSibling) {
		acc += sum_time_nodes(it, newOffsets, path);
	}
	return acc;
}

/* Like get_time_node(), but don't require the path to start at the
   root.  When multiple nodes in the tree match the path this sums
   them all up. */
static double
sum_time_nodes(const node *root, ...)
{
	std::vector<stackedCdfBucket> path;

	va_list args;
	va_start(args, root);
	while (1) {
		stackedCdfBucket b = (stackedCdfBucket)va_arg(args, int);
		if (b == cdf_root) {
			break;
		}
		path.push_back(b);
	}
	va_end(args);

	return sum_time_nodes(root, std::set<unsigned>(), path);
}

void
stacked_cdf_start(stackedCdfBucket bucket)
{
	if (currentNode) {
		node *child;
		for (child = currentNode->headChild;
		     child && child->bucket != bucket;
		     child = child->nextSibling)
			;
		if (child) {
			currentNode = child;
			child->time -= now();
			return;
		}
	}

	auto n = nodeCache.content;
	if (n) {
		nodeCache.content = nodeCache.content->nextSibling;
	} else {
		n = new node();
	}
	n->parent = currentNode;
	n->headChild = NULL;
	n->nextSibling = currentNode ? currentNode->headChild : NULL;
	n->bucket = bucket;
	n->time = -now();
	n->reported = false;
	if (currentNode) {
		currentNode->headChild = n;
	}
	currentNode = n;
}

void
stacked_cdf_stop(stackedCdfBucket bucket)
{
	assert(currentNode);
	assert(currentNode->bucket == bucket);
	currentNode->time += now();
	currentNode = currentNode->parent;
}

void
start()
{
	assert(currentNode == NULL);
	stacked_cdf_start(cdf_root);
	assert(currentNode != NULL);
}

void
stop(bool timed_out)
{
	if (timed_out) {
		transfer_to_cache(currentNode, true);
		currentNode = NULL;
		return;
	}
	static int cntr;

	node *root = currentNode;
	assert(root != NULL);
	assert(root->bucket == cdf_root);
	stacked_cdf_stop(cdf_root);
	assert(currentNode == NULL);

	int fd;
	while (1) {
		char *path = my_asprintf("stacked_cdfs/%d.sample", cntr);
		fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0666);
		if (fd < 0 && errno != EEXIST) {
			err(1, "opening %s", path);
		}
		free(path);
		if (fd >= 0) {
			break;
		}
		cntr++;
	}
	FILE *f = fdopen(fd, "w");

	/* Can't use get_time_node for root. */
	root->reported = true;
	fprintf(f, "Total time: %f\n", root->time);

	fprintf(f, "Building probe machine: %f\n",
	       get_time_node(root, cdf_BuildProbeMachine, cdf_root) +
	       get_time_node(root, cdf_ProbeResimplify, cdf_root));
	fprintf(f, "Deriving R atomic: %f\n", get_time_node(root, cdf_DeriveRAtomic, cdf_root));
	fprintf(f, "Building store machine: %f\n",
	       get_time_node(root, cdf_FindConflictingStores, cdf_root) +
	       get_time_node(root, cdf_BuildStoreCFGs, cdf_root) +
	       get_time_node(root, cdf_CompileStoreMachine, cdf_root) +
	       get_time_node(root, cdf_StoreInitialSimplify, cdf_root) +
	       get_time_node(root, cdf_StoreSecondSimplify, cdf_root));
	fprintf(f, "Deriving W atomic: %f\n", get_time_node(root, cdf_BuildWAtomic, cdf_root));
	fprintf(f, "Deriving crash constraint: %f\n", get_time_node(root, cdf_CrashConstraint, cdf_root));

	fprintf(f, "Probe:CFGs: %f\n", get_time_node(root, cdf_BuildProbeMachine, cdf_GetProbeCFGs, cdf_root));
	fprintf(f, "Probe:Compile: %f\n", get_time_node(root, cdf_BuildProbeMachine, cdf_CompileProbeMachine, cdf_root));
	fprintf(f, "Probe:SSA: %f\n", get_time_node(root, cdf_BuildProbeMachine, cdf_ProbeConvertSSA, cdf_root));
	fprintf(f, "Probe:Simplify: %f\n",
	       get_time_node(root, cdf_BuildProbeMachine, cdf_ProbeInitialSimplify, cdf_root) +
	       get_time_node(root, cdf_BuildProbeMachine, cdf_ProbeSecondSimplify, cdf_root) +
	       get_time_node(root, cdf_ProbeResimplify, cdf_root));

	fprintf(f, "Store:FindStores: %f\n", get_time_node(root, cdf_FindConflictingStores, cdf_root));
	fprintf(f, "Store:CFGs: %f\n", get_time_node(root, cdf_BuildStoreCFGs, cdf_root));
	fprintf(f, "Store:Compile: %f\n", get_time_node(root, cdf_CompileStoreMachine, cdf_root));
	fprintf(f, "Store:SSA: %f\n", get_time_node(root, cdf_StoreConvertToSSA, cdf_root));
	fprintf(f, "Store:Simplify: %f\n",
	       get_time_node(root, cdf_StoreInitialSimplify, cdf_root) +
	       get_time_node(root, cdf_StoreSecondSimplify, cdf_root));

	fprintf(f, "RAtomic:Build: 0\n");
	fprintf(f, "RAtomic:Simplify: %f\n", get_time_node(root, cdf_DeriveRAtomic, cdf_DeriveRAtomicResimplify, cdf_root));
	fprintf(f, "RAtomic:SymbExecute: %f\n", get_time_node(root, cdf_DeriveRAtomic, cdf_DeriveRAtomicSymbolicExecute, cdf_root));

	fprintf(f, "WAtomic:Build: %f\n", get_time_node(root, cdf_BuildWAtomic, cdf_BuildWAtomicMachine, cdf_root));
	fprintf(f, "WAtomic:Simplify: %f\n", get_time_node(root, cdf_BuildWAtomic, cdf_BuildWAtomicResimplify, cdf_root));
	fprintf(f, "WAtomic:SymbExecute: %f\n", get_time_node(root, cdf_BuildWAtomic, cdf_BuildWAtomicSymbolicExecute, cdf_root));

	fprintf(f, "CC:Build: %f\n", get_time_node(root, cdf_CrashConstraint, cdf_CrashConstraintBuildCross, cdf_root));
	fprintf(f, "CC:Simplify: %f\n", get_time_node(root, cdf_CrashConstraint, cdf_CrashConstraintResimplify, cdf_root));
	fprintf(f, "CC:SymbExecute: %f\n", get_time_node(root, cdf_CrashConstraint, cdf_CrashConstraintSymbolicExecute, cdf_root));

	fprintf(f, "Simplify:Total: %f\n", sum_time_nodes(root, cdf_Optimise, cdf_root));
	fprintf(f, "Simplify:Phi: %f\n", sum_time_nodes(root, cdf_Optimise, cdf_PhiElimination, cdf_root));
	fprintf(f, "Simplify:Load: %f\n", sum_time_nodes(root, cdf_Optimise, cdf_LoadElimination, cdf_root));
	fprintf(f, "Simplify:CDG: %f\n", sum_time_nodes(root, cdf_Optimise, cdf_BuildCDG, cdf_root));
	fprintf(f, "Simplify:Avail: %f\n", sum_time_nodes(root, cdf_Optimise, cdf_AvailExpression, cdf_root));
	fprintf(f, "Simplify:DeadCode: %f\n", sum_time_nodes(root, cdf_Optimise, cdf_Deadcode, cdf_root));
	fprintf(f, "Simplify:Peephole: %f\n", sum_time_nodes(root, cdf_Optimise, cdf_LocalOptimise, cdf_root));

	fprintf(f, "BDD: %f\n", sum_time_nodes(root, cdf_BDD, cdf_root));

	fclose(f);

	transfer_to_cache(root, false);
}

};

#endif
