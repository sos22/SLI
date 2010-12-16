/* Implementation of RawRangeTree and RangeSet.  RangeTree<> is in the
   header file, because it's a template. */
#include "libvex_alloc.h"
#include "range_tree.h"

void *const
RangeSet::presentEntry = (void *)1;

RawRangeTree::RawRangeTree()
{
}

bool
RawRangeTree::performSearch(unsigned long v, int &low, int &high)
{
	low = 0;
	high = content.size() - 1;
	if (content.size() == 0 ||
	    v < content[low].start ||
	    v >= content[high].end1)
		return false;
	/* We now maintain the invariant that v >= content[low].start
	   and v < content[high].end1. */
	while (high > low + 1) {
		int probe = (high + low) / 2;
		if (v >= content[probe].start)
			low = probe;
		if (v < content[probe].end1)
			high = probe;
		assert(v >= content[low].start && v < content[high].end1);
	}
	assert(v >= content[low].start && v < content[high].end1);
	return true;
}

void *
RawRangeTree::get(unsigned long v)
{
	int low;
	int high;
	if (!performSearch(v, low, high))
		return NULL;
	assert(low == high || low + 1 == high);
	assert(v >= content[low].start && v < content[high].end1);
	if (low == high) {
		return content[low].value;
	} else {
		assert(high == low + 1);
		if (v < content[low].end1)
			return content[low].value;
		if (v >= content[high].start)
			return content[high].value;
		return NULL;
	}
}

void
RawRangeTree::set(unsigned long start, unsigned long end1, void *value)
{
	int low, high;
	assert(end1 >= start);
	if (end1 == start)
		return;
	if (content.size() == 0) {
		content.push_back(entry(start, end1, value));
		return;
	}
	if (end1 < content[0].start ||
	    (end1 == content[0].start &&
	     value != content[0].value)) {
		content.insert(content.begin(),
			       entry(start, end1, value));
		return;
	}

	if (end1 == content[0].start) {
		assert(value == content[0].value);
		content[0].start = start;
		return;
	}

	if (start >= content[content.size()-1].end1) {
		if (start == content[content.size()-1].end1 &&
		    value == content[content.size()-1].value) {
			content[content.size()-1].end1 = end1;
		} else {
			content.push_back(entry(start, end1, value));
		}
		return;
	}

	/* Find the starting point of the new range in the current
	 * list. */
	bool t = performSearch(start, low, high);
	assert(t);
	if (high == low + 1) {
		if (start < content[low].end1)
			high = low;
		if (start >= content[high].start)
			low = high;
	}
	if (high == low) {
		/* Start is in the middle of this range.  Check for
		   compatibility with this range and then considering
		   splitting. */
		assert(value == content[low].value);
		if (end1 > content[low].end1)
			set(content[low].end1, end1, value);
		return;
	}
	assert(high == low + 1);

	/* The start of this range is in the gap between two other
	   ranges. */
	if (end1 > content[high].start) {
		/* But the end isn't, so split the range and try
		 * again. */
		set(start, content[high].start, value);
		set(content[high].start, end1, value);
		return;
	}

	/* Do we want to merge with an existing range? */
	bool mergeDown =
		value == content[low].value &&
		start == content[low].end1;
	bool mergeUp =
		value == content[high].value &&
		end1  == content[high].start;
	if (mergeDown && mergeUp) {
		/* Merge with both.  Extend low to subsume high, and
		   then nuke high. */
		content[low].end1 = content[high].end1;
		content.erase(content.begin() + high);
	} else if (mergeDown) {
		content[low].end1 = end1;
	} else if (mergeUp) {
		content[high].start = start;
	} else {
		/* No merge possible -> insert a completely new
		 * range. */
		content.insert(content.begin() + high,
			       entry(start, end1, value));
	}
}

void
RawRangeTree::purgeByValue(void *v)
{
	for (std::vector<entry>::iterator it = content.begin();
	     it != content.end();
		) {
		if (it->value == v)
			it = content.erase(it);
		else
			it++;
	}
}

void
RawRangeTree::iterator::updateInner()
{
	if (idx >= (int)t->content.size())
		return;
	else
		inner = t->content[idx];
}

void
RawRangeTree::visit(HeapVisitor &hv)
{
	for (std::vector<entry>::iterator it = content.begin();
	     it != content.end();
	     it++)
		hv(it->value);
}
