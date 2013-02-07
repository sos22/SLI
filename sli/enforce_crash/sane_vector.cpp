#include "sli.h"
#include "enforce_crash.hpp"

template <typename t>
sane_vector<t>::sane_vector()
	: nr_elems(0),
	  nr_elems_allocated(0),
	  content(NULL)
{
}

template <typename t>
sane_vector<t>::sane_vector(const sane_vector &o)
	: nr_elems(o.nr_elems),
	  nr_elems_allocated(o.nr_elems_allocated)

{
	if (nr_elems_allocated == 0) {
		content = NULL;
	} else {
		content = malloc(sizeof(t) * nr_elems_allocated);
		for (unsigned i = 0; i < nr_elems; i++) {
			new (&(((t *)content)[i])) t( ((const t *)o.content)[i] );
		}
	}
}

template <typename t>
sane_vector<t>::sane_vector(sane_vector &&o)
	: nr_elems(o.nr_elems),
	  nr_elems_allocated(o.nr_elems_allocated),
	  content(o.content)
{
	o.nr_elems = 0;
	o.nr_elems_allocated = 0;
	o.content = NULL;
}

template <typename t>
sane_vector<t>::~sane_vector()
{
	for (unsigned i = 0; i < nr_elems; i++) {
		((t *)content)[i].~t();
	}
	free(content);
}

template <typename t> void
sane_vector<t>::operator =(const sane_vector &o)
{
	~sane_vector();
	new (this) sane_vector(o);
}
template <typename t> void
sane_vector<t>::operator =(const sane_vector &&o)
{
	~sane_vector();
	new (this) sane_vector(o);
}

template <typename t>
sane_vector<t>::iterator::iterator(sane_vector *_owner)
	: owner(_owner), idx(0)
{
}
template <typename t> const t &
sane_vector<t>::iterator::get() const
{
	assert(idx < owner->nr_elems);
	return ((const t *)owner->content)[idx];
}
template <typename t> void
sane_vector<t>::iterator::set(const t &what)
{
	assert(idx < owner->nr_elems);
	((const t *)owner->content)[idx] = what;
}
template <typename t> void
sane_vector<t>::iterator::erase()
{
	assert(idx < owner->nr_elems);
	t *content = (t *)owner->content;
	for (unsigned idx1 = idx; idx1 + 1 < owner->nr_elems; idx1++) {
		content[idx1].~t();
		new (&content[idx1]) t(content[idx1+1]);
	}
	owner->nr_elems--;
	content[owner->nr_elems].~t();
}
template <typename t> bool
sane_vector<t>::iterator::finished() const
{
	assert(idx <= owner->nr_elems);
	return idx == owner->nr_elems;
}
template <typename t> bool
sane_vector<t>::iterator::started() const
{
	return idx != 0;
}
template <typename t> void
sane_vector<t>::iterator::advance()
{
	idx++;
}
template <typename t> typename sane_vector<t>::iterator
sane_vector<t>::begin()
{
	return sane_vector<t>::iterator(this);
}

template <typename t>
sane_vector<t>::const_iterator::const_iterator(const sane_vector *_owner)
	: owner(_owner), idx(0)
{
}
template <typename t> const t &
sane_vector<t>::const_iterator::get() const
{
	assert(idx < owner->nr_elems);
	return ((const t *)owner->content)[idx];
}
template <typename t> bool
sane_vector<t>::const_iterator::finished() const
{
	return idx == owner->nr_elems;
}
template <typename t> bool
sane_vector<t>::const_iterator::started() const
{
	return idx != 0;
}
template <typename t> void
sane_vector<t>::const_iterator::advance()
{
	idx++;
}
template <typename t> typename sane_vector<t>::const_iterator
sane_vector<t>::begin() const
{
	return sane_vector<t>::const_iterator(this);
}

template <typename t> bool
sane_vector<t>::operator == (const sane_vector &o) const
{
	if (size() != o.size()) {
		return false;
	}
	auto it1 = begin();
	auto it2 = o.begin();
	while (1) {
		assert(it1.finished() == it2.finished());
		if (it1.finished()) {
			return true;
		}
		if (it1.get() != it2.get()) {
			return false;
		}
		it1.advance();
		it2.advance();
	}
}

template <typename t> void
sane_vector<t>::push_back(const t &o)
{
	if (nr_elems == nr_elems_allocated) {
		/* Try to keep nr_elems_allocated to be a little bit
		   less than a power of two, because that tends to
		   work well with most underlying allocators. */
		if (nr_elems_allocated == 0) {
			nr_elems_allocated = 6;
		} else {
			nr_elems_allocated = (nr_elems_allocated + 2) * 2 - 2;
		}
		/* Resize */
		t *newTs = (t *)malloc(nr_elems_allocated * sizeof(t));
		for (unsigned i = 0; i < nr_elems; i++) {
			new (&newTs[i]) t(((const t *)content)[i]);
			((t *)content)[i].~t();
		}
		free(content);
		content = newTs;
	}

	new ( &((t *)content)[nr_elems] ) t(o);
	nr_elems++;
}

template <typename t> size_t
sane_vector<t>::size() const
{
	return nr_elems;
}

template <typename t> void
sane_vector<t>::visit(HeapVisitor &hv) const
{
	for (unsigned i = 0; i < nr_elems; i++) {
		hv( ((t *)content)[i] );
	}
}

template sane_vector<const IRExpr *>::sane_vector();
template sane_vector<const IRExpr *>::sane_vector(sane_vector<const IRExpr *> const &);
template sane_vector<const IRExpr *>::~sane_vector();
template void sane_vector<const IRExpr *>::visit(HeapVisitor &) const;

template sane_vector<const IRExpr *>::iterator sane_vector<const IRExpr *>::begin();
template void sane_vector<const IRExpr *>::iterator::erase();
template const IRExpr *const &sane_vector<const IRExpr *>::iterator::get() const;
template bool sane_vector<const IRExpr *>::iterator::finished() const;
template bool sane_vector<const IRExpr *>::iterator::started() const;
template void sane_vector<const IRExpr *>::iterator::advance();

template sane_vector<const IRExpr *>::const_iterator sane_vector<const IRExpr *>::begin() const;
template const IRExpr *const &sane_vector<const IRExpr *>::const_iterator::get() const;
template bool sane_vector<const IRExpr *>::const_iterator::finished() const;
template void sane_vector<const IRExpr *>::const_iterator::advance();

template void sane_vector<const IRExpr *>::push_back(const IRExpr *const&);

template size_t sane_vector<const IRExpr *>::size() const;
template bool sane_vector<const IRExpr *>::operator ==(const sane_vector<const IRExpr *> &) const;
