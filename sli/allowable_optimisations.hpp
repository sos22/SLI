#ifndef ALLOWABLE_OPTIMISATIONS_HPP__
#define ALLOWABLE_OPTIMISATIONS_HPP__

/* Flags:

   assumePrivateStack -- Assume that the stack is ``private'', in the
                         sense that no constant expressions can ever
                         alias with rsp.

   assumeExecutesAtomically -- Assume that the state machine executes
                               atomically.  This is useful for the
                               read-side machine, but not for the
                               write-side ones.

   ignoreSideEffects -- Effectively assume that the program terminates
  	                as soon as the machine completes, so that
  	                stores which aren't loaded by this machine are
  	                necessarily redundant.

   assumeNoInterferingStores -- Assume that there will be no stores
                                from other threads which interfere
                                with the machine we're currently
				examining.

   noExtend -- If true, assume that the machine will never be
               expanded.  This means that we can discard some
               assertions which would otherwise be quite useful.

   noSanityChecking -- Disable various extra assertions in the
                       optimiser.  These don't actually do anything in
                       NDEBUG builds, so this should normally be
                       turned on unless you're calling the optimiser
                       from a sanity check routine.

   preferCrash -- If true, we try to optimise to make the machine
                  crash when we have discretion (e.g. AssertFalse).
                  Otherwise, we try to make it survive.  You generally
                  want the former behaviour when you're deriving
                  validity predicates and the latter for crash
                  predicates.

   noLocalSurvival -- If true, convert any tests of entirely local
                      state which lead to survival into assertions.
                      i.e.  if you've got if (x) <survive>, and x
                      depends only on information which is entirely
                      local to this state, turn it into assert !x.
                      The idea is that, for most probe machines, we're
                      only really interested in the interactions with
                      remote machines, so if a test on local state
                      would mean that we skip the interesting bit we
                      should just require that the test fail.

   mustStoreBeforeCrash -- If true, the machine must issue a store
                           before it crashes.  If we encounter
			   a branch early in the machine, where it
			   definitely can't have issued a store, and
			   one of the targets of the branch is <crash>,
			   turn it into an assertion that we don't go
			   to <crash>.
		  
   Other fields:

   interestingStores -- Bit of a hack: sometimes, only some side
	                effects are interesting, so allow them to be
	                listed here.  If haveInterestingStoresSet is
	                false then we don't look at interestingStores
	                at all, and instead rely on ignoreSideEffects.

   nonLocalLoads -- If this is non-NULL then rather than using the
                    oracle to check whether loads might possibly
                    conflict with stuff outside of the current
                    machine, we just look in here.

   as -- if non-NULL, used to resolve BadPtr expressions with a
         constant address.

*/
class IRExprOptimisations : public Named {
	bool _assumePrivateStack;
	bool _noSanityChecking;

	IRExprOptimisations(bool __assumePrivateStack,
			    bool __noSanityChecking,
			    AddressSpace *__as)
		: _assumePrivateStack(__assumePrivateStack),
		  _noSanityChecking(__noSanityChecking),
		  _as(__as)
	{}
protected:
	IRExprOptimisations(double)
		: _assumePrivateStack(false),
		  _noSanityChecking(false),
		  _as(NULL)
	{}
	char *mkName() const {
		std::vector<const char *> fragments;
		if (_assumePrivateStack)
			fragments.push_back("assumePrivateStack");
		if (_noSanityChecking)
			fragments.push_back("noSanityChecking");
		if (_as)
			fragments.push_back("as");
		return flattenStringFragmentsMalloc(fragments, ", ",
						    "expropts(",
						    ")");
	}
public:
	/* If non-NULL, use this to resolve BadPtr expressions where
	   the address is a constant. */
	VexPtr<AddressSpace> _as;

	/* If @addr is definitely accessible, set *@res to true and
	   return true.  If it's definitely not accessible, set *@res
	   to false and return true.  If we can't be sure, return
	   false. */
	bool addressAccessible(unsigned long addr, bool *res) const {
		if (!_as)
			return false;
		*res = _as->isReadable(addr, 1);
		return true;
	}

	IRExprOptimisations setAddressSpace(AddressSpace *as) const
	{
		IRExprOptimisations res(*this);
		res._as = as;
		return res;
	}

	AddressSpace *getAddressSpace()
	{
		return _as;
	}

	bool noSanityChecking() const { return _noSanityChecking; }
	IRExprOptimisations enablenoSanityChecking() const { return IRExprOptimisations(_assumePrivateStack, true, _as); }
	bool assumePrivateStack() const { return _assumePrivateStack; }
	IRExprOptimisations enableassumePrivateStack() const { return IRExprOptimisations(true, _noSanityChecking, _as); }

	unsigned asUnsigned() const {
		unsigned x = 1; /* turning off all of the optional
				   optimisations doesn't turn off the
				   ones which are always available, so
				   have an implicit bit for them.
				   i.e. 0 means no optimisations at
				   all, and 1 means only the most
				   basic ones which are always
				   safe. */
		if (_assumePrivateStack)
			x |= 2;
#if 0
		/* _noSanityChecking doesn't really affect the final
		   result, so there's no point including it here. */
		if (_noSanityChecking)
			x |= 4;
#endif
		if (_as)
			x |= 8;
		return x;
	}

	bool parse(AddressSpace *addrSpace, const char *buf, const char **suffix) {
		if (!parseThisString("expropts(", buf, &buf))
			return false;
		_assumePrivateStack = false;
		_noSanityChecking = false;
		_as = NULL;
		clearName();
		if (parseThisString("assumePrivateStack", buf, &buf))
			_assumePrivateStack = true;
		parseThisString(", ", buf, &buf);
		if (parseThisString("noSanityChecking", buf, &buf))
			_noSanityChecking = true;
		parseThisString(", ", buf, &buf);
		if (parseThisString("as", buf, &buf))
			_as = addrSpace;
		if (!parseThisString(")", buf, suffix))
			return false;
		return true;
	}
};
class AllowableOptimisations : public IRExprOptimisations {
#define _optimisation_flags(f)						\
	f(assumeExecutesAtomically, bool)				\
	f(ignoreSideEffects, bool)					\
	f(assumeNoInterferingStores, bool)				\
	f(noExtend,bool)						\
	f(preferCrash,bool)						\
	f(noLocalSurvival,bool)						\
	f(mustStoreBeforeCrash,bool)
#define optimisation_flags(f)						\
	_optimisation_flags(f)						\
	f(interestingStores, const std::set<DynAnalysisRip> *)		\
	f(nonLocalLoads, std::set<DynAnalysisRip> *)

	/* The value of the argument doesn't matter, it's just there
	   so that we can select this constructor. */
	AllowableOptimisations(double)
		:
		IRExprOptimisations(1.0),
#define default_flag(name, type)		\
		_ ## name(false),
		_optimisation_flags(default_flag)
#undef default_flag
		_interestingStores(NULL),
		_nonLocalLoads(NULL)
	{}

#define mk_field(name, type) type _ ## name;
	optimisation_flags(mk_field)
#undef mk_field

	char *mkName() const {
		std::vector<const char *> fragments;
		fragments.push_back("opt{");
#define do_one_flag(name, ign)					\
		if ( _ ## name ) {				\
			if (fragments.size() != 1)		\
				fragments.push_back(", ");	\
			fragments.push_back( #name );		\
		}
		_optimisation_flags(do_one_flag);
#undef do_one_flag
		if (_interestingStores) {
			if (fragments.size() != 1)
				fragments.push_back(", ");
			fragments.push_back("interestingStores = {");
			for (auto it = _interestingStores->begin();
			     it != _interestingStores->end();
			     it++) {
				if (it != _interestingStores->begin())
					fragments.push_back(";");
				fragments.push_back(it->name());
			}
			fragments.push_back("}");
		}
		if (_nonLocalLoads) {
			if (fragments.size() != 1)
				fragments.push_back(", ");
			fragments.push_back("nonLocalLoads = {");
			for (auto it = _nonLocalLoads->begin();
			     it != _nonLocalLoads->end();
			     it++) {
				if (it != _nonLocalLoads->begin())
					fragments.push_back(";");
				fragments.push_back(it->name());
			}
			fragments.push_back("}");
		}
		if (fragments.size() != 1)
			fragments.push_back(", ");
		fragments.push_back(IRExprOptimisations::mkName());
		fragments.push_back("}");
		size_t sz = 1; /* nul terminator */
		for (auto it = fragments.begin(); it != fragments.end(); it++)
			sz += strlen(*it);
		char *res = (char *)malloc(sz);
		res[0] = 0;
		for (auto it = fragments.begin(); it != fragments.end(); it++)
			strcat(res, *it);
		free((void *)fragments[fragments.size() - 2]);
		return res;
	}
public:
	static AllowableOptimisations defaultOptimisations;

	AllowableOptimisations(
		const AllowableOptimisations *base,
		const IRExprOptimisations &ob)
		: IRExprOptimisations(ob),
#define mk_arg(name, type) _ ## name (base-> _ ## name),
		  _optimisation_flags(mk_arg)
#undef mk_arg
		  _interestingStores(base->_interestingStores),
		  _nonLocalLoads(base->_nonLocalLoads)
	{
	}

#define mk_set_value(name, type)				\
	AllowableOptimisations set ## name (type value) const	\
	{							\
		AllowableOptimisations res(*this);		\
		res._ ## name = value;				\
		return res;					\
	}
	optimisation_flags(mk_set_value);
#undef mk_set_value

#define mk_get_value(name, type)				\
	type name() const					\
	{							\
		return _ ## name ;				\
	}
	optimisation_flags(mk_get_value)
#undef mk_get_value
#define mk_set_flags(name, type)				\
	AllowableOptimisations enable ## name () const		\
	{							\
		return set ## name(true);			\
	}							\
	AllowableOptimisations disable ## name () const		\
	{							\
		return set ## name(false);			\
	}
	_optimisation_flags(mk_set_flags)
#undef mk_set_flags

	AllowableOptimisations setAddressSpace(AddressSpace *as) const
	{
		return AllowableOptimisations(this,
					      IRExprOptimisations::setAddressSpace(as));
	}
	AllowableOptimisations enableassumePrivateStack() const
	{
		return AllowableOptimisations(this,
					      IRExprOptimisations::enableassumePrivateStack());
	}

	bool ignoreStore(const VexRip &rip) const {
		if (_ignoreSideEffects)
			return true;
		if (_interestingStores &&
		    !_interestingStores->count(DynAnalysisRip(rip)))
			return true;
		return false;
	}

	bool parse(std::set<DynAnalysisRip> *is, std::set<DynAnalysisRip> *nll,
		   AddressSpace *as, const char *buf, const char **suffix)
	{
		if (!parseThisString("opt{", buf, &buf))
			return false;
#define clear_flg(name, ign) _ ## name = false;
		_optimisation_flags(clear_flg)
#undef clear_flg

		_interestingStores = NULL;
		_nonLocalLoads = NULL;
		is->clear();
		nll->clear();
		clearName();

#define parse_flag(name, ign)					\
		parseThisString(", ", buf, &buf);		\
		if (parseThisString( #name , buf, &buf))	\
			_ ## name = true;
		_optimisation_flags(parse_flag)
#undef parse_flag

		if (parseThisString("interestingStores = {", buf, &buf)) {
			while (!parseThisString("}", buf, &buf)) {
				parseThisString(";", buf, &buf);
				DynAnalysisRip dr;
				if (!parseDynAnalysisRip(&dr, buf, &buf))
					return false;
				is->insert(dr);
			}
			_interestingStores = is;
		}
		parseThisString(", ", buf, &buf);
		/* We used to have a bug which sometimes doubled up
		   this comma.  Rather than throw away all of the
		   results of those tests, just strip out an extra
		   comma here and ignore it. */
		parseThisString(", ", buf, &buf);
		if (parseThisString("nonLocalLoads = {", buf, &buf)) {
			while (!parseThisString("}", buf, &buf)) {
				parseThisString(";", buf, &buf);
				DynAnalysisRip dr;
				if (!parseDynAnalysisRip(&dr, buf, &buf))
					return false;
				nll->insert(dr);
			}
			_nonLocalLoads = nll;
		}
		parseThisString(", ", buf, &buf);
		if (!IRExprOptimisations::parse(as, buf, &buf))
			return false;
		if (!parseThisString("}", buf, suffix))
			return false;
		return true;
	}

#undef _optimisation_flags
#undef optimisation_flags

	static AllowableOptimisations fromFile(std::set<DynAnalysisRip> *is, std::set<DynAnalysisRip> *nll,
					       AddressSpace *as, const char *path);
};

#endif /* !ALLOWABLE_OPTIMISATIONS_HPP__ */
