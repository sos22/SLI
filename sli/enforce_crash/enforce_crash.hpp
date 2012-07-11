#ifndef enforceCrash_hpp__
#define enforceCrash_hpp__

#include <set>
#include <map>
#include "libvex_ir.h"
#include "libvex_parse.h"
#include "genfix.hpp"
#include "dnf.hpp"
#include "offline_analysis.hpp"

void enumerateNeededExpressions(IRExpr *e, std::set<IRExpr *> &out);

struct exprEvalPoint;
class happensBeforeEdge;

class internmentState {
public:
	std::set<happensBeforeEdge *> hbes;
	internIRExprTable exprs;
	IRExpr *intern(IRExpr *e) { return internIRExpr(e, exprs); }
	unsigned intern(unsigned x) { return x; }
	exprEvalPoint intern(const exprEvalPoint &);
	template <typename a, typename b> std::pair<a, b> intern(const std::pair<a, b> &x) {
		return std::pair<a, b>(intern(x.first), intern(x.second));
	}
	template <typename a> std::set<a> intern(const std::set<a> &x) {
		std::set<a> out;
		for (auto it = x.begin(); it != x.end(); it++)
			out.insert(intern(*it));
		return out;
	}
	template <typename a> std::vector<a> intern(const std::vector<a> &in) {
		std::vector<a> out;
		out.reserve(in.size());
		for (auto it = in.begin(); it != in.end(); it++)
			out.push_back(intern(*it));
		return out;
	}
};

class instrToInstrSetMap : public std::map<Instruction<ThreadRip> *, std::set<Instruction<ThreadRip> *> > {
public:
	void print(FILE *f);
};

/* Map from instructions to instructions which happen immediately
   before them, including those ordered by happens-before
   relationships. */
class predecessorMapT : public instrToInstrSetMap {
public:
	predecessorMapT(CFG<ThreadRip> *cfg) {
		for (CFG<ThreadRip>::ripToInstrT::iterator it = cfg->ripToInstr->begin();
		     it != cfg->ripToInstr->end();
		     it++) {
			Instruction<ThreadRip> *v = it.value();
			if (!count(v))
				(*this)[v];
			for (auto it2 = v->successors.begin(); it2 != v->successors.end(); it2++)
				if (it2->instr)
					(*this)[it2->instr].insert(v);
		}
	}
};

/* An encoding of the happens-before edges in a DNF clause into a map
   over Instructions. */
class happensAfterMapT {
public:
	/* happensBefore[i] -> the set of all instructions ordered before i */
	instrToInstrSetMap happensBefore;
	/* happensBefore[i] -> the set of all instructions ordered after i */
	instrToInstrSetMap happensAfter;
	bool init(DNF_Conjunction &c, CFG<ThreadRip> *cfg) __attribute__((warn_unused_result));
	void print(FILE *f) {
		fprintf(f, "before:\n");
		happensBefore.print(f);
		fprintf(f, "after:\n");
		happensAfter.print(f);
	}
};

/* A map from Instruction * to the set of instructions which must
 * complete before that instruction, based purely on the control flow
 * graph. */
class instructionDominatorMapT : public instrToInstrSetMap {
	friend class expressionDominatorMapT;
	instructionDominatorMapT() {}
	instructionDominatorMapT(CFG<ThreadRip> *cfg,
				 predecessorMapT &predecessors,
				 happensAfterMapT &happensAfter,
				 const std::set<ThreadRip> &neededInstructions);
};

class expressionDominatorMapT : public std::map<Instruction<ThreadRip> *, std::set<std::pair<bool, IRExpr *> > > {
	class trans1 : public IRExprTransformer {
		std::set<Instruction<ThreadRip> *> &avail;
		std::set<unsigned> &availThreads;
		CFG<ThreadRip> *cfg;
		bool isAvail(ThreadRip rip) {
			Instruction<ThreadRip> *i = cfg->ripToInstr->get(rip);
			assert(i);
			return avail.count(i) != 0;
		}
		IRExpr *transformIex(IRExprGet *e) {
			if (!availThreads.count(e->reg.tid()))
				isGood = false;
			return NULL;
		}
		IRExpr *transformIex(IRExprHappensBefore *) {
			isGood = false;
			return NULL;
		}
	public:
		bool isGood;
		trans1(std::set<Instruction<ThreadRip> *> &_avail, std::set<unsigned> &_availThreads, CFG<ThreadRip> *_cfg)
			: avail(_avail), availThreads(_availThreads), cfg(_cfg), isGood(true) 
		{}
	};
	static bool evaluatable(IRExpr *e, std::set<Instruction<ThreadRip> *> &avail, std::set<unsigned> &availThreads, CFG<ThreadRip> *cfg) {
		trans1 t(avail, availThreads, cfg);
		t.doit(e);
		return t.isGood;
	}
public:
	instructionDominatorMapT idom;
	bool init(DNF_Conjunction &, CFG<ThreadRip> *, const std::set<ThreadRip> &neededRips) __attribute__((warn_unused_result));
};

class simulationSlotT {
public:
	int idx;
	simulationSlotT(int _idx) : idx(_idx) {}
	simulationSlotT() : idx(-10000) {}
};

template <typename src, typename dest> void
setToVector(const std::set<src> &in, std::vector<dest> &out)
{
	out.reserve(in.size());
	for (typename std::set<src>::iterator it = in.begin();
	     it != in.end();
	     it++)
		out.push_back(*it);
}

template <typename t> void
visit_set(std::set<t> &s, HeapVisitor &hv)
{
	/* Ugg, can't just visit a set of GC'd
	   pointers because it rearranges them, so
	   have to do it via a vector. */
	std::vector<t> n;
	setToVector(s, n);
	visit_container(n, hv);
	s.clear();
	for (auto it2 = n.begin(); it2 != n.end(); it2++)
		s.insert(*it2);
}

class expressionStashMapT : public std::map<unsigned long, std::set<std::pair<unsigned, IRExpr *> > >,
			    private GcCallback<&ir_heap> {
	void runGc(HeapVisitor &hv) {
		for (auto it = begin(); it != end(); it++) {
			std::vector<std::pair<unsigned, IRExpr *> > n;
			setToVector(it->second, n);
			it->second.clear();
			for (auto it2 = n.begin(); it2 != n.end(); it2++) {
				hv(it2->second);
				it->second.insert(*it2);
			}
		}
	}
public:
	expressionStashMapT() {}
	expressionStashMapT(std::set<IRExpr *> &neededExpressions,
			    StateMachine *probeMachine,
			    StateMachine *storeMachine,
			    std::map<unsigned, ThreadRip> &roots)
	{
		std::set<IRExprGet *> neededTemporaries;
		for (auto it = neededExpressions.begin();
		     it != neededExpressions.end();
		     it++) {
			IRExpr *e = *it;
			ThreadRip rip;
			if (e->tag == Iex_Get) {
				IRExprGet *ieg = (IRExprGet *)e;
				if (ieg->reg.isReg()) {
					rip = roots[ieg->reg.tid()];
					(*this)[rip.rip.unwrap_vexrip()].insert(std::pair<unsigned, IRExpr *>(rip.thread, e));
				} else {
					neededTemporaries.insert(ieg);
				}
			} else if (e->tag == Iex_HappensBefore) {
				/* These don't really get stashed in any useful sense */
			} else {
				abort();
			}
		}
		if (!neededTemporaries.empty()) {
			std::set<StateMachineSideEffectLoad *> loads;
			enumSideEffects(probeMachine, loads);
			enumSideEffects(storeMachine, loads);
			for (auto it = neededTemporaries.begin();
			     it != neededTemporaries.end();
			     it++) {
				StateMachineSideEffectLoad *l = NULL;
				for (auto it2 = loads.begin(); it2 != loads.end(); it2++) {
					if ( threadAndRegister::fullEq((*it2)->target, (*it)->reg) ) {
						assert(!l);
						l = *it2;
					}
				}
				assert(l);
				(*this)[l->rip.rip.rip.unwrap_vexrip()].insert(
					std::pair<unsigned, IRExpr *>(
						l->rip.rip.thread,
						*it));
			}
		}
	}
	void operator|=(const expressionStashMapT &esm) {
		for (auto it = esm.begin(); it != esm.end(); it++) {
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				(*this)[it->first].insert(*it2);
		}
	}
	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Stash map:\n", str, &str))
			return false;
		clear();
		while (1) {
			unsigned long a;
			if (!parseHexUlong(&a, str, &str) ||
			    !parseThisString(" -> {", str, &str))
				break;
			std::set<std::pair<unsigned, IRExpr *> > b;
			while (1) {
				std::pair<unsigned, IRExpr *> s;
				if (!parseDecimalUInt(&s.first, str, &str) ||
				    !parseThisChar(':', str, &str) ||
				    !parseIRExpr(&s.second, str, &str) ||
				    !parseThisString(", ", str, &str))
					break;
				b.insert(s);
			}
			if (!parseThisString("}\n", str, &str))
				return false;
			assert(b.size() > 0);
			(*this)[a] = b;
		}
		*suffix = str;
		return true;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "\tStash map:\n");
		for (auto it = begin(); it != end(); it++) {
			fprintf(f, "\t\t%lx -> {", it->first);
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				fprintf(f, "%d:", it2->first);
				it2->second->prettyPrint(f);
				fprintf(f, ", ");
			}
			fprintf(f, "}\n");
		}
	}
	void internSelf(internmentState &state) {
		for (auto it = begin(); it != end(); it++) {
			std::set<std::pair<unsigned, IRExpr *> > out;
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				std::pair<unsigned, IRExpr *> a;
				a.first = it2->first;
				a.second = state.intern(it2->second);
				out.insert(a);
			}
			it->second = out;
		}
	}
};

class happensBeforeEdge : public GarbageCollected<happensBeforeEdge, &ir_heap>,
			  public Named {
	happensBeforeEdge() {}
	happensBeforeEdge(const ThreadRip &_before,
			  const ThreadRip &_after,
			  const std::vector<IRExpr *> &_content,
			  unsigned _msg_id)
		: before(_before), after(_after), content(_content), msg_id(_msg_id)
	{}
	static char *nameIRExpr(IRExpr *a) {
		char *ptr;
		size_t buf_size;
		FILE *f = open_memstream(&ptr, &buf_size);
		ppIRExpr(a, f);
		fclose(f);
		return ptr;
	}
	char *mkName() const {
		std::vector<const char *> fragments;

		fragments.push_back(my_asprintf(
					    "%d: %s <-< %s {", msg_id,
					    before.name(), after.name()));
		for (auto it = content.begin(); it != content.end(); it++) {
			fragments.push_back(nameIRExpr(*it));
			fragments.push_back(", ");
		}
		fragments.push_back("}");

		char *res_vex = flattenStringFragments(fragments);
		char *res_malloc = strdup(res_vex);
		_LibVEX_free(&main_heap, res_vex);
		free((void *)fragments[0]);
		for (unsigned x = 1; x < fragments.size() - 1; x += 2)
			free((void *)fragments[x]);
		return res_malloc;		
	}
public:
	ThreadRip before;
	ThreadRip after;
	std::vector<IRExpr *> content;
	unsigned msg_id;

	happensBeforeEdge *intern(internmentState &state) {
		content = state.intern(content);
		for (auto it = state.hbes.begin(); it != state.hbes.end(); it++) {
			if ( (*it)->msg_id == msg_id &&
			     (*it)->before == before &&
			     (*it)->after == after &&
			     (*it)->content == content )
				return (*it);
		}
		state.hbes.insert(this);
		return this;
	}
	happensBeforeEdge(bool invert, IRExprHappensBefore *hb,
			  instructionDominatorMapT &idom,
			  CFG<ThreadRip> *cfg,
			  expressionStashMapT &stashMap,
			  unsigned _msg_id)
		: before(invert ? hb->after.rip : hb->before.rip),
		  after(invert ? hb->before.rip : hb->after.rip),
		  msg_id(_msg_id)
	{
		printf("%x: HBE %s -> %s\n",
		       msg_id,
		       before.name(),
		       after.name());
		std::set<Instruction<ThreadRip> *> &liveInstructions(
			idom[cfg->ripToInstr->get(before)]);
		for (std::set<Instruction<ThreadRip> *>::iterator it = liveInstructions.begin();
		     it != liveInstructions.end();
		     it++) {
			Instruction<ThreadRip> *i = *it;
			std::set<std::pair<unsigned, IRExpr *> > &exprs(stashMap[i->rip.rip.unwrap_vexrip()]);
			for (std::set<std::pair<unsigned, IRExpr *> >::iterator it2 = exprs.begin();
			     it2 != exprs.end();
			     it2++) {
				if (it2->first == i->rip.thread)
					content.push_back(it2->second);
			}
		}
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%s", name());
	}
	static happensBeforeEdge *parse(const char *str, const char **suffix)
	{
		happensBeforeEdge *work = new happensBeforeEdge();
		if (!parseDecimalUInt(&work->msg_id, str, &str) ||
		    !parseThisString(": ", str, &str) ||
		    !parseThreadRip(&work->before, str, &str) ||
		    !parseThisString(" <-< ", str, &str) ||
		    !parseThreadRip(&work->after, str, &str) ||
		    !parseThisString(" {", str, &str))
			return NULL;
		while (1) {
			IRExpr *a;
			if (!parseIRExpr(&a, str, &str))
				break;
			if (!parseThisString(", ", str, &str))
				return NULL;
			work->content.push_back(a);
		}
		if (!parseThisChar('}', str, &str))
			return NULL;
		*suffix = str;
		return work;
	}
	void visit(HeapVisitor &hv) {
		visit_container(content, hv);
	}
	NAMED_CLASS
};

class slotMapT : public std::map<std::pair<unsigned, IRExpr *>, simulationSlotT>,
		 private GcCallback<&ir_heap> {
	typedef std::pair<unsigned, IRExpr *> key_t;
	void mk_slot(unsigned thr, IRExpr *e, simulationSlotT &next_slot) {
		key_t key(thr, e);
		if (!count(key)) {
			simulationSlotT s = allocateSlot(next_slot);
			insert(std::pair<key_t, simulationSlotT>(key, s));
		}
	}
	void runGc(HeapVisitor &hv) {
		slotMapT n(*this);
		clear();
		for (auto it = n.begin(); it != n.end(); it++) {
			std::pair<std::pair<unsigned, IRExpr *>, simulationSlotT> a = *it;
			hv(a.first.second);
			insert(a);
		}
	}
public:
	simulationSlotT rflagsSlot() {
		return simulationSlotT(0);
	}
	simulationSlotT allocateSlot(simulationSlotT &next_slot) {
		simulationSlotT r = next_slot;
		next_slot.idx++;
		return r;
	}

	simulationSlotT operator()(unsigned thr, IRExpr *e) {
		iterator it = find(std::pair<unsigned, IRExpr *>(thr, e));
		assert(it != end());
		return it->second;
	}

	void internSelf(internmentState &state) {
		std::map<std::pair<unsigned, IRExpr *>, simulationSlotT> work;
		for (auto it = begin(); it != end(); it++) {
			std::pair<unsigned, IRExpr *> key;
			work[state.intern(it->first)] = it->second;
		}
		clear();
		for (auto it = work.begin(); it != work.end(); it++)
			(*this)[it->first] = it->second;
	}

	slotMapT() { }

	slotMapT(std::map<unsigned long, std::set<std::pair<unsigned, IRExpr *> > > &neededExpressions,
		 std::map<unsigned long, std::set<happensBeforeEdge *> > &happensBefore,
		 simulationSlotT &next_slot)
	{
		/* Allocate slots for expressions which we know we're
		 * going to have to stash at some point. */
		for (std::map<unsigned long, std::set<key_t> >::iterator it = neededExpressions.begin();
		     it != neededExpressions.end();
		     it++) {
			std::set<key_t> &s((*it).second);
			for (std::set<key_t>::iterator it2 = s.begin();
			     it2 != s.end();
			     it2++)
				mk_slot(it2->first, it2->second, next_slot);
		}
		/* And the ones which we're going to receive in
		 * messages */
		for (std::map<unsigned long, std::set<happensBeforeEdge *> >::iterator it = happensBefore.begin();
		     it != happensBefore.end();
		     it++) {
			std::set<happensBeforeEdge *> &s(it->second);
			for (std::set<happensBeforeEdge *>::iterator it2 = s.begin();
			     it2 != s.end();
			     it2++) {
				happensBeforeEdge *hb = *it2;
				for (unsigned x = 0; x < hb->content.size(); x++)
					mk_slot(hb->after.thread, hb->content[x], next_slot);
			}
		}
	}

	void operator|=(const slotMapT &sm) {
		for (auto it = sm.begin(); it != sm.end(); it++)
			if (!count(it->first))
				insert(*it);
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "\tSlot map:\n");
		for (auto it = begin(); it != end(); it++) {
			fprintf(f, "\t\t%d:", it->first.first);
			it->first.second->prettyPrint(f);
			fprintf(f, " -> %d\n", it->second.idx);
		}
	}
	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Slot map:\n", str, &str))
			return false;
		clear();
		while (1) {
			std::pair<unsigned, IRExpr *> key;
			simulationSlotT value;
			if (!parseDecimalUInt(&key.first, str, &str) ||
			    !parseThisChar(':', str, &str) ||
			    !parseIRExpr(&key.second, str, &str) ||
			    !parseThisString(" -> ", str, &str) ||
			    !parseDecimalInt(&value.idx, str, &str) ||
			    !parseThisChar('\n', str, &str))
				break;
			(*this)[key] = value;
		}
		*suffix = str;
		return true;
	}
};

/* Note that this needs manual visiting (from the IR heap), despite
 * not being GC allocated itself! */
struct exprEvalPoint {
	bool invert;
	unsigned thread;
	IRExpr *e;

	void visit(HeapVisitor &hv) {
		hv(e);
	}

	exprEvalPoint(bool _invert,
		      unsigned _thread,
		      IRExpr *_e)
		: invert(_invert), thread(_thread), e(_e)
	{}
	bool operator <(const exprEvalPoint &o) const {
		if (invert < o.invert)
			return true;
		if (o.invert < invert)
			return false;
		if (thread < o.thread)
			return true;
		if (o.thread < thread)
			return false;
		return e < o.e;
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "%s%d:", invert ? "!" : "", thread);
		e->prettyPrint(f);
	}
	bool parse(const char *str, const char **suffix) {
		invert = false;
		if (parseThisChar('!', str, &str))
			invert = true;
		if (!parseDecimalUInt(&thread, str, &str) ||
		    !parseThisChar(':', str, &str) ||
		    !parseIRExpr(&e, str, &str))
			return false;
		*suffix = str;
		return true;
	}

	/* partially instantiating an exprEvalPoint is bad news, but
	   it's okay if done temporarily before calling parse().
	   Discourage people from hitting it by accident. */
	class YesIReallyMeanIt {};
	exprEvalPoint(const YesIReallyMeanIt &) {}
};

struct DirectRip : public Named {
	char *mkName() const { return my_asprintf("0x%lx", rip.rip); }

	struct _ {
		unsigned long rip;
		_(unsigned long r) : rip(r) {}
		_() {}
		operator unsigned long() const { return rip; }
		unsigned long unwrap_vexrip() const { return rip; }
		bool isValid() const { return rip != 0; }
	} rip;
	DirectRip(unsigned long _rip) : rip(_rip) {}
	DirectRip() : rip(0) {}
	bool operator==(const DirectRip &d) const { return rip == d.rip; }
	DirectRip operator+(long offset) const { return DirectRip(rip + offset); }
};

class ClientRip : public Named {
#define client_rip_types_iter(f)					\
	f(start_of_instruction)						\
	f(receive_messages)						\
	f(original_instruction)						\
	f(post_instr_generate)						\
	f(post_instr_checks)						\
	f(generate_messages)						\
	f(restore_flags_and_branch_post_instr_checks)			\
	f(pop_regs_restore_flags_and_branch_orig_instruction)		\
	f(rx_message)							\
	f(exit_threads_and_rx_message)					\
	f(exit_threads_and_pop_regs_restore_flags_and_branch_orig_instruction) \
	f(exit_threads_and_restore_flags_and_branch_post_instr_checks)	\
	f(uninitialised)

	char *mkName() const {
		std::vector<const char *> fragments;
		const char *label;
		bool free_label = false;
		switch (type) {
#define do_case(n) case n: label = #n; break;
			client_rip_types_iter(do_case)
#undef do_case
		default:
			label = my_asprintf("<bad%d>", type);
			free_label = true;
			break;
		}
		fragments.push_back(my_asprintf("%lx:%s{", (unsigned long)rip, label));
		if (free_label)
			free((void *)label);
		for (auto it = threads.begin(); it != threads.end(); it++)
			fragments.push_back(my_asprintf("%d,", *it));
		fragments.push_back(strdup("}"));
		if (type == rx_message)
			fragments.push_back(my_asprintf("hbe(%s)", completed_edge->name()));
		if (exit_threads_valid()) {
			fragments.push_back(strdup("thr{"));
			for (auto it = exit_threads.begin();
			     it != exit_threads.end();
			     it++)
				fragments.push_back(my_asprintf("%d, ", *it));
			fragments.push_back(strdup("}"));
		}
		if (skip_orig_valid())
			fragments.push_back(strdup(skip_orig ? "skip_orig" : "no_skip_orig"));
		char *res_vex = flattenStringFragments(fragments);
		char *res_malloc = strdup(res_vex);
		_LibVEX_free(&main_heap, res_vex);
		for (unsigned x = 0; x < fragments.size(); x++)
			free((void *)fragments[x]);
		return res_malloc;
	}
public:
	struct _{
		unsigned long rip;
		unsigned long unwrap_vexrip() const {
			return rip;
		}
		_(unsigned long r) : rip(r) {}
		_() {}
		operator unsigned long() const {
			return rip;
		}
		bool isValid() const { return rip != 0; }
	} rip;
	const happensBeforeEdge *completed_edge; /* Only valid for rx_message */
	bool skip_orig; /* Only valid for if skip_orig_valid() is true */
	std::set<int> exit_threads; /* Only for
				       exit_threads_and_rx_message and
				       exit_threads_and_pop_regs_... */

	bool skip_orig_valid() const {
		return type == receive_messages ||
			type == original_instruction ||
			type == rx_message ||
			type == pop_regs_restore_flags_and_branch_orig_instruction ||
			type == exit_threads_and_rx_message ||
			type == exit_threads_and_pop_regs_restore_flags_and_branch_orig_instruction;
	}

	bool exit_threads_valid() const {
		return type == exit_threads_and_rx_message ||
			type == exit_threads_and_pop_regs_restore_flags_and_branch_orig_instruction ||
			type == exit_threads_and_restore_flags_and_branch_post_instr_checks;
	}

	/* CAUTION! This comment is badly out of date! CAUTION! */
	/* Each original instruction (used to) expand into a sequence
	 * of psuedo-instructions:
	 *
	 * start_of_instruction:
	 * <generate anything which is generated at the start of the instruction>
	 * receive_messages:
	 * <receive any incoming messages>
	 * original_instruction:
	 * <the original instruction>
	 * <store any newly-generated expressions>
	 * post_instr_checks:
	 * <rest of checks>
	 * generate_messages:
	 * <generate any necessary messages>
	 *
	 * When we degrade from thread rips to client rips, we
	 * introduce appropriate zero-length instructions for each of
	 * the new steps.
	 *
	 * We also have a special type of alternative instruction,
	 * restore_flags_and_branch_{post_instr_checks,receive_messages},
	 * which just restores rflags and then jumps to either
	 * post_instr_checks or receive_messages, with the same RIP.
	 */
	enum instruction_type {
#define do_case(x) x,
		client_rip_types_iter(do_case)
#undef do_case
	};
private:
	bool parseType(instruction_type *res, const char *str, const char **suffix) {
#define do_case(n) if (parseThisString(#n, str, suffix)) { *res = n; return true; }
		client_rip_types_iter(do_case);
#undef do_case
		return false;
	}
public:
	bool parse(const char *str, const char **suffix) {
		if (!parseHexUlong(&rip.rip, str, &str) ||
		    !parseThisChar(':', str, &str) ||
		    !parseType(&type, str, &str) ||
		    !parseThisChar('{', str, &str))
			return false;
		int thread;
		threads.clear();
		while (1) {
			if (!parseDecimalInt(&thread, str, &str))
				break;
			if (!parseThisChar(',', str, &str))
				return false;
			threads.insert(thread);
		}
		if (!parseThisChar('}', str, &str))
			return false;
		if (type == rx_message) {
			if (!parseThisString("hbe(", str, &str))
				return false;
			completed_edge = happensBeforeEdge::parse(str, &str);
			if (!completed_edge)
				return false;
			if (!parseThisString(")", str, &str))
				return false;
		}
		if (exit_threads_valid()) {
			if (!parseThisString("thr{", str, &str))
				return false;
			exit_threads.clear();
			while (1) {
				int i;
				if (!parseDecimalInt(&i, str, &str))
					break;
				if (!parseThisString(", ", str, &str))
					return false;
				exit_threads.insert(i);
			}
			if (!parseThisString("}", str, &str))
				return false;
				
		}
		if (skip_orig_valid()) {
			if (parseThisString("skip_orig", str, &str))
				skip_orig = true;
			else if (parseThisString("no_skip_orig", str, &str))
				skip_orig = false;
			else
				return false;
		}
		*suffix = str;
		return true;
	}

	instruction_type type;

	std::set<unsigned> threads;
	std::set<unsigned> origThreads;

	ClientRip(unsigned long _rip, instruction_type _type)
		: rip(_rip), completed_edge(NULL), skip_orig(false), type(_type)
	{}
	ClientRip()
		: type(uninitialised)
	{}
	ClientRip(unsigned long _rip, const std::set<unsigned> &_threads, instruction_type _type)
		: rip(_rip), completed_edge(NULL), skip_orig(false), type(_type), threads(_threads), origThreads(_threads)
	{}
	ClientRip(const ClientRip &orig, instruction_type t)
		: rip(orig.rip), completed_edge(NULL), skip_orig(false), type(t), threads(orig.threads), origThreads(orig.origThreads)
	{}
	ClientRip(const ClientRip &orig, unsigned long _rip, instruction_type t)
		: rip(_rip), completed_edge(NULL), skip_orig(false), type(t), threads(orig.threads), origThreads(orig.origThreads)
	{}
	/* This ordering doesn't mean much, but it means that we can
	   use ClientRips as keys in std::map. */
	bool operator<(const ClientRip &k) const {
		if (type < k.type)
			return true;
		if (type > k.type)
			return false;
		if (rip < k.rip)
			return true;
		else if (rip > k.rip)
			return false;
		else if (threads < k.threads)
			return true;

		if (type == rx_message) {
			if (completed_edge < k.completed_edge)
				return true;
			if (completed_edge > k.completed_edge)
				return false;
		}
		if (skip_orig_valid()) {
			if (skip_orig > k.skip_orig)
				return true;
			if (skip_orig < k.skip_orig)
				return false;
		}
		if (exit_threads_valid()) {
			if (exit_threads < k.exit_threads)
				return true;
			if (exit_threads > k.exit_threads)
				return true;
		}
		return false;
	}
	bool operator!=(const ClientRip &k) const { return *this < k || k < *this; }
	bool operator==(const ClientRip &k) const { return !(*this != k); }

	bool threadLive(unsigned tid) const {
		return threads.count(tid) != 0;
	}
	bool noThreadsLive() const {
		return threads.empty();
	}
	void eraseThread(unsigned tid) {
		threads.erase(tid);
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "%s", name());
	}
};

class expressionEvalMapT : public std::map<unsigned long, std::set<exprEvalPoint> >,
			   private GcCallback<&ir_heap> {
	void runGc(HeapVisitor &hv) {
		for (auto it = begin(); it != end(); it++) {
			std::vector<exprEvalPoint> n;
			setToVector(it->second, n);
			it->second.clear();
			for (auto it2 = n.begin(); it2 != n.end(); it2++) {
				it2->visit(hv);
				it->second.insert(*it2);
			}
		}
	}
public:

	void internSelf(internmentState &state) {
		for (auto it = begin(); it != end(); it++)
			it->second = state.intern(it->second);
	}

	expressionEvalMapT(expressionDominatorMapT &exprDominatorMap) {
		for (expressionDominatorMapT::iterator it = exprDominatorMap.begin();
		     it != exprDominatorMap.end();
		     it++) {
			for (std::set<std::pair<bool, IRExpr *> >::iterator it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++)
				(*this)[it->first->rip.rip.unwrap_vexrip()].insert(
					exprEvalPoint(
						it2->first,
						it->first->rip.thread,
						it2->second));
		}
	}
	expressionEvalMapT() {}
	void operator|=(const expressionEvalMapT &eem) {
		for (auto it = eem.begin(); it != eem.end(); it++)
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				(*this)[it->first].insert(*it2);
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "\tEval map:\n");
		for (auto it = begin(); it != end(); it++) {
			fprintf(f, "\t\t%lx -> {", it->first);
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				it2->prettyPrint(f);
				fprintf(f, ", ");
			}
			fprintf(f, "}\n");
		}
	}
	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Eval map:\n", str, &str))
			return false;
		clear();
		while (1) {
			unsigned long key;
			std::set<exprEvalPoint> value;
			const char *a;
			if (!parseHexUlong(&key, str, &a) ||
			    !parseThisString(" -> {", a, &str))
				break;
			while (1) {
				exprEvalPoint::YesIReallyMeanIt y;
				exprEvalPoint p(y);
				if (!p.parse(str, &str))
					break;
				if (!parseThisString(", ", str, &str))
					return false;
				value.insert(p);
			}
			if (!parseThisString("}\n", str, &str))
				return false;
			(*this)[key] = value;
		}
		*suffix = str;
		return true;
	}
};

class EnforceCrashPatchFragment : public PatchFragment<ClientRip> {
	std::set<happensBeforeEdge *> edges;

	void generateEpilogue(ClientRip rip);

public:
	EnforceCrashPatchFragment(std::map<unsigned long, std::set<happensBeforeEdge *> > &happensBeforePoints,
				  const std::set<ClientRip> &roots)
		: PatchFragment<ClientRip>(roots)
	{
		for (std::map<unsigned long, std::set<happensBeforeEdge *> >::iterator it = happensBeforePoints.begin();
		     it != happensBeforePoints.end();
		     it++) {
			for (std::set<happensBeforeEdge *>::iterator it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++)
				edges.insert(*it2);
		}
	}

	char *asC(const char *ident, int max_rx_site_id);
};

class crashEnforcementRoots : public std::set<ClientRip> {
public:
	crashEnforcementRoots() {}

	crashEnforcementRoots(std::map<unsigned, ThreadRip> &roots) {
		std::map<unsigned long, std::set<unsigned> > threadsRelevantAtEachEntryPoint;
		for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
		     it != roots.end();
		     it++)
			threadsRelevantAtEachEntryPoint[it->second.rip.unwrap_vexrip()].insert(it->first);
		for (std::map<unsigned, ThreadRip>::iterator it = roots.begin();
		     it != roots.end();
		     it++) {
			std::set<unsigned> &threads(threadsRelevantAtEachEntryPoint[it->second.rip.unwrap_vexrip()]);
			insert(ClientRip(it->second.rip.unwrap_vexrip(), threads, ClientRip::start_of_instruction));
		}
	}

	void operator|=(const crashEnforcementRoots &cer) {
		for (auto it = cer.begin(); it != cer.end(); it++)
			insert(*it);
	}

	bool parse(const char *str, const char **suffix) {
		clear();
		if (!parseThisString("Roots: ", str, &str))
			return false;
		ClientRip r;
		while (1) {
			if (!r.parse(str, &str))
				break;
			if (!parseThisChar(' ', str, &str))
				return false;
			insert(r);
		}
		*suffix = str;
		return true;
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "\tRoots: ");
		for (auto it = begin(); it != end(); it++) {
			it->prettyPrint(f);
			fprintf(f, " ");
		}
		fprintf(f, "\n");
	}
};

class EnforceCrashCFG : public CFG<ThreadRip> {
public:
	std::set<ThreadRip> usefulInstrs;
	bool instructionUseful(Instruction<ThreadRip> *i) {
		if (usefulInstrs.count(i->rip))
			return true;
		else
			return false;
	}
	bool exploreFunction(ThreadRip) {
		return true;
	}
	EnforceCrashCFG(AddressSpace *as,
			const std::set<ThreadRip> &_usefulInstrs)
		: CFG<ThreadRip>(as), usefulInstrs(_usefulInstrs)
	{}
};

class happensBeforeMapT : public std::map<unsigned long, std::set<happensBeforeEdge *> >,
			  private GcCallback<&ir_heap> {
	void runGc(HeapVisitor &hv) {
		for (auto it = begin(); it != end(); it++)
			visit_set(it->second, hv);
	}
public:
	happensBeforeMapT() {}
	happensBeforeMapT(DNF_Conjunction &c,
			  expressionDominatorMapT &exprDominatorMap,
			  EnforceCrashCFG *cfg,
			  expressionStashMapT &exprStashPoints,
			  int &next_hb_id)
	{
		for (unsigned x = 0; x < c.size(); x++) {
			IRExpr *e = c[x].second;
			bool invert = c[x].first;
			if (e->tag == Iex_HappensBefore) {
				IRExprHappensBefore *hb = (IRExprHappensBefore *)e;
				happensBeforeEdge *hbe = new happensBeforeEdge(invert, hb, exprDominatorMap.idom,
									       cfg, exprStashPoints, next_hb_id++);
				(*this)[hbe->before.rip.unwrap_vexrip()].insert(hbe);
				(*this)[hbe->after.rip.unwrap_vexrip()].insert(hbe);
			}
		}
	}
	void operator|=(const happensBeforeMapT &hbm) {
		for (auto it = hbm.begin(); it != hbm.end(); it++) {
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				(*this)[it->first].insert(*it2);
		}
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "\tHappens before map:\n");
		for (auto it = begin(); it != end(); it++) {
			fprintf(f, "\t\t%lx -> {", it->first);
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				(*it2)->prettyPrint(f);
				fprintf(f, ", ");
			}
			fprintf(f, "}\n");
		}
	}
	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Happens before map:\n", str, &str))
			return false;
		clear();
		while (1) {
			unsigned long addr;
			std::set<happensBeforeEdge *> edges;
			if (!parseHexUlong(&addr, str, &str) ||
			    !parseThisString(" -> {", str, &str))
				break;
			while (1) {
				happensBeforeEdge *edge = happensBeforeEdge::parse(str, &str);
				if (!edge)
					break;
				edges.insert(edge);
				if (!parseThisString(", ", str, &str))
					return false;
			}
			if (!parseThisString("}\n", str, &str))
				return false;
			(*this)[addr] = edges;
		}
		*suffix = str;
		return true;
	}
	void internSelf(internmentState &state) {
		for (auto it = begin(); it != end(); it++) {
			std::set<happensBeforeEdge *> out;
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				out.insert( (*it2)->intern(state) );
			it->second = out;
		}
	}
};

/* Map that tells us where the various threads have to exit. */
class abstractThreadExitPointsT : public std::map<unsigned long, std::set<unsigned> > {
public:
	abstractThreadExitPointsT() {}
	abstractThreadExitPointsT(EnforceCrashCFG *cfg, happensBeforeMapT &);
	void operator|=(const abstractThreadExitPointsT &atet) {
		for (auto it = atet.begin(); it != atet.end(); it++)
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				(*this)[it->first].insert(*it2);
	}
	void prettyPrint(FILE *f) const {
		fprintf(f, "\tAbstract thread exit points:\n");
		for (auto it = begin(); it != end(); it++) {
			fprintf(f, "\t\t%lx -> {", it->first);
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++)
				fprintf(f, "%d, ", *it2);
			fprintf(f, "}\n");
		}
	}
	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Abstract thread exit points:\n", str, &str))
			return false;
		clear();
		while (1) {
			unsigned long key;
			std::set<unsigned> value;
			if (!parseHexUlong(&key, str, &str) ||
			    !parseThisString(" -> {", str, &str))
				break;
			while (1) {
				unsigned v;
				if (!parseDecimalUInt(&v, str, &str) ||
				    !parseThisString(", ", str, &str))
					break;
				value.insert(v);
			}
			if (!parseThisString("}\n", str, &str))
				return false;
			(*this)[key] = value;
		}
		*suffix = str;
		return true;
	}
};

class crashEnforcementData {
	void internSelf(internmentState &state) {
		exprStashPoints.internSelf(state);
		happensBeforePoints.internSelf(state);
		exprsToSlots.internSelf(state);
		expressionEvalPoints.internSelf(state);
	}
public:
	crashEnforcementRoots roots;
	expressionStashMapT exprStashPoints;
	happensBeforeMapT happensBeforePoints;
	slotMapT exprsToSlots;
	expressionEvalMapT expressionEvalPoints;
	abstractThreadExitPointsT threadExitPoints;

	crashEnforcementData(std::set<IRExpr *> &neededExpressions,
			     std::map<unsigned, ThreadRip> &_roots,
			     expressionDominatorMapT &exprDominatorMap,
			     StateMachine *probeMachine,
			     StateMachine *storeMachine,
			     DNF_Conjunction &conj,
			     EnforceCrashCFG *cfg,
			     int &next_hb_id,
			     simulationSlotT &next_slot)
		: roots(_roots),
		  exprStashPoints(neededExpressions, probeMachine, storeMachine, _roots),
		  happensBeforePoints(conj, exprDominatorMap, cfg, exprStashPoints, next_hb_id),
		  exprsToSlots(exprStashPoints, happensBeforePoints, next_slot),
		  expressionEvalPoints(exprDominatorMap),
		  threadExitPoints(cfg, happensBeforePoints)
	{}

	bool parse(const char *str, const char **suffix) {
		if (!parseThisString("Crash enforcement data:\n", str, &str) ||
		    !roots.parse(str, &str) ||
		    !exprStashPoints.parse(str, &str) ||
		    !happensBeforePoints.parse(str, &str) ||
		    !exprsToSlots.parse(str, &str) ||
		    !expressionEvalPoints.parse(str, &str) ||
		    !threadExitPoints.parse(str, &str))
			return false;
		internmentState state;
		internSelf(state);
		*suffix = str;
		return true;
	}
	crashEnforcementData() {}

	void prettyPrint(FILE *f) {
		fprintf(f, "Crash enforcement data:\n");
		roots.prettyPrint(f);
		exprStashPoints.prettyPrint(f);
		happensBeforePoints.prettyPrint(f);
		exprsToSlots.prettyPrint(f);
		expressionEvalPoints.prettyPrint(f);
		threadExitPoints.prettyPrint(f);
	}

	void operator|=(const crashEnforcementData &ced) {
		roots |= ced.roots;
		exprStashPoints |= ced.exprStashPoints;
		happensBeforePoints |= ced.happensBeforePoints;
		exprsToSlots |= ced.exprsToSlots;
		expressionEvalPoints |= ced.expressionEvalPoints;
		threadExitPoints |= ced.threadExitPoints;
	}
};

#endif /* !enforceCrash_hpp__ */
