#ifndef crashCfg_HPP__
#define crashCfg_HPP__

#include "libvex_parse.h"
#include "alloc_mai.hpp"
#include "cfgnode.hpp"
#include "genfix.hpp"
#include "inferred_information.hpp"

class CrashCfg;

class SummaryId : public Named {
	static unsigned next_id;
	unsigned id;
	char *mkName() const {
		return my_asprintf("%d", id);
	}
public:
	static SummaryId uninitialised()
	{
		return SummaryId(-1);
	}
	explicit SummaryId(unsigned _id)
		: id(_id)
	{}
	bool parse(const char *str, const char **suffix)
	{
		if (!parseDecimalUInt(&id, str, suffix))
			return false;
		clearName();
		return true;
	}
	bool operator==(const SummaryId &o) const
	{
		return id == o.id;
	}
	bool operator<(const SummaryId &o) const
	{
		return id < o.id;
	}
	unsigned long hash() const
	{
		return id * 10114771ul;
	}
};

class ConcreteThread : public Named {
public:
	SummaryId summary_id;
private:
	unsigned id;

	char *mkName() const {
		return my_asprintf("T%s:%d", summary_id.name(), id);
	}
public:
	ConcreteThread(const SummaryId &_summary_id, unsigned _id)
		: summary_id(_summary_id), id(_id)
	{}
	static ConcreteThread uninitialised() {
		return ConcreteThread(SummaryId::uninitialised(), -1);
	}
	bool parse(const char *str, const char **suffix)
	{
		clearName();
		if (!parseThisChar('T', str, &str) ||
		    !summary_id.parse(str, &str) ||
		    !parseThisChar(':', str, &str) ||
		    !parseDecimalUInt(&id, str, suffix))
			return false;
		return true;
	}
	bool operator==(const ConcreteThread &o) const
	{
		return summary_id == o.summary_id && id == o.id;
	}
	bool operator<(const ConcreteThread &o) const
	{
		return summary_id < o.summary_id ||
			(summary_id == o.summary_id && id < o.id);
	}
	unsigned long hash() const
	{
		return id * 10113569ul + summary_id.hash() * 10118387ul;
	}
	const SummaryId &summary() const { return summary_id; }
	unsigned raw_id() const { return id; }
};

class AbstractThread : public Named {
	friend class ThreadAbstracter;
	char *mkName() const {
		return my_asprintf("t%d", id);
	}
	AbstractThread(unsigned _id)
		: id(_id)
	{}
	unsigned id;
public:
	AbstractThread(const AbstractThread &o)
		: id (o.id)
	{}
	static AbstractThread uninitialised() {
		return AbstractThread(-1);
	}
	bool parse(const char *str, const char **suffix)
	{
		if (!parseThisChar('t', str, &str) ||
		    !parseDecimalUInt(&id, str, suffix))
			return false;
		clearName();
		return true;
	}
	bool operator==(const AbstractThread &o) const
	{
		return id == o.id;
	}
	bool operator<(const AbstractThread &o) const
	{
		return id < o.id;
	}
	unsigned long hash() const
	{
		return id * 10113109ul;
	}
};

class ThreadCfgLabel : public Named {
	char *mkName() const {
		return my_asprintf("%s:%s", label.name(), thread.name());
	}
public:
	AbstractThread thread;
	CfgLabel label;
	ThreadCfgLabel(const AbstractThread &_thread, const CfgLabel &_label)
		: thread(_thread), label(_label)
	{}
	ThreadCfgLabel()
		: thread(AbstractThread::uninitialised()), label(CfgLabel::uninitialised())
	{}
	bool operator <(const ThreadCfgLabel &o) const {
		return thread < o.thread ||
			(thread == o.thread && label < o.label);
	}
	bool operator!=(const ThreadCfgLabel &o) const {
		return (*this < o) || (o < *this);
	}
	bool operator==(const ThreadCfgLabel &o) const {
		return !(*this != o);
	}
	unsigned long hash() const {
		return thread.hash() * 874109 + label.hash() * 877939;
	}
	bool parse(const char *str, const char **suffix) {
		CfgLabel l(CfgLabel::uninitialised());
		AbstractThread t(AbstractThread::uninitialised());
		if (l.parse(str, &str) &&
		    parseThisChar(':', str, &str) &&
		    t.parse(str, suffix)) {
			label = l;
			thread = t;
			clearName();
			return true;
		}
		return false;
	}
};

class ConcreteCfgLabel : public Named {
	char *mkName() const {
		return my_asprintf("%s:%s", summary.name(), label.name());
	}
public:
	SummaryId summary;
	CfgLabel label;
	ConcreteCfgLabel(const SummaryId &_summary, const CfgLabel &_label)
		: summary(_summary), label(_label)
	{}
	ConcreteCfgLabel()
		: summary(SummaryId::uninitialised()), label(CfgLabel::uninitialised())
	{}
	bool operator <(const ConcreteCfgLabel &o) const {
		return summary < o.summary ||
			(summary == o.summary && label < o.label);
	}
	bool operator!=(const ConcreteCfgLabel &o) const {
		return (*this < o) || (o < *this);
	}
	bool operator==(const ConcreteCfgLabel &o) const {
		return !(*this != o);
	}
	unsigned long hash() const {
		return summary.hash() * 10120421 + label.hash() * 10123909;
	}
	bool parse(const char *str, const char **suffix) {
		CfgLabel l(CfgLabel::uninitialised());
		SummaryId t(SummaryId::uninitialised());
		if (t.parse(str, &str) &&
		    parseThisChar(':', str, &str) &&
		    l.parse(str, suffix)) {
			label = l;
			summary = t;
			clearName();
			return true;
		}
		return false;
	}
};

class ThreadAbstracter {
	std::map<ConcreteThread, std::set<AbstractThread> > content;
	AbstractThread nxtThread;
public:
	ThreadAbstracter()
		: nxtThread(1)
	{}
	class iterator {
		std::set<AbstractThread>::const_iterator it;
		std::set<AbstractThread>::const_iterator endIt;
	public:
		iterator(const std::set<AbstractThread> &a)
			: it(a.begin()), endIt(a.end())
		{}
		bool finished() const { return it == endIt; }
		void advance() { it++; }
		AbstractThread get() const { return *it; }

		iterator(double, double, double) {}
	};
	iterator begin(const ConcreteThread &tid) const {
		auto it = content.find(tid);
		assert(it != content.end());
		return iterator(it->second);
	}
	AbstractThread newThread(const ConcreteThread &oldTid)
	{
		AbstractThread res = nxtThread;
		nxtThread.id++;
		content[oldTid].insert(res);
		return res;
	}
	class thread_cfg_iterator {
		iterator content;
		CfgLabel where;
	public:
		thread_cfg_iterator(const iterator &_content, const CfgLabel &_where)
			: content(_content), where(_where)
		{}
		bool finished() const { return content.finished(); }
		void advance() { content.advance(); }
		ThreadCfgLabel get() const { return ThreadCfgLabel(content.get(), where); }

		/* Should only be used by mai_iterator */
		thread_cfg_iterator(double, double, double)
			: content(1.0, 1.0, 1.0),
			  where(CfgLabel::uninitialised())
		{}
	};
	thread_cfg_iterator begin(const ConcreteThread &tid, const CfgLabel &where) const
	{
		return thread_cfg_iterator( begin(tid), where);
	}

	class mai_iterator {
		MaiMap::const_iterator hl_iter;
		thread_cfg_iterator ll_iter;
		bool _finished;
		ThreadCfgLabel current_item;
		ConcreteThread tid;
		ThreadAbstracter *_this;
	public:
		bool finished() const { return _finished; }
		void advance() {
			if (hl_iter.finished()) {
				_finished = true;
				return;
			}
			assert(!ll_iter.finished());
			current_item = ll_iter.get();
			ll_iter.advance();
			if (!ll_iter.finished())
				return;
			while (1) {
				hl_iter.advance();
				if (hl_iter.finished())
					return;
				ll_iter = _this->begin(tid, hl_iter.label());
				if (!ll_iter.finished())
					return;
				ll_iter.advance();
			}
		}
		mai_iterator(const SummaryId &summary, const MaiMap &mai, const MemoryAccessIdentifier &rip, ThreadAbstracter *__this)
			: hl_iter(mai.begin(rip)),
			  ll_iter(1.0, 1.0, 1.0),
			  _finished(false),
			  tid(ConcreteThread(summary, rip.tid)),
			  _this(__this)
		{
			if (hl_iter.finished()) {
				_finished = true;
				return;
			}
			ll_iter = _this->begin(tid, hl_iter.label());
			while (ll_iter.finished()) {
				hl_iter.advance();
				if (hl_iter.finished()) {
					_finished = true;
					return;
				}
				ll_iter = _this->begin(tid, hl_iter.label());
			}
			advance();
		}
		ThreadCfgLabel get() const { return current_item; }
	};
	mai_iterator begin(const SummaryId &summary, const MaiMap &mai, const MemoryAccessIdentifier &rip)
	{
		return mai_iterator(summary, mai, rip, this);
	}

	class instr_iterator {
		mai_iterator underlying;
		CrashCfg &cfg;
	public:
		bool finished() const { return underlying.finished(); }
		void advance() { underlying.advance(); }
		Instruction<ThreadCfgLabel> *get() const;
		instr_iterator(const mai_iterator &_underlying, CrashCfg &_cfg)
			: underlying(_underlying), cfg(_cfg)
		{}
	};
	instr_iterator begin(const SummaryId &summary, const MaiMap &mai, const MemoryAccessIdentifier &rip, CrashCfg &cfg)
	{
		return instr_iterator(begin(summary, mai, rip), cfg);
	}

	const ConcreteThread &lookup(const AbstractThread &abs) const
	{
		for (auto it = content.begin(); it != content.end(); it++)
			if (it->second.count(abs))
				return it->first;
		abort();
	}

};

class crashEnforcementRoots {
	std::map<ConcreteThread, std::set<AbstractThread> > threadAbs;
public:
	std::map<AbstractThread, std::set<std::pair<CfgLabel, long> > > content;
	crashEnforcementRoots() {}

	crashEnforcementRoots(std::map<ConcreteThread, std::set<std::pair<CfgLabel, long> > > &roots, ThreadAbstracter &abs) {
		for (auto it = roots.begin(); it != roots.end(); it++) {
			assert(!threadAbs.count(it->first));
			AbstractThread tid(abs.newThread(it->first));
			threadAbs[it->first].insert(tid);
			content[tid] = it->second;
		}
	}

	bool empty() const {
		return content.empty();
	}

	void insert(ConcreteThread concrete_tid, long rspDelta, const ThreadCfgLabel &root)
	{
		threadAbs[concrete_tid].insert(root.thread);
		content[root.thread].insert(std::pair<CfgLabel, long>(root.label, rspDelta));
	}

	void operator|=(const crashEnforcementRoots &cer) {
		for (auto it = cer.threadAbs.begin(); it != cer.threadAbs.end(); it++)
			threadAbs[it->first].insert(it->second.begin(), it->second.end());
		for (auto it = cer.content.begin(); it != cer.content.end(); it++) {
			assert(!content.count(it->first));
			content[it->first] = it->second;
		}
	}

	void prettyPrint(FILE *f) const {
		fprintf(f, "\tThreads: ");
		for (auto it = threadAbs.begin(); it != threadAbs.end(); it++) {
			if (it != threadAbs.begin())
				fprintf(f, "; ");
			fprintf(f, "%s = {", it->first.name());
			for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
				if (it2 != it->second.begin())
					fprintf(f, ",");
				fprintf(f, "%s", it2->name());
			}
			fprintf(f, "}");
		}
		fprintf(f, "\n\tRoots: ");
		for (auto it = content.begin(); it != content.end(); it++) {
			if (it != content.begin())
				fprintf(f, "; ");
			fprintf(f, "%s = {", it->first.name());
			for (auto it2 = it->second.begin();
			     it2 != it->second.end();
			     it2++) {
				if (it2 != it->second.begin())
					fprintf(f, ",");
				fprintf(f, "%s(%ld)", it2->first.name(), it2->second);
			}
			fprintf(f, "}");
		}
		fprintf(f, "\n");
	}
	bool parse(const char *str, const char **suffix) {
		content.clear();
		threadAbs.clear();
		if (!parseThisString("Threads: ", str, &str))
			return false;
		while (1) {
			ConcreteThread concrete_tid(ConcreteThread::uninitialised());
			if (!concrete_tid.parse(str, &str) ||
			    threadAbs.count(concrete_tid) ||
			    !parseThisString(" = {", str, &str))
				return false;
			std::set<AbstractThread> &abs(threadAbs[concrete_tid]);
			while (1) {
				AbstractThread a(AbstractThread::uninitialised());
				if (!a.parse(str, &str))
					return false;
				abs.insert(a);
				if (parseThisString("}", str, &str))
					break;
				if (!parseThisChar(',', str, &str))
					return false;
			}
			if (parseThisChar('\n', str, &str))
				break;
			if (!parseThisString("; ", str, &str))
				return false;
		}
		if (!parseThisString("Roots: ", str, &str))
			return false;
		while (1) {
			AbstractThread abs(AbstractThread::uninitialised());
			if (!abs.parse(str, &str) ||
			    content.count(abs) ||
			    !parseThisString(" = {", str, &str))
				return false;
			std::set<std::pair<CfgLabel, long> > &roots(content[abs]);
			while (1) {
				CfgLabel a(CfgLabel::uninitialised());
				long rspDelta;
				if (!a.parse(str, &str) ||
				    !parseThisChar('(', str, &str) ||
				    !parseDecimalLong(&rspDelta, str, &str) ||
				    !parseThisChar(')', str, &str)) {
					return false;
				}
				roots.insert(std::pair<CfgLabel, long>(a, rspDelta));
				if (parseThisString("}", str, &str))
					break;
				if (!parseThisChar(',', str, &str))
					return false;
			}
			if (parseThisChar('\n', str, suffix))
				break;
			if (!parseThisString("; ", str, &str))
				return false;
		}
		return true;
	}

	/* Iterate over all of the ThreadCfgLabels with a given
	 * concrete tid. */
	class conc_iterator {
		const std::set<AbstractThread> *i2set;
		const std::map<AbstractThread, std::set<std::pair<CfgLabel, long> > > *content;
		const std::set<std::pair<CfgLabel, long> > *i3set;
		std::set<AbstractThread>::const_iterator it2;
		std::set<std::pair<CfgLabel, long> >::const_iterator it3;

	public:
		bool finished() const { return it2 == i2set->end(); }
		void advance() {
			assert(it2 != i2set->end());
			it3++;
			while (it3 == i3set->end()) {
				it2++;
				if (it2 == i2set->end())
					return;
				auto foo = content->find(*it2);
				assert(foo != content->end());
				i3set = &foo->second;
				it3 = i3set->begin();
			}
		}
		ThreadCfgLabel threadCfgLabel() const { return ThreadCfgLabel(*it2, it3->first); }
		long rspDelta() const { return it3->second; }
		const AbstractThread &abstract_tid() const { return *it2; }
		conc_iterator(const std::set<AbstractThread> *_i2set,
			      const std::map<AbstractThread, std::set<std::pair<CfgLabel, long> > > &_content)
			: i2set(_i2set), content(&_content)
		{
			it2 = i2set->begin();
			if (it2 == i2set->end())
				return;

			auto foo = content->find(*it2);
			assert(foo != content->end());
			i3set = &foo->second;

			it3 = i3set->begin();
			while (it3 == i3set->end()) {
				it2++;
				if (it2 == i2set->end())
					return;

				auto foo = content->find(*it2);
				assert(foo != content->end());
				i3set = &foo->second;

				it3 = i3set->begin();
			}
		}
		conc_iterator() {}
	};
	conc_iterator begin(ConcreteThread concrete_tid) {
		auto it = threadAbs.find(concrete_tid);
		assert(it != threadAbs.end());
		return conc_iterator(&it->second, content);
	}

	/* Iterate over all of the ThreadCfgLabels. */
	class iterator {
		const std::map<ConcreteThread, std::set<AbstractThread> > &threadAbs;
		std::map<ConcreteThread, std::set<AbstractThread> >::const_iterator it1;
		conc_iterator it2;

		const std::map<AbstractThread, std::set<std::pair<CfgLabel, long> > > &content;
	public:
		bool finished() const { return it1 == threadAbs.end(); }
		void advance() {
			assert(it1 != threadAbs.end());
			it2.advance();
			while (it2.finished()) {
				it1++;
				if (it1 == threadAbs.end())
					return;
				it2 = conc_iterator(&it1->second, content);
			}
		}
		ThreadCfgLabel threadCfgLabel() const { return it2.threadCfgLabel(); }
		long rspDelta() const { return it2.rspDelta(); }
		ConcreteThread concrete_tid() const { return it1->first; }
		const AbstractThread &abstract_tid() const { return it2.abstract_tid(); }
		iterator(const std::map<ConcreteThread, std::set<AbstractThread> > &_threadAbs,
			 const std::map<AbstractThread, std::set<std::pair<CfgLabel, long> > > &_content)
			: threadAbs(_threadAbs),
			  content(_content)
		{
			it1 = threadAbs.begin();
			if (it1 == threadAbs.end())
				return;
			it2 = conc_iterator(&it1->second, content);
			while (it2.finished()) {
				it1++;
				if (it1 == threadAbs.end())
					return;
				it2 = conc_iterator(&it1->second, content);
			}
		}
	};
	iterator begin() const { return iterator(threadAbs, content); }

	ConcreteThread lookupAbsThread(const AbstractThread &abs)
	{
#ifndef NDEBUG
		bool found_it = false;
		ConcreteThread res(ConcreteThread::uninitialised());
		for (auto it = threadAbs.begin(); it != threadAbs.end(); it++) {
			if (it->second.count(abs)) {
				assert(!found_it);
				res = it->first;
				found_it = true;
			}
		}
		assert(found_it);
		return res;
#else
		for (auto it = threadAbs.begin(); it != threadAbs.end(); it++) {
			if (it->second.count(abs))
				return it->first;
		}
		abort();
#endif
	}
};

class CrashCfg {
	std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *> content;
	std::map<ConcreteCfgLabel, VexRip> rips;
public:
	Instruction<ThreadCfgLabel> *findInstr(const ThreadCfgLabel &label) {
		auto it = content.find(label);
		if (it == content.end())
			return NULL;
		else
			return it->second;
	}
	CrashCfg() {};
	CrashCfg(crashEnforcementRoots &roots, const SummaryId &summaryId, CrashSummary *summary,
		 AddressSpace *as, bool need_relocs, const ThreadAbstracter &abs);
	CrashCfg(crashEnforcementRoots &roots, const std::map<SummaryId, CrashSummary *> &summaries,
		 AddressSpace *as, bool need_relocs, const ThreadAbstracter &abs);
	void init(crashEnforcementRoots &roots, const std::map<SummaryId, CrashSummary *> &summaries,
		  AddressSpace *as, bool need_relocs, const ThreadAbstracter &abs);
	
	bool parse(crashEnforcementRoots &roots, AddressSpace *as, bool generateRelocs, const char *str, const char **suffix);
	void prettyPrint(FILE *f, bool verbose = false);
	void operator|=(const CrashCfg &o) {
		for (auto it = o.content.begin(); it != o.content.end(); it++) {
			auto it2_did_insert = content.insert(*it);
			assert(it2_did_insert.second);
		}
		for (auto it = o.rips.begin(); it != o.rips.end(); it++)
			rips.insert(*it);
	}
	void removeAllBut(const std::set<Instruction<ThreadCfgLabel> *> &retain);

	class iterator {
		std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *>::const_iterator it;
		std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *>::const_iterator endIt;
	public:
		bool finished() const { return it == endIt; }
		void advance() { it++; }
		Instruction<ThreadCfgLabel> *instr() const { return it->second; }
		iterator(const std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *>::const_iterator &_it,
			 const std::map<ThreadCfgLabel, Instruction<ThreadCfgLabel> *>::const_iterator &_endIt)
			: it(_it), endIt(_endIt)
		{}

	};
	iterator begin() const { return iterator(content.begin(), content.end()); }
	const VexRip &labelToRip(const ConcreteCfgLabel &l) const;
};

Instruction<ThreadCfgLabel> *decode_instr(AddressSpace *as, unsigned long ptr, const ThreadCfgLabel &label,
					  unsigned *true_size, bool include_reloacs);

#endif /* !crashCfg_HPP__ */
