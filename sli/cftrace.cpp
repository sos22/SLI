#include <err.h>

#include <vector>
#include <map>

#include "sli.h"

class GetControlTraces : public EventRecorder<unsigned long> {
public:
	typedef std::vector<unsigned long> vtype;
	typedef std::map<ThreadId, vtype> mtype;
	typedef mtype::iterator iterator;
private:
	mtype map;
public:
	iterator begin() { return map.begin(); }
	iterator end() { return map.end(); }

	void record(Thread<unsigned long> *thr,
		    ThreadEvent<unsigned long> *evt);

	void visit(HeapVisitor &hv) { }
	void destruct() {}
};

void GetControlTraces::record(Thread<unsigned long> *thr,
			      ThreadEvent<unsigned long> *evt)
{
	const InstructionEvent<unsigned long> *ie =
		dynamic_cast<const InstructionEvent<unsigned long> *>(evt);
	if (!ie)
		return;

	iterator i = map.find(thr->tid);
	if (i == map.end()) {
		vtype v;
		v.push_back(ie->rip);
		map.insert( std::pair<ThreadId, vtype>(thr->tid, v) );
	} else {
		i->second.push_back(ie->rip);
	}
}

int
main(int argc, char *argv[])
{
	init_sli();

	LogReaderPtr ptr;

	VexPtr<LogReader<unsigned long> > lf(LogFile::open(argv[1], &ptr));
	if (!lf)
		err(1, "opening %s", argv[1]);
	VexGcRoot k((void **)&lf, "lf");

	MachineState<unsigned long> *m = MachineState<unsigned long>::initialMachineState(lf, ptr, &ptr, ALLOW_GC);

	Interpreter<unsigned long> i(m);

	VexPtr<GetControlTraces> gct(new GetControlTraces());
	VexPtr<EventRecorder<unsigned long> > downcast(gct.get());
	VexPtr<LogWriter<unsigned long> > dummy(NULL);
	i.replayLogfile(lf, ptr, ALLOW_GC, NULL, dummy, downcast);

	for (GetControlTraces::iterator i = gct->begin();
	     i != gct->end();
	     i++) {
		printf("Thread %d:\n", i->first._tid());
		for (GetControlTraces::vtype::iterator j = i->second.begin();
		     j != i->second.end();
		     j++)
			printf("\t%lx\n", *j);
	}

	return 0;
}
