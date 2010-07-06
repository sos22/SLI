/* Simple gdb stub for inspecting machine states */
#include <sys/socket.h>
#include <sys/types.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <err.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <wait.h>

#include "sli.h"

template <typename ait> class GdbChannel;

template <typename ait>
class GdbCommand {
protected:
	GdbChannel<ait> *chan;
	void sendResponse(const char *fmt, ...);
public:
	static GdbCommand *read(int fd);
	virtual void doIt(MachineState<ait> *) = 0;
	GdbCommand<ait>(GdbChannel<ait> *_chan)
		: chan(_chan)
	{
	}
	virtual ~GdbCommand() {}
};

template <typename ait>
class GdbChannel {
	int fd;
	char *buf;
	unsigned buf_avail;
	unsigned buf_size;
	GdbChannel(int _fd)
		: fd(_fd),
		  buf(NULL),
		  buf_avail(0),
		  buf_size(0),
		  currentTidQuery(ThreadId(1)),
		  currentTidRun(ThreadId(1))
	{
	}
public:
	ThreadId currentTidQuery;
	ThreadId currentTidRun;
	unsigned threadInfoIndex;
	static GdbChannel *accept();
	~GdbChannel()
	{
		close(fd);
		free(buf);
	}
	GdbCommand<ait> *getCommand();

	void sendResponse(const char *buf);
	char *readCommand();
};

template <typename ait>
class UnknownCommand : public GdbCommand<ait> {
public:
	void doIt(MachineState<ait> *) { this->sendResponse(""); }
	UnknownCommand(GdbChannel<ait> *c) : GdbCommand<ait>(c) {}
};

template <typename ait>
class GetSigCommand : public GdbCommand<ait> {
public:
	void doIt(MachineState<ait> *) { this->sendResponse("S00"); }
	GetSigCommand(GdbChannel<ait> *c) : GdbCommand<ait>(c) {}
};

template <typename ait>
class QueryCommand : public GdbCommand<ait> {
	char *q;
public:
	void doIt(MachineState<ait> *);
	QueryCommand(GdbChannel<ait> *c, const char *n)
		: GdbCommand<ait>(c),
		  q(strdup(n))
	{
	}
	~QueryCommand() { free(q); }
};

template <typename ait>
class GetRegistersCommand : public GdbCommand<ait> {
public:
	void doIt(MachineState<ait> *);
	GetRegistersCommand(GdbChannel<ait> *c) : GdbCommand<ait>(c) {}
};

template <typename ait>
class GetRegisterCommand : public GdbCommand<ait> {
	unsigned regNr;
public:
	void doIt(MachineState<ait> *);
	GetRegisterCommand(GdbChannel<ait> *c, const char *b) : GdbCommand<ait>(c) { regNr = strtol(b, NULL, 16); }
};

template <typename ait>
class GetMemoryCommand : public GdbCommand<ait> {
	unsigned long addr;
	unsigned size;
public:
	void doIt(MachineState<ait> *);
	GetMemoryCommand(GdbChannel<ait> *c, const char *b) : GdbCommand<ait>(c) { sscanf(b, "%lx,%x", &addr, &size); }
};

template <typename ait>
class SetThreadCommand : public GdbCommand<ait> {
	ThreadId tid;
	bool query;
public:
	void doIt(MachineState<ait> *)
	{
		if (query)
			this->chan->currentTidQuery = tid;
		else if (tid._tid() != 0 && (int)tid._tid() != -1)
			this->chan->currentTidRun = tid;
		this->sendResponse("");
	}
	SetThreadCommand(GdbChannel<ait> *c, const char *b)
		: GdbCommand<ait>(c),
		  tid(ThreadId(strtol(b+1, NULL, 16))),
		  query(b[0] != 'c')
	{
	}
};

template <typename ait>
class ThreadAliveCommand : public GdbCommand<ait> {
	ThreadId tid;
public:
	void doIt(MachineState<ait> *);
	ThreadAliveCommand(GdbChannel<ait> *c, const char *b)
		: GdbCommand<ait>(c),
		  tid(ThreadId(strtol(b, NULL, 16)))
	{
	}
};

template <typename ait>
class DetachCommand : public GdbCommand<ait> {
public:
	void doIt(MachineState<ait> *) {abort(); }
	DetachCommand(GdbChannel<ait> *c) : GdbCommand<ait>(c) {}
};

template <typename ait>
class ContinueCommand : public GdbCommand<ait> {
	ait newRip;
	bool haveNewRip;
public:
	void doIt(MachineState<ait> *ms);
	ContinueCommand(GdbChannel<ait> *c, const char *buf)
		: GdbCommand<ait>(c)
	{
		if (buf[0] == '0') {
			haveNewRip = false;
		} else {
			haveNewRip = true;
			newRip = mkConst<ait>(strtol(buf, NULL, 16));
		}
	}
};

static unsigned long
htonlong(unsigned long x)
{
	return ((unsigned long)htonl(x) << 32) | htonl(x >> 32);
}

template <typename ait> void
GetMemoryCommand<ait>::doIt(MachineState<ait> *ms)
{
	ait *membuf = (ait *)malloc(size * sizeof(ait));
	try {
		ms->addressSpace->readMemory(mkConst<ait>(addr), size, membuf, true,
					     ms->findThread(this->chan->currentTidQuery));
	} catch (BadMemoryException<ait> exc) {
		this->sendResponse("E12");
		free(membuf);
		return;
	}

	char *chrbuf = (char *)malloc(size * 2 + 1);
	unsigned x;

	for (x = 0; x < size; x++)
		sprintf(chrbuf + x * 2, "%02x", (unsigned char)force(membuf[x]));
	free(membuf);
	this->sendResponse(chrbuf);
	free(chrbuf);
}

template <typename ait> void
GetRegistersCommand<ait>::doIt(MachineState<ait> *ms)
{
	const Thread<ait> *thr = ms->findThread(this->chan->currentTidQuery);

	char *buf = my_asprintf("%016lx%016lx%016lx%016lx%016lx%016lx%016lx%016lx",
				htonlong(force(thr->regs.get_reg(REGISTER_IDX(RAX)))),
				htonlong(force(thr->regs.get_reg(REGISTER_IDX(RBX)))),
				htonlong(force(thr->regs.get_reg(REGISTER_IDX(RCX)))),
				htonlong(force(thr->regs.get_reg(REGISTER_IDX(RDX)))),
				htonlong(force(thr->regs.get_reg(REGISTER_IDX(RSI)))),
				htonlong(force(thr->regs.get_reg(REGISTER_IDX(RDI)))),
				htonlong(force(thr->regs.get_reg(REGISTER_IDX(RBP)))),
				htonlong(force(thr->regs.get_reg(REGISTER_IDX(RSP)))));
	this->sendResponse(buf);
	free(buf);
}

template <typename ait> void
GetRegisterCommand<ait>::doIt(MachineState<ait> *ms)
{
	const Thread<ait> *thr = ms->findThread(this->chan->currentTidQuery);
	ait r;
	bool haveIt;

	switch (regNr) {
#define REG(nr, name) case nr: haveIt = true; r = thr->regs.get_reg(REGISTER_IDX(name)); break
		REG(0, RAX);
		REG(1, RBX);
		REG(2, RCX);
		REG(3, RDX);
		REG(4, RSI);
		REG(5, RDI);
		REG(6, RBP);
		REG(7, RSP);
		REG(8, R8);
		REG(9, R9);
		REG(10, R10);
		REG(11, R11);
		REG(12, R12);
		REG(13, R13);
		REG(14, R14);
		REG(15, R15);
		REG(16, RIP);
#undef REG
	default:
		printf("Unknown reg %d\n", regNr);
		haveIt = false;
		break;
	}

	if (haveIt) {
		char *b = my_asprintf("%016lx", htonlong(force(r)));
		this->sendResponse(b);
		free(b);
	} else {
		this->sendResponse("E01");
	}
}

template <typename ait> void
QueryCommand<ait>::doIt(MachineState<ait> *ms)
{
	if (!strcmp(q, "C")) {
		this->sendResponse("QC%x", this->chan->currentTidQuery._tid());
	} else if (!strcmp(q, "Supported")) {
		this->sendResponse("");
	} else if (!strcmp(q, "fThreadInfo")) {
		this->chan->threadInfoIndex = 1;
		this->sendResponse("m%d", ms->threads->index(0)->tid._tid());
	} else if (!strcmp(q, "sThreadInfo")) {
		if (this->chan->threadInfoIndex >= ms->threads->size()) {
			this->sendResponse("l");
		} else {
			this->sendResponse("m%d", ms->threads->index(this->chan->threadInfoIndex)->tid._tid());
			this->chan->threadInfoIndex++;
		}
	} else {
		warnx("unknown query %s", q);
		this->sendResponse("E00");
	}
}

template <typename ait> void
ThreadAliveCommand<ait>::doIt(MachineState<ait> *ms)
{
	const Thread<ait> *thr = ms->findThread(tid);
	if (thr->exitted || thr->crashed)
		this->sendResponse("E01");
	else
		this->sendResponse("OK");
}

template <typename ait> void
ContinueCommand<ait>::doIt(MachineState<ait> *ms)
{
	Thread<ait> *thr = ms->findThread(this->chan->currentTidRun);
	if (haveNewRip)
		thr->regs.set_reg(REGISTER_IDX(RIP), newRip);

        while (1) {
		ThreadEvent<ait> *evt = thr->runToEvent(ms->addressSpace, ms);
                InterpretResult res = evt->fake(ms);

		if (dynamic_cast<SignalEvent<ait> *>(evt) ||
		    res != InterpretResultContinue)
			break;
	}

	this->sendResponse("S03");
}

template <typename ait> void
GdbCommand<ait>::sendResponse(const char *fmt, ...)
{
	va_list args;
	char *buf;
	va_start(args, fmt);
	int x = vasprintf(&buf, fmt, args);
	(void)x;
	va_end(args);
	this->chan->sendResponse(buf);
	free(buf);
}

template <typename ait> void
GdbChannel<ait>::sendResponse(const char *m)
{
	char *obuf;
	unsigned x;
	unsigned csum;
	unsigned sent;
	int this_time;
	unsigned l;

top:
	csum = 0;
	for (x = 0; m[x]; x++)
		csum += (unsigned char)m[x];
	obuf = my_asprintf("$%s#%02x", m, csum & 0xff);
	l = strlen(obuf);
	for (sent = 0; sent < l; sent += this_time) {
		this_time = write(fd, obuf + sent, l - sent);
		if (this_time == 0)
			warnx("EOF sending response to debugger");
		if (this_time < 0)
			warn("sending response to debugger");
		if (this_time <= 0)
			break;
	}
	free(obuf);

	char b;
	if (read(fd, &b, 1) != 1) {
		warn("reading ack from debugger");
	} else if (b == '+') {
		return;
	} else if (b == '-') {
		warnx("retransmitting packet... %s", m);
		goto top;
	} else {
		warnx("unexpected response char %c from debugger", b);
	}
}

template <typename ait> char *
GdbChannel<ait>::readCommand()
{
	int r;

	while (1) {
		/* First, try to parse what we have. */
		if (buf_avail != 0) {
			if (buf[0] != '$') {
				warnx("garbage at start of debug packet: %.*s, expected to start with $", buf_avail, (char *)buf);
				char *s = (char *)memchr(buf, '$', buf_avail);
				if (s) {
					unsigned o = s - buf;
					memmove(buf, buf + o, buf_avail - o);
					buf_avail -= o;
				} else {
					buf_avail = 0;
				}
				continue;
			}

			char *hashmark = (char *)memchr(buf, '#', buf_avail);
			if (hashmark && hashmark + 3 - buf <= buf_avail) {
				/* Have a complete message.  Dupe it and return. */
				unsigned msg_size = hashmark - buf - 1;
				char *res = (char *)malloc(msg_size + 1);
				memcpy(res, buf + 1, msg_size);
				res[msg_size] = 0;
				memmove(buf, buf + msg_size + 4, buf_avail - (msg_size - 4));
				buf_avail -= msg_size + 4;
				if (write(fd, "+", 1) != 1)
					warn("send ack to debugger");
				return res;
			}
		}

		/* Don't yet have a complete message.  Keep reading. */
		if (buf_avail == buf_size) {
			if (buf_size == 0)
				buf_size = 128;
			else
				buf_size *= 2;
			buf = (char *)realloc(buf, buf_size);
		}
		r = ::read(fd, buf + buf_avail, buf_size - buf_avail - 1);
		if (r < 0)
			warn("receiving data from debugger");
		if (r == 0)
			warnx("EOF from debugger");
		if (r <= 0)
			return NULL;
		buf_avail += r;
	}
}

template <typename ait> GdbCommand<ait> *
GdbChannel<ait>::getCommand()
{
	char *buf;

	buf = readCommand();
	if (!buf)
		return NULL;
	/* Minimum commands for a full stub: g (read regs), G (write
	 * regs), m (read memory), M (write memory), c (continue), s
	 * (step).  Since we're only really inspecting state, we only
	 * need g and m. */
	GdbCommand<ait> *r;
	switch (buf[0]) {
	case '?':
		r = new GetSigCommand<ait>(this);
		break;
	case 'c':
		r = new ContinueCommand<ait>(this, buf + 1);
		break;
	case 'D':
		r = new DetachCommand<ait>(this);
		break;
	case 'g':
		r = new GetRegistersCommand<ait>(this);
		break;
	case 'H':
		r = new SetThreadCommand<ait>(this, buf + 1);
		break;
	case 'm':
		r = new GetMemoryCommand<ait>(this, buf + 1);
		break;
	case 'p':
		r = new GetRegisterCommand<ait>(this, buf + 1);
		break;
	case 'q':
		r = new QueryCommand<ait>(this, buf + 1);
		break;
	case 'T':
		r = new ThreadAliveCommand<ait>(this, buf + 1);
		break;
	default:
		printf("Unknown GDB command %s\n", buf);
		r = new UnknownCommand<ait>(this);
		break;
	}
	free(buf);
	return r;
}

template <typename ait> GdbChannel<ait> *
GdbChannel<ait>::accept()
{
	int lfd;
	struct sockaddr_in saddr;
	socklen_t saddr_size;

	lfd = socket(AF_INET, SOCK_STREAM, 0);
	if (lfd < 0) {
		warn("socket()");
		return NULL;
	}
	if (listen(lfd, 1) < 0) {
		warn("listen()");
		close(lfd);
		return NULL;
	}
	saddr_size = sizeof(saddr);
	if (getsockname(lfd, (struct sockaddr *)&saddr, &saddr_size) < 0) {
		warn("getsockname()");
		close(lfd);
		return NULL;
	}
	printf("Listening on port %d\n", htons(saddr.sin_port));

	int fd = ::accept(lfd, NULL, NULL);
	close(lfd);
	if (fd < 0) {
		warn("accept()");
		return NULL;
	}

	return new GdbChannel<ait>(fd);
}

template <typename ait> static void
gdb_machine_state(const MachineState<ait> *base_ms)
{
	MachineState<ait> *ms = base_ms->dupeSelf();

	VexGcRoot ms_keeper((void **)&ms, "gdb_machine_state");

	GdbChannel<ait> *chan = GdbChannel<ait>::accept();

	while (1) {
		GdbCommand<ait> *cmd = chan->getCommand();
		if (!cmd)
			break;
		/* Bit of a hack.  Oh well. */
		if (dynamic_cast<DetachCommand<ait> *>(cmd)) {
			delete cmd;
			break;
		}
		cmd->doIt(ms);
		delete cmd;
	}

	delete chan;
}

void
gdb_concrete(const MachineState<unsigned long> *ms)
{
	gdb_machine_state(ms);
}

void
gdb_abstract(const MachineState<abstract_interpret_value> *ms)
{
	gdb_machine_state(ms);
}

/* Support for attaching gdb to ourself. */
static volatile bool gdb_attached;
static pid_t gdb_pid;

void
gdb(void)
{
	if (gdb_pid) {
		/* Should already have a GDB.  See if it's exitted. */
		int status;
		pid_t r = waitpid(gdb_pid, &status, WNOHANG);
		if (r == gdb_pid) {
			/* Yes */
			gdb_pid = 0;
		} else {
			/* No */
			dbg_break("Debugger invoked");
			return;
		}
	}
	pid_t me = getpid();
	char *path = vex_asprintf("/proc/%d/exe", me);
	char buf[4097];
	if (readlink(path, buf, sizeof(buf)) < 0) {
		warn("cannot read %s", path);
		return;
	}
	pid_t gdb_pid = fork();
	if (gdb_pid == -1) {
		warn("fork()");
		return;
	}
	if (gdb_pid == 0) {
		execlp("gdb", "gdb", buf, vex_asprintf("%d", me), NULL);
		err(1, "executing gdb");
	}
	while (1) {
		int status;
		pid_t r = waitpid(gdb_pid, &status, WNOHANG);

		if (r == -1) {
			warn("waiting for gdb");
			break;
		}
		if (r == gdb_pid) {
			/* We're done. */
			gdb_pid = 0;
			break;
		}
		if (gdb_attached)
			break;

		sleep(1);
	}
}
