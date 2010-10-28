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

class GdbChannel;

class GdbCommand {
protected:
	GdbChannel *chan;
	void sendResponse(const char *fmt, ...);
public:
	static GdbCommand *read(int fd);
	virtual void doIt(VexPtr<MachineState > &, GarbageCollectionToken) = 0;
	GdbCommand(GdbChannel *_chan)
		: chan(_chan)
	{
	}
	virtual ~GdbCommand() {}
};

class GdbChannel {
	int fd;
	char *buf;
	unsigned buf_avail;
	unsigned buf_size;
	bool synchronised;
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
	GdbCommand *getCommand();

	void sendResponse(const char *buf);
	char *readCommand();
};

class UnknownCommand : public GdbCommand {
public:
	void doIt(VexPtr<MachineState > &, GarbageCollectionToken) { this->sendResponse(""); }
	UnknownCommand(GdbChannel *c) : GdbCommand(c) {}
};

class GetSigCommand : public GdbCommand {
public:
	void doIt(VexPtr<MachineState > &, GarbageCollectionToken) { this->sendResponse("S00"); }
	GetSigCommand(GdbChannel *c) : GdbCommand(c) {}
};

class QueryCommand : public GdbCommand {
	char *q;
public:
	void doIt(VexPtr<MachineState > &, GarbageCollectionToken);
	QueryCommand(GdbChannel *c, const char *n)
		: GdbCommand(c),
		  q(strdup(n))
	{
	}
	~QueryCommand() { free(q); }
};

class GetRegistersCommand : public GdbCommand {
public:
	void doIt(VexPtr<MachineState > &, GarbageCollectionToken);
	GetRegistersCommand(GdbChannel *c) : GdbCommand(c) {}
};

class GetRegisterCommand : public GdbCommand {
	unsigned regNr;
public:
	void doIt(VexPtr<MachineState > &, GarbageCollectionToken);
	GetRegisterCommand(GdbChannel *c, const char *b) : GdbCommand(c) { regNr = strtol(b, NULL, 16); }
};

class GetMemoryCommand : public GdbCommand {
	unsigned long addr;
	unsigned size;
public:
	void doIt(VexPtr<MachineState > &, GarbageCollectionToken);
	GetMemoryCommand(GdbChannel *c, const char *b) : GdbCommand(c) { sscanf(b, "%lx,%x", &addr, &size); }
};

class SetThreadCommand : public GdbCommand {
	ThreadId tid;
	bool query;
public:
	void doIt(VexPtr<MachineState > &, GarbageCollectionToken)
	{
		if (query)
			this->chan->currentTidQuery = tid;
		else if (tid._tid() != 0 && (int)tid._tid() != -1)
			this->chan->currentTidRun = tid;
		this->sendResponse("");
	}
	SetThreadCommand(GdbChannel *c, const char *b)
		: GdbCommand(c),
		  tid(ThreadId(strtol(b+1, NULL, 16))),
		  query(b[0] != 'c')
	{
	}
};

class ThreadAliveCommand : public GdbCommand {
	ThreadId tid;
public:
	void doIt(VexPtr<MachineState > &, GarbageCollectionToken);
	ThreadAliveCommand(GdbChannel *c, const char *b)
		: GdbCommand(c),
		  tid(ThreadId(strtol(b, NULL, 16)))
	{
	}
};

class DetachCommand : public GdbCommand {
public:
	void doIt(VexPtr<MachineState > &, GarbageCollectionToken) {abort(); }
	DetachCommand(GdbChannel *c) : GdbCommand(c) {}
};

class ContinueCommand : public GdbCommand {
	unsigned long newRip;
	bool haveNewRip;
public:
	void doIt(VexPtr<MachineState > &ms, GarbageCollectionToken);
	ContinueCommand(GdbChannel *c, const char *buf)
		: GdbCommand(c)
	{
		if (buf[0] == '0') {
			haveNewRip = false;
		} else {
			haveNewRip = true;
			newRip = strtol(buf, NULL, 16);
		}
	}
};

static unsigned long
htonlong(unsigned long x)
{
	return ((unsigned long)htonl(x) << 32) | htonl(x >> 32);
}

void
GetMemoryCommand::doIt(VexPtr<MachineState > &ms, GarbageCollectionToken)
{
	unsigned long *membuf = (unsigned long *)malloc(size * sizeof(unsigned long));
	try {
		ms->addressSpace->readMemory(addr, size, membuf, true, NULL);
	} catch (BadMemoryException exc) {
		this->sendResponse("E12");
		free(membuf);
		return;
	}

	char *chrbuf = (char *)malloc(size * 2 + 1);
	unsigned x;

	for (x = 0; x < size; x++)
		sprintf(chrbuf + x * 2, "%02x", (unsigned char)membuf[x]);
	free(membuf);
	this->sendResponse(chrbuf);
	free(chrbuf);
}

void
GetRegistersCommand::doIt(VexPtr<MachineState > &ms, GarbageCollectionToken)
{
	Thread *thr = ms->findThread(this->chan->currentTidQuery, true);

	if (thr) {
		char *buf = my_asprintf("%016lx%016lx%016lx%016lx%016lx%016lx%016lx%016lx",
					htonlong(thr->regs.get_reg(REGISTER_IDX(RAX))),
					htonlong(thr->regs.get_reg(REGISTER_IDX(RBX))),
					htonlong(thr->regs.get_reg(REGISTER_IDX(RCX))),
					htonlong(thr->regs.get_reg(REGISTER_IDX(RDX))),
					htonlong(thr->regs.get_reg(REGISTER_IDX(RSI))),
					htonlong(thr->regs.get_reg(REGISTER_IDX(RDI))),
					htonlong(thr->regs.get_reg(REGISTER_IDX(RBP))),
					htonlong(thr->regs.get_reg(REGISTER_IDX(RSP))));
		this->sendResponse(buf);
		free(buf);
	} else {
		this->sendResponse("E01");
	}
}

void
GetRegisterCommand::doIt(VexPtr<MachineState > &ms, GarbageCollectionToken)
{
	Thread *thr = ms->findThread(this->chan->currentTidQuery, true);
	unsigned long r;
	bool haveIt;

	if (!thr) {
		this->sendResponse("E01");
		return;
	}

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
		char *b = my_asprintf("%016lx", htonlong(r));
		this->sendResponse(b);
		free(b);
	} else {
		this->sendResponse("E01");
	}
}

void
QueryCommand::doIt(VexPtr<MachineState > &ms, GarbageCollectionToken)
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
	} else if (!strcmp(q, "Offsets") || !strcmp(q, "Symbol::")) {
		/* Not supported, but doesn't seem to be necessary,
		   and the warning gets really annoying after a
		   while. */
		this->sendResponse("E00");
	} else {
		warnx("unknown query %s", q);
		this->sendResponse("E00");
	}
}

void
ThreadAliveCommand::doIt(VexPtr<MachineState > &ms, GarbageCollectionToken)
{
	const Thread *thr = ms->findThread(tid, true);
	if (!thr || thr->exitted || thr->crashed)
		this->sendResponse("E01");
	else
		this->sendResponse("OK");
}

void
ContinueCommand::doIt(VexPtr<MachineState > &ms, GarbageCollectionToken t)
{
	VexPtr<Thread > thr(ms->findThread(this->chan->currentTidRun, true));
	if (!thr) {
		this->sendResponse("E99");
		return;
	}
	if (haveNewRip)
		thr->regs.set_reg(REGISTER_IDX(RIP), newRip);

        while (1) {
		ThreadEvent *evt = thr->runToEvent(thr, ms, LogReaderPtr(), t);
                InterpretResult res = evt->fake(ms);

		if (dynamic_cast<SignalEvent *>(evt) ||
		    res != InterpretResultContinue)
			break;
	}

	this->sendResponse("S03");
}

void
GdbCommand::sendResponse(const char *fmt, ...)
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

void
GdbChannel::sendResponse(const char *m)
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

char *
GdbChannel::readCommand()
{
	int r;

	while (1) {
		/* First, try to parse what we have. */
		if (buf_avail != 0) {
			if (buf[0] != '$') {
				if (!synchronised)
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
				synchronised = true;
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

GdbCommand *
GdbChannel::getCommand()
{
	char *buf;

	buf = readCommand();
	if (!buf)
		return NULL;
	/* Minimum commands for a full stub: g (read regs), G (write
	 * regs), m (read memory), M (write memory), c (continue), s
	 * (step).  Since we're only really inspecting state, we only
	 * need g and m. */
	GdbCommand *r;
	switch (buf[0]) {
	case '?':
		r = new GetSigCommand(this);
		break;
	case 'c':
		r = new ContinueCommand(this, buf + 1);
		break;
	case 'D':
		r = new DetachCommand(this);
		break;
	case 'g':
		r = new GetRegistersCommand(this);
		break;
	case 'H':
		r = new SetThreadCommand(this, buf + 1);
		break;
	case 'm':
		r = new GetMemoryCommand(this, buf + 1);
		break;
	case 'p':
		r = new GetRegisterCommand(this, buf + 1);
		break;
	case 'q':
		r = new QueryCommand(this, buf + 1);
		break;
	case 'T':
		r = new ThreadAliveCommand(this, buf + 1);
		break;
	default:
		printf("Unknown GDB command %s\n", buf);
		r = new UnknownCommand(this);
		break;
	}
	free(buf);
	return r;
}

GdbChannel *
GdbChannel::accept()
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

	return new GdbChannel(fd);
}

static void
gdb_machine_state(const MachineState *_ms)
{
	if (fork())
		return;

	/* Allowed because of the fork() */
	VexPtr<MachineState > ms(const_cast<MachineState *>(_ms));

	/* Force a GC, so as to clear up any mess we had left over
	 * from the parent. */
	LibVEX_gc(ALLOW_GC);

	GdbChannel *chan = GdbChannel::accept();

	while (1) {
		GdbCommand *cmd = chan->getCommand();
		if (!cmd)
			break;
		/* Bit of a hack.  Oh well. */
		if (dynamic_cast<DetachCommand *>(cmd)) {
			delete cmd;
			break;
		}
		cmd->doIt(ms, ALLOW_GC);
		delete cmd;
	}

	delete chan;

	_exit(0);
}

void
gdb_concrete(const MachineState *ms)
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
