/* Simple gdb stub for inspecting machine states */
#include <sys/socket.h>
#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <err.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "sli.h"

class GdbChannel;

class GdbCommand {
protected:
	GdbChannel *chan;
	void sendResponse(const char *fmt, ...);
public:
	static GdbCommand *read(int fd);
	virtual void doIt(MachineState *) = 0;
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
	void doIt(MachineState *) { sendResponse(""); }
	UnknownCommand(GdbChannel *c) : GdbCommand(c) {}
};

class GetSigCommand : public GdbCommand {
public:
	void doIt(MachineState *) { sendResponse("S00"); }
	GetSigCommand(GdbChannel *c) : GdbCommand(c) {}
};

class QueryCommand : public GdbCommand {
	char *q;
public:
	void doIt(MachineState *);
	QueryCommand(GdbChannel *c, const char *n)
		: GdbCommand(c),
		  q(strdup(n))
	{
	}
	~QueryCommand() { free(q); }
};

class GetRegistersCommand : public GdbCommand {
public:
	void doIt(MachineState *);
	GetRegistersCommand(GdbChannel *c) : GdbCommand(c) {}
};

class GetRegisterCommand : public GdbCommand {
	unsigned regNr;
public:
	void doIt(MachineState *);
	GetRegisterCommand(GdbChannel *c, const char *b) : GdbCommand(c) { regNr = strtol(b, NULL, 16); }
};

class GetMemoryCommand : public GdbCommand {
	unsigned long addr;
	unsigned size;
public:
	void doIt(MachineState *);
	GetMemoryCommand(GdbChannel *c, const char *b) : GdbCommand(c) { sscanf(b, "%lx,%x", &addr, &size); }
};

class SetThreadCommand : public GdbCommand {
	ThreadId tid;
	bool query;
public:
	void doIt(MachineState *)
	{
		if (query)
			chan->currentTidQuery = tid;
		else if (tid._tid() != 0 && (int)tid._tid() != -1)
			chan->currentTidRun = tid;
		sendResponse("");
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
	void doIt(MachineState *);
	ThreadAliveCommand(GdbChannel *c, const char *b)
		: GdbCommand(c),
		  tid(ThreadId(strtol(b, NULL, 16)))
	{
	}
};

class DetachCommand : public GdbCommand {
public:
	void doIt(MachineState *) {abort(); }
	DetachCommand(GdbChannel *c) : GdbCommand(c) {}
};

class ContinueCommand : public GdbCommand {
	unsigned long newRip;
	bool haveNewRip;
public:
	void doIt(MachineState *ms);
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

static unsigned long htonlong(unsigned long x)
{
	return ((unsigned long)htonl(x) << 32) | htonl(x >> 32);
}

void GetMemoryCommand::doIt(MachineState *ms)
{
	char *membuf = (char *)malloc(size);
	try {
		ms->addressSpace->readMemory(addr, size, membuf, true);
	} catch (BadMemoryException exc) {
		sendResponse("E12");
		free(membuf);
		return;
	}

	char *chrbuf = (char *)malloc(size * 2 + 1);
	unsigned x;

	for (x = 0; x < size; x++)
		sprintf(chrbuf + x * 2, "%02x", (unsigned char)membuf[x]);
	free(membuf);
	sendResponse(chrbuf);
	free(chrbuf);
}

void GetRegistersCommand::doIt(MachineState *ms)
{
	const Thread *thr = ms->findThread(chan->currentTidQuery);

	char *buf = my_asprintf("%016lx%016lx%016lx%016lx%016lx%016lx%016lx%016lx",
				htonlong(thr->regs.get_reg(REGISTER_IDX(RAX))),
				htonlong(thr->regs.get_reg(REGISTER_IDX(RBX))),
				htonlong(thr->regs.get_reg(REGISTER_IDX(RCX))),
				htonlong(thr->regs.get_reg(REGISTER_IDX(RDX))),
				htonlong(thr->regs.get_reg(REGISTER_IDX(RSI))),
				htonlong(thr->regs.get_reg(REGISTER_IDX(RDI))),
				htonlong(thr->regs.get_reg(REGISTER_IDX(RBP))),
				htonlong(thr->regs.get_reg(REGISTER_IDX(RSP))));
	sendResponse(buf);
	free(buf);
}

void GetRegisterCommand::doIt(MachineState *ms)
{
	const Thread *thr = ms->findThread(chan->currentTidQuery);
	unsigned long r;
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
		char *b = my_asprintf("%016lx", htonlong(r));
		sendResponse(b);
		free(b);
	} else {
		sendResponse("E01");
	}
}

void QueryCommand::doIt(MachineState *ms)
{
	if (!strcmp(q, "C")) {
		sendResponse("QC%x", chan->currentTidQuery._tid());
	} else if (!strcmp(q, "Supported")) {
		sendResponse("");
	} else if (!strcmp(q, "fThreadInfo")) {
		chan->threadInfoIndex = 1;
		sendResponse("m%d", ms->threads->index(0)->tid._tid());
	} else if (!strcmp(q, "sThreadInfo")) {
		if (chan->threadInfoIndex >= ms->threads->size()) {
			sendResponse("l");
		} else {
			sendResponse("m%d", ms->threads->index(chan->threadInfoIndex)->tid._tid());
			chan->threadInfoIndex++;
		}
	} else {
		warnx("unknown query %s", q);
		sendResponse("E00");
	}
}

void ThreadAliveCommand::doIt(MachineState *ms)
{
	const Thread *thr = ms->findThread(tid);
	if (thr->exitted || thr->crashed)
		sendResponse("E01");
	else
		sendResponse("OK");
}

void ContinueCommand::doIt(MachineState *ms)
{
	Thread *thr = ms->findThread(chan->currentTidRun);
	if (haveNewRip)
		thr->regs.set_reg(REGISTER_IDX(RIP), newRip);

        while (1) {
                ThreadEvent *evt = thr->runToEvent(ms->addressSpace);
                PointerKeeper<ThreadEvent> k_evt(evt);
                InterpretResult res = evt->fake(thr, ms);

		if (dynamic_cast<SignalEvent *>(evt) ||
		    res != InterpretResultContinue)
			break;
	}

	sendResponse("S03");
}

void GdbCommand::sendResponse(const char *fmt, ...)
{
	va_list args;
	char *buf;
	va_start(args, fmt);
	int x = vasprintf(&buf, fmt, args);
	(void)x;
	va_end(args);
	chan->sendResponse(buf);
	free(buf);
}

void GdbChannel::sendResponse(const char *m)
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

char *GdbChannel::readCommand()
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

GdbCommand *GdbChannel::getCommand()
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

GdbChannel *GdbChannel::accept()
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

void
gdb_machine_state(const MachineState *base_ms)
{
	MachineState *ms = base_ms->dupeSelf();

	VexGcRoot ms_keeper((void **)&ms);

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
		cmd->doIt(ms);
		delete cmd;
	}

	delete chan;
}
