#include <sys/fcntl.h>
#include <err.h>
#include <errno.h>
#include <unistd.h>
#include <wait.h>

#include "sli.h"
#include "genfix.hpp"

class SourceSinkCFG : public CFG {
	static unsigned long __trivial_hash_function(const unsigned long &k) { return k; }	
	gc_map<unsigned long, bool, __trivial_hash_function> *sinkInstructions;
public:
	void add_sink(unsigned long rip) { (*sinkInstructions)[rip] = true; }
	void destruct() { this->~SourceSinkCFG(); }

	bool exploreInstruction(Instruction *i) { return !(*sinkInstructions)[i->rip]; }
	bool instructionUseful(Instruction *i) { return (*sinkInstructions)[i->rip]; }

	SourceSinkCFG(AddressSpace *as)
		: CFG(as)
	{
		sinkInstructions = new gc_map<unsigned long, bool, __trivial_hash_function>();
	}
	void visit(HeapVisitor &hv) {
		CFG::visit(hv);
		hv(sinkInstructions);
	}
};

class AddExitCallPatch : public PatchFragment {
protected:
	bool generateEpilogue(unsigned long exitRip);
	/* XXX should really override emitInstruction here to catch
	   indirect jmp and ret instructions; oh well. */
};

bool
AddExitCallPatch::generateEpilogue(unsigned long exitRip)
{
	Instruction *i = Instruction::pseudo(exitRip);

	cfg->registerInstruction(i);
	registerInstruction(i, content.size());

	emitCallSequence("(unsigned long)release_lock", true);
	emitJmpToRipHost(exitRip);

	return true;
}

struct CriticalSection {
	unsigned long entry;
	unsigned long exit;
};

static char *
mkPatch(AddressSpace *as, struct CriticalSection *csects, unsigned nr_csects)
{
	SourceSinkCFG *cfg = new SourceSinkCFG(as);
	for (unsigned x = 0; x < nr_csects; x++) {
		cfg->add_root(csects[x].entry, 50);
		cfg->add_sink(csects[x].exit);
	}
	cfg->doit();

	PatchFragment *pf = new AddExitCallPatch();
	pf->fromCFG(cfg);

	char *res = pf->asC();
	res = vex_asprintf("#include \"patch_head.h\"\n\n%s\nstatic unsigned long entry_points[] = {\n",
			   res);
	for (unsigned x = 0; x < nr_csects; x++)
		res = vex_asprintf("%s\t0x%lx,\n", res, csects[x].entry);
	return vex_asprintf("%s};\n\n#include \"patch_skeleton.c\"\n", res);
}

static void
safeWrite(int fd, const void *buf, size_t buf_size)
{
	unsigned written;
	int this_time;

	for (written = 0; written < buf_size; written += this_time) {
		this_time = write(fd, (const char*)buf + written, buf_size - written);
		if (this_time < 0)
			err(1, "writing to output file");
		if (this_time == 0)
			errx(1, "cannot write to output file");
	}
}

class DeleteOnDeath {
	char *path;
public:
	DeleteOnDeath(char *_path) : path(strdup(_path)) {}
	~DeleteOnDeath() { unlink(path); free(path); }
};

static int
spawn(const char *path, ...)
{
	va_list args;
	unsigned nr_args;
	const char *arg;
	const char **argv;

	va_start(args, path);
	nr_args = 2; /* Include argv[0] and the NULL terminator */
	while (1) {
		arg = va_arg(args, const char *);
		if (!arg)
			break;
		nr_args++;
	}
	va_end(args);

	argv = (const char **)malloc(sizeof(argv[0]) * nr_args);
	argv[0] = path;
	va_start(args, path);
	unsigned argc = 1;
	while (1) {
		argv[argc] = va_arg(args, const char *);
		if (argv[argc] == NULL)
			break;
		argc++;		
	}
	va_end(args);

	pid_t child = fork();
	if (child == 0) {
		execv(path, (char *const*)argv);
		err(1, "cannot exec %s", path);
	}
	if (child == -1)
		err(1, "cannot fork");

	int status;
	pid_t r = waitpid(child, &status, 0);
	if (r < 0)
		err(1, "waiting for child");
	assert(r == child);
	if (WIFEXITED(status))
		return WEXITSTATUS(status);
	if (WIFSIGNALED(status))
		return -WTERMSIG(status);
	abort();
}

int
main(int argc, char *argv[])
{
	if (argc < 4 || argc % 2)
		errx(1, "expected at least one critical section, and for each section to have two rips, plus the logfile");

	init_sli();

	/* The only thing we care about in the log file is the initial
	   memory layout.  We should arguably fast-forward it to the
	   point for which the patch was created, so that we can
	   handle e.g. self-modifying code, but that's a pain, and
	   there are so many other things which go wrong when code
	   changes while you're trying to fix it that it's not worth
	   it. */
	LogReaderPtr ptr;
	VexPtr<LogReader> lf(LogReader::open(argv[1], &ptr));
	if (!lf)
		err(1, "opening %s", argv[1]);
	MachineState *ms = MachineState::initialMachineState(lf, ptr, &ptr, ALLOW_GC);
	AddressSpace *as = ms->addressSpace;

	CriticalSection *csects = (CriticalSection *)malloc(sizeof(CriticalSection) * (argc - 2) / 2);
	for (int x = 0; x < (argc - 2) / 2; x++) {
		csects[x].entry = strtol(argv[x * 2 + 2], NULL, 16);
		csects[x].exit = strtol(argv[x * 2 + 3], NULL, 16);
	}

	char *patchFragment = mkPatch(as, csects, (argc - 2) / 2);

	char *tmpPath;
	int tmpFd;
	while (1) {
		tmpPath = tempnam(NULL, NULL);
		tmpFd = open(tmpPath, O_WRONLY|O_CREAT|O_EXCL|O_APPEND, 0600);
		if (tmpFd >= 0)
			break;
		if (errno != EEXIST)
			err(1, "creating temporary file");
		free(tmpPath);
	}
	DeleteOnDeath dod(tmpPath);
	safeWrite(tmpFd, patchFragment, strlen(patchFragment));

	int r = spawn("/usr/bin/gcc",
		      "-Wall",
		      "-shared",
		      "-fPIC",
		      "-I",
		      "sli",
		      "-x"
		      "c",
		      tmpPath,
		      "-o",
		      "patch1.so",
		      NULL);

	printf("gcc said %d\n", r);

	return 0;
}
