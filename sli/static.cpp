/* Simple thing for experimenting with various forms of static
   analysis. */
#include <ctype.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>

#include "libvex_alloc.h"
#include "sli.h"
#include "map.h"

class Function;

class Instruction : public GarbageCollected<Instruction, &ir_heap>, public Named {
	IRStmt **statements;
	int nr_statements;
public:
	unsigned long rip;
	unsigned long _fallThroughRip;
	unsigned long _branchRip;
	Instruction *branch;
	Instruction *fallThrough;

protected:
	char *mkName() const { return my_asprintf("%lx", rip); }
public:
	Instruction(unsigned long rip, IRStmt **content, int nr_statements);
	void resolveSuccessors(Function *f);

	void visit(HeapVisitor &hv) { hv(statements); hv(branch); hv(fallThrough); }
	NAMED_CLASS
};

class Function : public GarbageCollected<Function>, public Named {
public:
	typedef gc_heap_map<unsigned long, Instruction, &ir_heap>::type instr_map_t;

	unsigned long rip;
	VexPtr<instr_map_t, &ir_heap> instructions;

protected:
	char *mkName() const { return my_asprintf("%lx", rip); }
public:
	Function(unsigned long _rip) :
		rip(_rip),
		instructions(new instr_map_t())
	{}

	bool hasInstruction(unsigned long rip) const { return instructions->hasKey(rip); }
	void addInstruction(Instruction *i) { instructions->set(i->rip, i); }
	Instruction *ripToInstruction(unsigned long rip) { return instructions->get(rip); }

	void visit(HeapVisitor &hv) { }
	NAMED_CLASS
};

class Oracle : public GarbageCollected<Oracle> {
	std::vector<unsigned long> unprocessedRoots;

	gc_heap_map<unsigned long, Function>::type *addrToFunctions;

	void processRoot(unsigned long x);
public:
	MachineState *ms;

	Oracle(MachineState *_ms)
		: addrToFunctions(new gc_heap_map<unsigned long, Function>::type()),
		  ms(_ms)
	{
	}

	void add_root(unsigned long root);
	void calculate(void);
	void list_functions(std::vector<Function *> *heads) {
		heads->clear();
		for (gc_heap_map<unsigned long, Function>::type::iterator i = addrToFunctions->begin();
		     i != addrToFunctions->end();
		     i++)
			heads->push_back(i.value());
	}
	void visit(HeapVisitor &hv) { hv(ms); hv(addrToFunctions); }
	NAMED_CLASS
};

void
Oracle::add_root(unsigned long root)
{
	unprocessedRoots.push_back(root);
}

void
Oracle::calculate(void)
{
	while (!unprocessedRoots.empty()) {
		unsigned long x = unprocessedRoots.back();
		unprocessedRoots.pop_back();
		processRoot(x);
	}
}

void
Oracle::processRoot(unsigned long x)
{
	if (addrToFunctions->hasKey(x)) {
		/* Already done */
		return;
	}

	printf("Discovered function at %lx\n", x);

	Function *work = new Function(x);

	/* Start by building a CFG of the function's instructions. */
	std::vector<unsigned long> unexplored;
	unexplored.push_back(x);
	while (!unexplored.empty()) {
		unsigned long rip = unexplored.back();
		unexplored.pop_back();

		if (work->hasInstruction(rip))
			continue;
		IRSB *irsb = ms->addressSpace->getIRSBForAddress(99, rip);
		if (!irsb) {
			printf("WARNING: No IRSB for %lx!\n", rip);
			continue;
		}
		assert(irsb->stmts[0]->tag == Ist_IMark);
		int end_of_instruction;
		for (end_of_instruction = 1;
		     end_of_instruction < irsb->stmts_used && irsb->stmts[end_of_instruction]->tag != Ist_IMark;
		     end_of_instruction++)
			;
		Instruction *i = new Instruction(rip, irsb->stmts + 1, end_of_instruction - 1);
		if (end_of_instruction == irsb->stmts_used) {
			if (irsb->jumpkind == Ijk_Call) {
				i->_fallThroughRip = extract_call_follower(irsb);
				if (irsb->next->tag == Iex_Const)
					unprocessedRoots.push_back(irsb->next->Iex.Const.con->Ico.U64);
			} else {
				if (irsb->next->tag == Iex_Const)
					i->_fallThroughRip = irsb->next->Iex.Const.con->Ico.U64;
			}
		} else {
			i->_fallThroughRip = irsb->stmts[end_of_instruction]->Ist.IMark.addr;
		}
		work->addInstruction(i);
		if (i->_fallThroughRip)
			unexplored.push_back(i->_fallThroughRip);
		if (i->_branchRip)
			unexplored.push_back(i->_branchRip);
	}

	/* Now go through and set successor pointers etc. */
	for (Function::instr_map_t::iterator it = work->instructions->begin();
	     it != work->instructions->end();
	     it++) {
		Instruction *i = it.value();
		i->resolveSuccessors(work);
	}
	addrToFunctions->set(work->rip, work);
}

Instruction::Instruction(unsigned long _rip, IRStmt **stmts, int nr_stmts)
	: statements((IRStmt **)__LibVEX_Alloc_Ptr_Array(&ir_heap, nr_stmts)),
	  nr_statements(nr_stmts),
	  rip(_rip)
{
	for (int i = 0; i < nr_statements; i++) {
		statements[i] = stmts[i];
		if (statements[i]->tag == Ist_Exit)
			_branchRip = statements[i]->Ist.Exit.dst->Ico.U64;
	}
}

void
Instruction::resolveSuccessors(Function *f)
{
	if (_fallThroughRip) {
		fallThrough = f->ripToInstruction(_fallThroughRip);
		assert(fallThrough);
	}
	if (_branchRip) {
		branch = f->ripToInstruction(_branchRip);
		assert(branch);
	}
}

/* Read a whole line into the GC heap */
static char *
read_line(FILE *f)
{
	size_t acc_size;
	size_t used;
	char *acc;
	int c;

	acc_size = 128;
	acc = (char *)LibVEX_Alloc_Bytes(acc_size);
	used = 0;
	while (1) {
		c = fgetc(f);
		if (c == '\n' || c == EOF)
			break;
		acc[used] = c;
		used++;
		if (used == acc_size) {
			acc_size *= 2;
			acc = (char *)LibVEX_realloc(&main_heap, acc, acc_size);
		}
	}
	if (c == EOF) {
		if (used == 0 || ferror(f))
			return NULL;
	}
	acc[used] = 0;
	return acc;
}

class BadParseException {
};

class Word : public GarbageCollected<Word>, public Named {
protected:
	char *mkName() const { return strdup(content); }
public:
	char *content;
	Word(const char *c, int len) {
		content = (char *)LibVEX_Alloc_Bytes(len + 1);
		memcpy(content, c, len);
		content[len] = 0;
	}
	bool operator==(const char *p) const {
		return strcmp(content, p) == 0;
	}
	operator unsigned long() const {
		errno = 0;
		char *end;
		unsigned long r = strtol(content, &end, 0);
		if (errno != 0 || *end != 0) {
			printf("Expected number; got %s\n", content);
			throw BadParseException();
		}
		return r;
	}
	void visit(HeapVisitor &hv) { hv(content); }
	NAMED_CLASS
};

static Word **
find_words(char *command)
{
	int i;
	int nr_words;
	int j;

	nr_words = 0;
	i = 0;
	while (1) {
		/* Find the start of the current word. */
		while (isspace(command[i]))
			i++;
		if (command[i] == 0)
			break;
		/* We have another word. */
		nr_words++;
		/* And now find its end */
		while (!isspace(command[i]) && command[i])
			i++;
	}

	Word **res;
	res = (Word **)__LibVEX_Alloc_Ptr_Array(&main_heap, nr_words + 1);
	j = 0;
	i = 0;
	nr_words = 0;
	while (1) {
		/* Find the start of the word */
		while (isspace(command[i]))
			i++;
		if (command[i] == 0)
			break;
		/* Now find the end. */
		j = i;
		while (!isspace(command[j]) && command[j])
			j++;
		res[nr_words] = new Word(command + i, j - i);
		nr_words++;
		i = j;
	}
	res[nr_words] = NULL;
	return res;
}

static void
list_heads(Oracle *oracle)
{
	std::vector<Function *> f;

	oracle->list_functions(&f);
	for (std::vector<Function *>::iterator it = f.begin();
	     it != f.end();
	     it++)
		printf("%s\n", (*it)->name());
}

static void
run_command(Oracle *oracle)
{
	printf("\n> ");
	fflush(stdout);
	char *command = read_line(stdin);
	if (!command)
		exit(0);
	Word **words = find_words(command);	

	if (*words[0] == "add_root") {
		oracle->add_root(*words[1]);
	} else if (*words[0] == "doit") {
		oracle->calculate();
	} else if (*words[0] == "list_heads") {
		list_heads(oracle);
	} else {
		printf("Unknown command %s\n", words[0]->content);
	}
}

int
main(int argc, char *argv[])
{
	init_sli();

	VexPtr<MachineState> ms(MachineState::readCoredump(argv[1]));
	VexPtr<Oracle> oracle(new Oracle(ms));

	while (1) {
		LibVEX_maybe_gc(ALLOW_GC);
		try {
			run_command(oracle);
		} catch (BadParseException e) {
		}
	}
}
