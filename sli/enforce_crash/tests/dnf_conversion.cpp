#include <sys/fcntl.h>
#include <unistd.h>

#include "../dnf.cpp"

int
main(int argc, char *argv[])
{
	init_sli();

	IRExpr *exp = readIRExpr(open(argv[1], O_RDONLY));

	printf("Input expression: ");
	ppIRExpr(exp, stdout);
	printf("\n");

	DNF_Disjunction res;

	dnf(exp, res);

	printDnf(res, stdout);

	return 0;
}
