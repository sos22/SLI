#include <assert.h>
#include <pthread.h>
#include <stdio.h>
#include <signal.h>
#include <unistd.h>
#include <stdlib.h>

#include "test.h"

static volatile int global;
static volatile bool getout;

asm (
"thr_main:\n"
"3:\n"
"  movzbl getout,%eax\n"
"  test   %al,%al\n"
"  jne    1f\n"
".fill 100,1,0x90\n"
"  mov global,%eax\n"
"  mov global,%edx\n"
"  lea (%rax,%rdx,1),%eax\n"
"  cmp $0x3, %eax\n"
"  je 2f\n"
".fill 100,1,0x90\n"
"  mov read_cntr, %eax\n"
"  inc %eax\n"
"  mov %eax, read_cntr\n"
"  jmp 3b\n"
"1:\n"
"  ret\n"
"2:\n"
"  mov $4f, %ecx\n"
"  mov $0x16, %edx\n"
"  mov $5f, %esi\n"
"  mov $6f, %edi\n"
"  call __assert_fail@plt\n"
"  int3\n"
"4:\n"
".asciz \"string1\"\n"
"5:\n"
".asciz \"string2\"\n"
"6:\n"
".asciz \"string4\"\n"
	);

extern unsigned char thr_main[];
static void
sighandler(int ign)
{
	getout = true;
}

int
main()
{
	pthread_t thr;

	pthread_create(&thr, NULL, (void *(*)(void *))thr_main, NULL);

	signal(SIGALRM, sighandler);
	if (!getenv("SOS22_RUN_FOREVER")) {
		alarm(10);
	}
	while (!getout) {
		STOP_ANALYSIS();
		global = 1;
		STOP_ANALYSIS();
		write_cntr++;
	}

	printf("Survived, %d read events and %d write events\n", read_cntr, write_cntr);
	return 0;
}
