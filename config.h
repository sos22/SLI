#include "extra_config.h"

#ifndef CONTROL_LOG_DEPTH
#define CONTROL_LOG_DEPTH 10
#endif

#ifndef ASSERT_FAILED_ADDRESS
#define ASSERT_FAILED_ADDRESS 0x40a770
#endif

#ifndef CRASHED_THREAD
#define CRASHED_THREAD 1
#endif

#ifndef DROP_STORES_DEPTH
#define DROP_STORES_DEPTH 5
#endif

#ifndef DROP_BRANCHES_DEPTH
#define DROP_BRANCHES_DEPTH 10
#endif

#ifndef MALLOC_ADDRESS
#define MALLOC_ADDRESS 0
#endif

#ifndef FREE_ADDRESS
#define FREE_ADDRESS 0
#endif

#ifndef __STACK_CHK_FAILED
#define __STACK_CHK_FAILED 0x4ffe80ul
#endif

#ifndef STORE_CLUSTER_THRESHOLD
#define STORE_CLUSTER_THRESHOLD 20
#endif

/* We always reach threshold1, and we can expand up to threshold2 if
   that looks like it'll reach a convenient place in the program to do
   analysis from. */
#ifndef PROBE_CLUSTER_THRESHOLD1
#define PROBE_CLUSTER_THRESHOLD1 20
#endif
#ifndef PROBE_CLUSTER_THRESHOLD2
#define PROBE_CLUSTER_THRESHOLD2 20
#endif
