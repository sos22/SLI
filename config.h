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
#define STORE_CLUSTER_THRESHOLD 50
#endif

#ifndef PROBE_CLUSTER_THRESHOLD
#define PROBE_CLUSTER_THRESHOLD 10
#endif
