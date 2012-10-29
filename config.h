#include "extra_config.h"

#ifndef CONTROL_LOG_DEPTH
#define CONTROL_LOG_DEPTH 10
#endif

#ifndef ASSERT_FAILED_ADDRESS
//#define ASSERT_FAILED_ADDRESS 0x40a770
#define ASSERT_FAILED_ADDRESS 0
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

#ifndef CONFIG_CLUSTER_THRESHOLD
#define CONFIG_CLUSTER_THRESHOLD 50
#endif

/* We do an initial clustering using @STORE_CLUSTER_THRESHOLD, and
   then backtrack by up to @CONFIG_MAX_STORE_BACKTRACK instructions to
   find a nice place to start the analysis from (where that's
   unambiguous). */
#ifndef STORE_CLUSTER_THRESHOLD
#define STORE_CLUSTER_THRESHOLD CONFIG_CLUSTER_THRESHOLD
#endif
#ifndef CONFIG_MAX_STORE_BACKTRACK
#define CONFIG_MAX_STORE_BACKTRACK 10
#endif

/* We always reach threshold1, and we can expand up to threshold2 if
   that looks like it'll reach a convenient place in the program to do
   analysis from. */
#ifndef PROBE_CLUSTER_THRESHOLD1
#define PROBE_CLUSTER_THRESHOLD1 CONFIG_CLUSTER_THRESHOLD
#endif
#ifndef PROBE_CLUSTER_THRESHOLD2
#define PROBE_CLUSTER_THRESHOLD2 CONFIG_CLUSTER_THRESHOLD
#endif

#ifndef CONFIG_DATABASE_RIP_DEPTH
#define CONFIG_DATABASE_RIP_DEPTH 4
#endif

#ifndef CONFIG_RECORD_MACHINE_OPTIMISATIONS
#define CONFIG_RECORD_MACHINE_OPTIMISATIONS 0
#endif

#ifndef CONFIG_USE_INDUCTION
#define CONFIG_USE_INDUCTION 1
#endif

#ifndef CONFIG_DISCARD_FLOATING_POINT
#define CONFIG_DISCARD_FLOATING_POINT 0
#endif
