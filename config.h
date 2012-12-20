#include "extra_config.h"

#ifndef CRASHED_THREAD
#define CRASHED_THREAD 1
#endif

#ifndef CONFIG_CLUSTER_THRESHOLD
#define CONFIG_CLUSTER_THRESHOLD 40
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

#ifndef PROBE_CLUSTER_THRESHOLD
#define PROBE_CLUSTER_THRESHOLD CONFIG_CLUSTER_THRESHOLD
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
