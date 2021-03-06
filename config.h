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
#define CONFIG_DATABASE_RIP_DEPTH 1
#endif

#ifndef CONFIG_RECORD_MACHINE_OPTIMISATIONS
#define CONFIG_RECORD_MACHINE_OPTIMISATIONS 0
#endif

#ifndef CONFIG_USE_INDUCTION
#define CONFIG_USE_INDUCTION 0
#endif

#ifndef CONFIG_DISCARD_FLOATING_POINT
#define CONFIG_DISCARD_FLOATING_POINT 0
#endif

#ifndef CONFIG_STATIC_ANALYSIS
#define CONFIG_STATIC_ANALYSIS 1
#endif

/* Bit of a hack: the free() template stores the last free()d address
   here, so that the double_free stub can find it and decide whether
   we've suffered a double free bug.  The precise value doesn't
   matter, provided it doesn't overlap with any addresses which the
   program actually accesses.  A denormal address satisfies that
   nicely. */
#ifndef CONFIG_LASTFREE_ADDR
#define CONFIG_LASTFREE_ADDR 0x800000000008
#endif

#ifndef CONFIG_PHI_ELIMINATION
#define CONFIG_PHI_ELIMINATION 1
#endif

#ifndef CONFIG_LOAD_ELIMINATION
#define CONFIG_LOAD_ELIMINATION 1
#endif

#ifndef CONFIG_REALIAS_SIMPLE_ONLY
#define CONFIG_REALIAS_SIMPLE_ONLY 1
#endif

#ifndef CONFIG_NO_DYNAMIC_ALIASING
#define CONFIG_NO_DYNAMIC_ALIASING 0
#endif

#ifndef CONFIG_NO_STATIC_ALIASING
#define CONFIG_NO_STATIC_ALIASING (!CONFIG_STATIC_ANALYSIS)
#endif

#ifndef CONFIG_STACKED_CDF
#define CONFIG_STACKED_CDF 0
#endif

#ifndef CONFIG_FIXED_REGS
#define CONFIG_FIXED_REGS CONFIG_STATIC_ANALYSIS
#endif

#ifndef CONFIG_W_ISOLATION
#define CONFIG_W_ISOLATION 1
#endif

#if !CONFIG_NO_STATIC_ALIASING && CONFIG_LOAD_ELIMINATION
#define TRACK_FRAMES 1
#else
#define TRACK_FRAMES 0
#endif

#ifndef CONFIG_SIMPLIFIER
#define CONFIG_SIMPLIFIER 1
#endif

/* How long do we have to do the per-crashing-thread bits, in seconds? */
#ifndef CONFIG_TIMEOUT1
#define CONFIG_TIMEOUT1 60
#endif
#ifndef CONFIG_TIMEOUT2
#define CONFIG_TIMEOUT2 60
#endif

#ifndef TIMEOUT_EC_STRATEGY
#define TIMEOUT_EC_STRATEGY 60
#endif
#ifndef TIMEOUT_EC_DRIVER
#define TIMEOUT_EC_DRIVER 60
#endif
#ifndef TIMEOUT_EC_SLICE_HB
#define TIMEOUT_EC_SLICE_HB 60
#endif
#ifndef TIMEOUT_EC_PLACE
#define TIMEOUT_EC_PLACE 60
#endif

#ifndef CONFIG_USE_CHILDREN
#define CONFIG_USE_CHILDREN 1
#endif

#ifndef CONFIG_NO_W_ATOMIC
#define CONFIG_NO_W_ATOMIC 0
#endif

#ifndef CONFIG_NO_SELF_RACE
#define CONFIG_NO_SELF_RACE 0
#endif
