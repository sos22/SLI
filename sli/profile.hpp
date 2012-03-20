#ifndef PROFILER_HPP__
#define PROFILER_HPP__

#if SELECTIVE_PROFILING
void initialise_profiling();
void start_profiling();
void stop_profiling();
void dump_profiling_data();
#else
static inline void initialise_profiling() {}
static inline void start_profiling() {}
static inline void stop_profiling() {}
static inline void dump_profiling_data() {}
#endif

#endif /* !PROFILER_HPP__ */
