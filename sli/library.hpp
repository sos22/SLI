#ifndef LIBRARY_HPP__
#define LIBRARY_HPP__

#include "libvex_parse.h"

namespace LibraryFunctionTemplate {
#define enum_library_function_templates(f)	\
	f(__cxa_atexit)				\
	f(bzero)				\
	f(strlen)				\
	f(memcpy)				\
	f(memset)				\
	f(malloc)				\
	f(free)					\
	f(pthread_mutex_lock)			\
	f(pthread_mutex_unlock)			\
	f(__stack_chk_fail)			\
	f(time)

	enum __type {
		none = 0,
#define def_one(n) n,
		enum_library_function_templates(def_one)
#undef def_one
	};

	static inline void pp(enum __type t, FILE *f) {
		switch (t) {
#define do_one(n)					\
		case n :				\
			fprintf(f, "%s", #n);		\
			break;
		enum_library_function_templates(do_one)
#undef do_one
		case none:
			fprintf(f, "<not_a_library>");
			break;
		default:
			fprintf(f, "<library%d>", (int)t);
			break;
		}
	}

	static inline enum __type parse(const char *name) {
#define do_one(n)				\
		if (!strcmp(name, #n ) )	\
			return n;
		enum_library_function_templates(do_one);
#undef do_one
		return none;
	}

	static inline bool parse(enum __type *out, const char *str, const char **suffix) {
#define do_one(n)						\
		if (parseThisString(#n, str, suffix)) {		\
			*out = n;				\
			return true;				\
		}
		enum_library_function_templates(do_one);
#undef do_one
		return false;
	}
#undef enum_library_function_templates
};
typedef LibraryFunctionTemplate::__type LibraryFunctionType;

#endif /* !LIBRARY_HPP__ */
