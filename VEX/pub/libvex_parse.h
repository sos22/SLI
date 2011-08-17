/* Simple parsing library */
#ifndef LIBVEX_PARSE_H__
#define LIBVEX_PARSE_H__

#include <vector>

bool parseThisChar(char c, const char *str, const char **suffix, char **err);
bool parseThisString(const char *pattern,
		     const char *str,
		     const char **suffix,
		     char **err);
bool parseDecimalInt(int *out, const char *str, const char **suffix, char **err);
bool parseHexUlong(unsigned long *out, const char *str, const char **suffix,
		   char **err);

template <typename c> bool
parseContainer(c *out, bool (*parseItem)(typename c::value_type *out, const char *str, const char **suffix, char **err),
	       const char *str, const char **suffix, char **err)
{
	if (!parseThisChar('[', str, &str, err))
		return false;

	c res;
	while (1) {
		typename c::value_type x;
		if (!parseItem(&x, str, &str, err)) {
			if (parseThisChar(']', str, &str, err))
				break;
			return false;
		}
		res.push_back(x);
		if (!parseThisString(", ", str, &str, err)) {
			if (parseThisChar(']', str, &str, err))
				break;
			return false;
		}
	}

	*suffix = str;
	*out = res;
	return true;
}

#endif /* !LIBVEX_PARSE_H__ */
