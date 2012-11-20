/* Simple parsing library */
#ifndef LIBVEX_PARSE_H__
#define LIBVEX_PARSE_H__

#include <vector>

bool parseThisChar(char c, const char *str, const char **suffix);
bool parseThisString(const char *pattern,
		     const char *str,
		     const char **suffix);
bool parseDecimalInt(int *out, const char *str, const char **suffix);
bool parseDecimalLong(long *out, const char *str, const char **suffix);
bool parseDecimalUInt(unsigned int *out, const char *str, const char **suffix);
bool parseHexUlong(unsigned long *out, const char *str, const char **suffix);

template <typename c> bool
parseContainer(c *out, bool (*parseItem)(typename c::value_type *out, const char *str, const char **suffix),
	       const char *str, const char **suffix)
{
	if (!parseThisChar('[', str, &str))
		return false;

	c res;
	while (1) {
		typename c::value_type x;
		if (!parseItem(&x, str, &str)) {
			if (parseThisChar(']', str, &str))
				break;
			return false;
		}
		res.push_back(x);
		if (!parseThisString(", ", str, &str)) {
			if (parseThisChar(']', str, &str))
				break;
			return false;
		}
	}

	*suffix = str;
	*out = res;
	return true;
}

#endif /* !LIBVEX_PARSE_H__ */
