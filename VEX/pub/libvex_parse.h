/* Simple parsing library */
#ifndef LIBVEX_PARSE_H__
#define LIBVEX_PARSE_H__

bool parseThisChar(char c, const char *str, const char **suffix);
bool parseThisString(const char *pattern,
		     const char *str,
		     const char **suffix);
bool parseDecimalInt(int *out, const char *str, const char **suffix);
bool parseHexUlong(unsigned long *out, const char *str, const char **suffix);

#endif /* !LIBVEX_PARSE_H__ */
