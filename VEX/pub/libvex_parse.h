/* Simple parsing library */
#ifndef LIBVEX_PARSE_H__
#define LIBVEX_PARSE_H__

bool parseThisChar(char c, const char *str, const char **suffix, char **err);
bool parseThisString(const char *pattern,
		     const char *str,
		     const char **suffix,
		     char **err);
bool parseDecimalInt(int *out, const char *str, const char **suffix, char **err);
bool parseHexUlong(unsigned long *out, const char *str, const char **suffix,
		   char **err);

#endif /* !LIBVEX_PARSE_H__ */
