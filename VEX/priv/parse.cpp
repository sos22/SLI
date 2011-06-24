/* Various bits of parsing gubbins */
#include <sys/types.h>
#include <ctype.h>
#include <errno.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include "libvex_parse.h"
#include "libvex_alloc.h"

bool parseThisChar(char c, const char *str, const char **suffix,
		   char **err)
{
  if (isspace(c)) {
    if (!isspace(str[0])) {
      *err = vex_asprintf("wanted whitespace, got %c", str[0]);
      return false;
    }
    while (isspace(str[0]))
      str++;
    *suffix = str;
    return true;
  }
  if (str[0] == c) {
    *suffix = str + 1;
    return true;
  } else {
    *err = vex_asprintf("wanted %c, got %c", c, str[0]);
    return false;
  }
}

bool parseThisString(const char *pattern,
		     const char *str,
		     const char **suffix,
		     char **err)
{
  while (*pattern) {
    if (isspace(*pattern)) {
      while (isspace(*pattern))
	pattern++;
      if (!isspace(*str)) {
	*err = vex_asprintf("wanted space in pattern %s, got %.10s", pattern, str);
	return false;
      }
      while (isspace(*str))
	str++;
      continue;
    }
    if (*pattern != *str) {
      *err = vex_asprintf("wanted %s, got %.10s", pattern, str);
      return false;
    }
    pattern++;
    str++;
  }
  *suffix = str;
  return true;
}

bool parseDecimalInt(int *out, const char *str, const char **suffix, char **err)
{
  long res;
  errno = 0;
  res = strtol(str, (char **)suffix, 10);
  *out = res;
  if (errno != 0 || *out != res || *suffix == str) {
    *err = vex_asprintf("wanted decimal int, got %.10s", str);
    return false;
  }
  return true;
}

bool parseHexUlong(unsigned long *out, const char *str, const char **suffix, char **err)
{
  errno = 0;
  *out = strtoul(str, (char **)suffix, 16);
  if (errno != 0 || *suffix == str) {
    *err = vex_asprintf("wanted hex ulong, got %.10s", str);
    return false;
  }
  return true;
}

