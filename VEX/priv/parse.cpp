/* Various bits of parsing gubbins */
#include <sys/types.h>
#include <errno.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include "libvex_parse.h"

bool parseThisChar(char c, const char *str, const char **suffix)
{
  if (str[0] == c) {
    *suffix = str + 1;
    return true;
  } else {
    return false;
  }
}

bool parseThisString(const char *pattern,
		     const char *str,
		     const char **suffix)
{
  size_t l = strlen(pattern);
  if (strlen(str) < l || memcmp(str, pattern, l))
    return false;
  *suffix = str + l;
  return true;
}

bool parseDecimalInt(int *out, const char *str, const char **suffix)
{
  long res;
  errno = 0;
  res = strtol(str, (char **)suffix, 10);
  *out = res;
  if (errno != 0 || *out != res || *suffix == str)
    return false;
  return true;
}

bool parseHexUlong(unsigned long *out, const char *str, const char **suffix)
{
  errno = 0;
  *out = strtoul(str, (char **)suffix, 16);
  return errno == 0 && *suffix != str;
}

