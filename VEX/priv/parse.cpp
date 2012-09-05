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
#include "libvex_ir.h"

bool parseThisChar(char c, const char *str, const char **suffix)
{
  if (isspace(c)) {
    if (!isspace(str[0]))
      return false;
    while (isspace(str[0]))
      str++;
    *suffix = str;
    return true;
  }
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
  while (*pattern) {
    if (isspace(*pattern)) {
      while (isspace(*pattern))
	pattern++;
      if (!isspace(*str))
	return false;
      while (isspace(*str))
	str++;
      continue;
    }
    if (*pattern != *str)
      return false;
    pattern++;
    str++;
  }
  *suffix = str;
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

bool parseDecimalUInt(unsigned *out, const char *str, const char **suffix)
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
  if (errno != 0 || *suffix == str)
    return false;
  return true;
}

bool parseThreadRip(ThreadRip *out, const char *str, const char **suffix)
{
  int tid;
  VexRip rip;
  if (!parseDecimalInt(&tid, str, &str) ||
      !parseThisChar(':', str, &str) ||
      !parseVexRip(&rip, str, suffix)) {
    return false;
  }
  out->thread = tid;
  out->rip = rip;
  return true;
}

bool parseVexRip(VexRip *out, const char *str, const char **suffix)
{
  if (!parseThisChar('{', str, &str))
    return false;
  out->stack.clear();
  while (1) {
    if (parseThisChar('}', str, suffix))
      return true;
    unsigned long v;
    if (!parseHexUlong(&v, str, &str))
      return false;
    out->stack.push_back(v);
    parseThisString(", ", str, &str);
  }
}

bool
MemoryAccessIdentifier::parse(const char *str,
			      const char **suffix)
{
	int tid, id;
	if (!parseThisString("mai", str, &str) ||
	    !parseDecimalInt(&tid, str, &str) ||
	    !parseThisChar(':', str, &str) ||
	    !parseDecimalInt(&id, str, suffix))
		return false;
	tid = tid;
	id = id;
	clearName();
	return true;
}

bool
CfgLabel::parse(const char *str, const char **suffix)
{
	return parseThisString("cfg", str, &str) &&
		parseDecimalInt(&label, str, suffix);
}
