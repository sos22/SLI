#ifndef __LIBVEX_PRINT_H
#define __LIBVEX_PRINT_H

#include <stdio.h>

class PrettyPrintable {
public:
	virtual void prettyPrint(FILE *f) const = 0;
};

#endif /* !__LIBVEX_PRINT_H */
