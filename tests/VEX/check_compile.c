/* Very simple thing to make sure that VEX is compelte.  Doesn't do
   anything useful when run. */
#include <stddef.h>
#include "libvex.h"

int
main()
{
	LibVEX_default_VexArchInfo(NULL);
	LibVEX_default_VexAbiInfo(NULL);
	LibVEX_default_VexControl(NULL);
	LibVEX_ShowAllocStats();

	LibVEX_Init(NULL, NULL, 0, 0, NULL);

	LibVEX_Translate(NULL);

	return 0;
}
