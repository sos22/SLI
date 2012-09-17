#include "mapping.hpp"

int
Mapping::init(const char *path)
{
	int fd = open(path, O_RDONLY);
	if (fd < 0)
		return -1;
	size = lseek(fd, 0, SEEK_END);
	if (size < 0) {
		close(fd);
		return -1;
	}
	content = mmap(NULL, (size + 4095) & ~4095ul, PROT_READ, MAP_SHARED,
		       fd, 0);
	close(fd);
	if (content == MAP_FAILED) {
		content = NULL;
		return -1;
	}
	return 0;
}

const void *
Mapping::window(off_t offset, size_t sz)
{
	if (offset < 0 || (off_t)(offset + sz) > size)
		return NULL;
	else
		return (const void *)((unsigned long)content + offset);
}
