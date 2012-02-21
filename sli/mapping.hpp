/* Simple-ish wrapper around a read-only mmap() */
#ifndef MAPPING_HPP__
#define MAPPING_HPP__

#include <sys/fcntl.h>
#include <sys/mman.h>
#include <unistd.h>

class Mapping {
	const void *content;
	off_t size;
public:
	Mapping() : content(NULL) {}
	int init(const char *path);
	~Mapping() { if (content) munmap((void *)content, size); }
	template <typename t> const t *get(off_t offset, int nr = 1) const;
	const void *window(off_t offset, size_t size);
	bool live() const { return content != NULL; }
};

template <typename t> const t *
Mapping::get(off_t offset, int nr) const
{
	if (offset < 0 || (off_t)(offset + sizeof(t) * nr) > size)
		return NULL;
	else
		return (const t *)((unsigned long)content + offset);
}

#endif /* !MAPPING_HPP__ */
