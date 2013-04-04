#include <err.h>
#include <stdio.h>
#include "sli.h"

int
main(int argc, char *argv[])
{
	const char *outfile = argv[1];
	const char **inputs = (const char **)(argv + 2);
	int nr_inputs = argc - 2;

	std::map<unsigned long, std::set<unsigned long> > result;
	for (int i = 0; i < nr_inputs; i++) {
		FILE *f = fopen(inputs[i], "r");
		if (!f) {
			err(1, "opening %s", inputs[i]);
		}
		unsigned long magic;
		if (fread(&magic, sizeof(magic), 1, f) != 1) {
			err(1, "reading head of %s", inputs[i]);
		}
		if (magic != 0xaabbccddeeff) {
			errx(1, "%s is missing the magic number", inputs[i]);
		}
		while (1) {
			unsigned long src;
			if (fread(&src, sizeof(src), 1, f) != 1) {
				if (feof(f)) {
					break;
				}
				err(1, "reading %s", inputs[i]);
			}
			unsigned nr_entries;
			if (fread(&nr_entries, sizeof(nr_entries), 1, f) != 1) {
				if (feof(f)) {
					errx(1, "%s truncated?", inputs[i]);
				} else {
					err(1, "reading %s", inputs[i]);
				}
			}
			unsigned long content[nr_entries];
			if (fread(content, sizeof(content[0]), nr_entries, f) != nr_entries) {
				if (feof(f)) {
					errx(1, "%s truncated?", inputs[i]);
				} else {
					err(1, "reading %s", inputs[i]);
				}
			}
			std::set<unsigned long> &s(result[src]);
			for (unsigned i = 0; i < nr_entries; i++) {
				s.insert(content[i]);
			}
		}
		fclose(f);
		size_t nr_entries = 0;
		for (auto it = result.begin(); it != result.end(); it++) {
			nr_entries += it->second.size();
		}
		printf("Processed %s.  Database has %zx sources, %zd edges\n",
		       inputs[i], result.size(), nr_entries);
	}

	/* And now write it out */
	FILE *f = fopen(outfile, "w");
	if (!f) {
		err(1, "opening %s", outfile);
	}
	unsigned long magic = 0xaabbccddeeff;
	if (fwrite(&magic, sizeof(magic), 1, f) != 1) {
		err(1, "writing header to %s", outfile);
	}
	for (auto it = result.begin(); it != result.end(); it++) {
		unsigned long src = it->first;
		unsigned nr_entries = it->second.size();
		unsigned long content[nr_entries];
		unsigned long *cursor = content;
		for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
			*(cursor++) = *it2;
		}
		if (fwrite(&src, sizeof(src), 1, f) != 1 ||
		    fwrite(&nr_entries, sizeof(nr_entries), 1, f) != 1 ||
		    fwrite(content, sizeof(content[0]), nr_entries, f) != nr_entries) {
			err(1, "writing %s", outfile);
		}
	}
	if (fclose(f) == EOF) {
		err(1, "flushing %s", outfile);
	}
	return 0;
}

