#include <stdlib.h>
#include <assert.h>

#include "nd_chooser.h"

static void
test1(void)
{
	NdChooser chooser;
	std::vector<int> output;

	do {
		switch (chooser.nd_choice(3)) {
		case 0:
			switch (chooser.nd_choice(5)) {
			case 0:
				output.push_back(1);
				break;
			case 1:
				switch (chooser.nd_choice(1)) {
				case 0:
					output.push_back(2);
					break;
				default:
					abort();
				}
				break;
			case 2:
				switch (chooser.nd_choice(2)) {
				case 0:
					output.push_back(3);
					break;
				case 1:
					output.push_back(4);
					break;
				default:
					abort();
				}
				break;
			case 3:
				output.push_back(5);
				break;
			case 4:
				output.push_back(6);
				break;
			default:
				abort();
			}
			break;
		case 1:
			output.push_back(7);
			break;
		case 2:
			switch (chooser.nd_choice(2)) {
			case 0:
				switch (chooser.nd_choice(2)) {
				case 0:
					output.push_back(8);
					break;
				case 1:
					output.push_back(9);
					break;
				default:
					abort();
				}
				break;
			case 1:
				output.push_back(10);
				break;
			default:
				abort();
			}
			break;
		default:
			abort();
		}
	} while (chooser.advance());

	assert(output.size() == 10);
	for (int x = 0; x < 10; x++)
		assert(output[x] == x + 1);
}

int
main()
{
	test1();
	return 0;
}
