#! /usr/bin/env python

import sys
import math

low = float(sys.argv[1])
high = float(sys.argv[2])

range = high - low

s = math.log(range, 10)
shift = int(s)
if s != shift:
    shift -= 1
low += 0.5 * 10 **shift
high += 0.5 * 10 **shift
low -= low % (10 ** shift)
high -= high % (10 ** shift)
print "%.*f %.*f" % (-shift, low, -shift, high)
