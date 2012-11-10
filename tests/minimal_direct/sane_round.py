#! /usr/bin/env python

import sys
import math

mu = float(sys.argv[1])
sigma = float(sys.argv[2])

s = math.log(sigma, 10)
shift = int(s)
if s != shift:
    shift -= 1
if int(sigma * 10**(-shift)) >= 5:
    shift += 1
mu += 0.5 * 10 **shift
sigma += 0.5 * 10 **shift
mu -= mu % (10 ** shift)
sigma -= sigma % (10 ** shift)
print "%f %f" % (mu, sigma)
