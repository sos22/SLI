#! /usr/bin/env python

import sys
import math

extra = sys.argv[1]
data = map(float, sys.stdin.xreadlines())
data.sort()

def percentile(n):
    idx = len(data) * n / 100.0
    if idx < 0 or idx >= len(data):
        raise "percentile out of range"
    # If it lands precisely on one of the buckets then get out the easy way.
    if idx == int(idx):
        return data[int(idx)]
    l_idx = int(idx)
    h_idx = l_idx + 1
    if h_idx == len(data):
        return data[l_idx]
    l = data[l_idx]
    h = data[h_idx]
    return l + (h - l) * (idx - l_idx)

def round(n):
    shift = int(math.log(n, 10))
    n += 0.5 * 10 ** (shift - 1)
    n -= n % (10 ** (shift - 1))
    return n

p10 = percentile(10)
p50 = percentile(50)
p90 = percentile(90)
p10 = round(p10)
p50 = round(p50)
p90 = round(p90)

print "$[%f; %f; %f]_{%d}$" % (p10, p50, p90, len(data))
