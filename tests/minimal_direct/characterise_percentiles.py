#! /usr/bin/env python

import sys

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
    l = data[l_idx]
    h = data[h_idx]
    return l + (h - l) * (idx - l_idx)

print "$[%f; %f; %f]_{%d}$" % (percentile(10), percentile(50), percentile(90), len(data))
