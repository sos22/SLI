#! /usr/bin/env python

import sys
import os

def read_sample(fname):
    f = file(fname, "r")
    res = {}
    for l in f:
        w = l.split()
        last = w[-1]
        rest = " ".join(w[:-1])[:-1]
        res[rest] = float(last)
    f.close()
    return (res["Total time"], res)

samples = [read_sample("%s/%s" % (sys.argv[1], i)) for i in os.listdir(sys.argv[1])]
samples.sort()
samples = [i[1] for i in samples]

heads = ["Total time",
         "Building probe machine",
         "Deriving R atomic",
         "Building store machine",
         "Deriving W atomic",
         "Deriving crash constraint",
         "Probe:CFGs",
         "Probe:Compile",
         "Probe:SSA",
         "Probe:Simplify",
         "Store:FindStores",
         "Store:CFGs",
         "Store:Compile",
         "Store:SSA",
         "Store:Simplify",
         "RAtomic:Build",
         "RAtomic:Simplify",
         "RAtomic:SymbExecute",
         "WAtomic:Build",
         "WAtomic:Simplify",
         "WAtomic:SymbExecute",
         "CC:Build",
         "CC:Simplify",
         "CC:SymbExecute",
         "Simplify:Total",
         "Simplify:Phi",
         "Simplify:Load",
         "Simplify:CDG",
         "Simplify:Avail",
         "Simplify:Avail:SSA",
         "Simplify:Avail:Base",
         "Simplify:DeadCode",
         "Simplify:Peephole",
         "BDD"]
transposed = {}
for h in heads:
    transposed[h] = []
f = file(sys.argv[2], "w")
f.write("Idx,%s\n" % ",".join(heads))
idx = 0
for i in samples:
    r = ",".join([("%f" % i[j]) for j in heads])
    f.write("%d,%s\n" % (idx, r))
    for h in heads:
        transposed[h].append(i[h])
    idx += 1
f.close()

for k in transposed.iterkeys():
    transposed[k].sort()

f = file(sys.argv[3], "w")
f.write(",".join(heads))
for i in xrange(idx):
    items = ",".join([("%f" % transposed[h][i]) for h in heads])
    f.write("%s\n" % items)
f.close()

