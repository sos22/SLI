#! /usr/bin/env python

import sys

delta = float(sys.argv[1])

for i in sys.stdin.xreadlines():
    print float(i) - delta
