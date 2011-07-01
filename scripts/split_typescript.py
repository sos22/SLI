#! /usr/bin/env python

import sys
import re

start = re.compile("^Considering ([0-9a-f]*)\.\.\.")
lines = sys.stdin.xreadlines()
try:
    # Skip to first block
    m = None
    while not m:
        l = lines.next()
        m = start.match(l)

    while True:
        addr = int(m.group(1), 16)
        print "Consider %x" % addr
        f = file("split_typescript/%x" % addr, "w")
        m = None
        while not m:
            f.write(l)
            l = lines.next()
            m = start.match(l)
except StopIteration:
    pass
    
