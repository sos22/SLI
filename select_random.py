#! /usr/bin/env python

import sys
import random

lines = sys.stdin.readlines()
random.shuffle(lines)
for x in lines[0:int(sys.argv[1])]:
    print x,
