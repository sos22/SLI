#! /usr/bin/env python

import sys
import random

lines = sys.stdin.readlines()
random.shuffle(lines)
for l in lines:
    print l,
