#! /usr/bin/env python

import sys
import random

samples = map(float, sys.stdin.xreadlines())

def generate_sample():
    res = [0] * 100
    for i in xrange(len(res)):
        res[i] = samples[random.randint(0,len(samples)-1)]
    return res

def estimate_p(samples):
    mean = sum(samples)/len(samples)
    return 1.0 / mean

while True:
    print estimate_p(generate_sample())
