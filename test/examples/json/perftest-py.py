#!/usr/bin/env python3

import argparse
import json
import os
import time

N_RUNS = 10

parser = argparse.ArgumentParser()
parser.add_argument("file", type=os.path.realpath,
                    help="File to load contents from.")

args = parser.parse_args()

print("[Python JSON benchmark]");
print(f"loading file {args.file}...")
with open(args.file) as f:
    contents = f.read()

print(f"measuring over {N_RUNS} runs")
times = []
for i in range(N_RUNS):
    print(f"Run {i+1}/{N_RUNS}")
    t_start = time.time()
    obj = json.loads(contents)
    t_end = time.time()
    times.append((t_end - t_start) * 1000.0)

avg = sum(times) / len(times)
print(f"avg: {avg} ms | min: {min(times)} ms | max: {max(times)} ms")
