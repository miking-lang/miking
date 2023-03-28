#!/usr/bin/env python3

import argparse
import json
import random

MIN_SIZE = 1
CHARSET = ["\n", "\t"] + \
          [chr(c) for c in range(0x20,0x7F)]

def sizetype(v):
    v = int(v)
    if v < MIN_SIZE:
        raise ValueError(f"Minimum size is {MIN_SIZE}")
    return v

parser = argparse.ArgumentParser()
parser.add_argument("size", type=sizetype,
                    help="Number of elements to include in the blob.")
parser.add_argument("--seed", metavar="VALUE", dest="seed",
                    type=int, default=None,
                    help="Seed to use for the randomization.")

args = parser.parse_args()
if args.seed is not None:
    random.seed(args.seed)

state = {"remaining": args.size}

def random_string(minlen=1, maxlen=16):
    l = random.randint(minlen, maxlen)
    return "".join([random.choice(CHARSET) for _ in range(l)])

def gen():
    choice = random.choice(["object", "array", "int", "float", "bool", "null"])
    if choice == "object":
        obj = {}
        count = random.randint(0, state["remaining"])
        state["remaining"] -= count
        for _ in range(count):
            obj[random_string()] = gen()
        return obj
    elif choice == "array":
        arr = []
        count = random.randint(0, state["remaining"])
        state["remaining"] -= count
        for _ in range(count):
            arr.append(gen())
        return arr
    elif choice == "int":
        return random.randint(-(2**30), 2**30)
    elif choice == "float":
        return random.random()
    elif choice == "bool":
        return (random.randint(0,1) == 0)
    elif choice == "null":
        return None

items = []
while state["remaining"] > 0:
    state["remaining"] -= 1
    items.append(gen())

s = json.dumps(items)
print(s)
