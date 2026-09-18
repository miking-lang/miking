#!/usr/bin/env python3
"""Pick a per-benchmark scale at which `mi eval --fast-eval` runs ~TARGET ms
net of its startup floor, so the compiled executable -- several times faster
again -- still lands far above its own ~5 ms floor.

Probes are timeout-protected and bracketed: benchmarks that scale exponentially
(ackermann doubles per +1 of scale, tak is steeper still) would otherwise be
sent to a scale that never returns.
"""
import math, os, pathlib, re, subprocess, sys, tempfile, time

ROOT  = pathlib.Path("/home/vipa/repositories/ai-sandbox/miking")
HERE  = ROOT / "experiments"
MI    = ROOT / "build" / "mi"
TARGET, LO, HI = 3000, 1800, 5500
PROBE_TIMEOUT  = 25.0
MAX_STEPS      = 12

env = dict(os.environ)
env["MCORE_LIBS"] = f"stdlib={ROOT/'src/stdlib'}"
env["OCAMLPATH"]  = f"{ROOT/'build/lib'}" + (":" + env["OCAMLPATH"] if env.get("OCAMLPATH") else "")

SCALE_RE = re.compile(r"^let scale = (\d+) in -- SCALE$", re.M)
work = pathlib.Path(tempfile.mkdtemp())

def time_ms(argv, timeout):
    """Best-effort wall time in ms; None if it blew the timeout."""
    t0 = time.monotonic()
    try:
        subprocess.run(argv, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       env=env, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    return int((time.monotonic() - t0) * 1000)

def floor_ms():
    best = None
    for _ in range(5):
        m = time_ms([str(MI), "eval", "--fast-eval", str(HERE / "noop.mc")], 60)
        if m is not None and (best is None or m < best):
            best = m
    return best

FLOOR = floor_ms()
print(f"# fast-eval floor: {FLOOR} ms", file=sys.stderr)

def probe(src_text, scale):
    p = work / "p.mc"
    p.write_text(SCALE_RE.sub(f"let scale = {scale} in -- SCALE", src_text))
    m = time_ms([str(MI), "eval", "--fast-eval", str(p)], PROBE_TIMEOUT)
    return None if m is None else max(m - FLOOR, 1)

results = {}
for f in sorted(HERE.glob("*.mc")):
    text = f.read_text()
    mt = SCALE_RE.search(text)
    if not mt:
        continue
    name = f.stem
    scale = int(mt.group(1))
    lo = hi = None          # lo: (scale, net) too fast; hi: scale too slow
    prev = None             # previous (scale, net), for the exponent fit
    best = scale
    seen = {}               # scale -> net, so a revisited scale costs nothing

    for step in range(MAX_STEPS):
        if scale in seen:
            net = seen[scale]
            tag = ("TIMEOUT" if net is None else f"net {net:6d} ms") + " (cached)"
        else:
            net = probe(text, scale)
            seen[scale] = net
            tag = "TIMEOUT" if net is None else f"net {net:6d} ms"
        print(f"{name:<20} step {step}  scale {scale:<12} {tag}", file=sys.stderr)

        # A steeply scaling benchmark can have no integer scale inside the
        # window -- ackermann doubles per +1, so it straddles it.  Once the
        # bracket is two adjacent integers, take whichever is closer to TARGET
        # in log space rather than oscillating between them.
        if lo is not None and hi is not None and hi - lo[0] <= 1:
            nlo = seen.get(lo[0])
            nhi = seen.get(hi)
            if nhi is None:
                best = lo[0]
            elif nlo is None:
                best = hi
            else:
                best = lo[0] if abs(math.log(TARGET / nlo)) <= abs(math.log(TARGET / nhi)) else hi
            print(f"{name:<20} bracket {lo[0]}/{hi} adjacent -> {best}", file=sys.stderr)
            break

        if net is None:
            hi = scale
            scale = int(math.sqrt(lo[0] * hi)) if lo else max(scale // 2, 1)
            if lo and scale <= lo[0]:
                scale = lo[0] + max(1, (hi - lo[0]) // 4)
            if hi - (lo[0] if lo else 0) <= 1:
                break
            continue

        if LO <= net <= HI:
            best = scale
            break

        if net < LO:
            best, lo, = scale, (scale, net)
            p = 1.0
            if prev and prev[0] != scale and prev[1] > 0:
                try:
                    p = math.log(net / prev[1]) / math.log(scale / prev[0])
                except (ValueError, ZeroDivisionError):
                    p = 1.0
            p = max(p, 0.3)
            f_ = min(max((TARGET / net) ** (1.0 / p), 1.15), 3.0)
            nxt = math.ceil(scale * f_)
            if hi is not None and nxt >= hi:
                nxt = max(scale + 1, int(math.sqrt(scale * hi)))
            if nxt == scale:
                nxt = scale + 1
        else:                                   # too slow
            hi = scale
            p = 1.0
            if prev and prev[0] != scale and prev[1] > 0:
                try:
                    p = math.log(net / prev[1]) / math.log(scale / prev[0])
                except (ValueError, ZeroDivisionError):
                    p = 1.0
            p = max(p, 0.3)
            f_ = max(min((TARGET / net) ** (1.0 / p), 0.87), 0.25)
            nxt = max(int(scale * f_), 1)
            if lo is not None and nxt <= lo[0]:
                nxt = max(lo[0] + 1, int(math.sqrt(lo[0] * scale)))
            if nxt == scale:
                nxt = scale - 1
            best = scale
        prev = (scale, net)
        scale = max(nxt, 1)

    results[name] = best
    print(f"{name} {best}", flush=True)

print("# done", file=sys.stderr)
