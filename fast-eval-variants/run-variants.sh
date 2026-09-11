#!/usr/bin/env bash
# Time every compiled evaluator variant over the benchmark suite in
# ../experiments, and report each variant's cost relative to the baseline.
#
#   ./run-variants.sh                  # all variants, all benchmarks
#   ./run-variants.sh -b fib,loop-sum  # only these benchmarks
#   ./run-variants.sh -r 5             # best of 5 runs (default 3)
#   ./run-variants.sh -v v00,v07       # only these variants
#
# Exit codes are the correctness check: every variant must agree with
# v00-baseline on every benchmark, or the row is flagged.
set -u

here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
root=$(dirname "$here")
bench=$root/experiments
export MCORE_LIBS="stdlib=$root/src/stdlib"

# The benchmarks in ../experiments are scaled for the three-evaluator suite,
# where `mi-boot` is 10-100x slower than these compiled variants and sets the
# ceiling.  Measured here, the shortest of them do only 40-120ms of work on top
# of a 5ms floor.  These overrides give those eight roughly 300ms each, so a
# few percent of difference between variants is still visible; everything else
# already does 150ms or more and keeps its own scale.
declare -A SCALE_OVERRIDE=(
  [mutual-rec]=7200000
  [mutual-rec-outer]=7200000
  [loop-sum]=8000000
  [env-lookup-shallow]=4500000
  [seq-set]=3600000
  [float-loop]=5000000
  [seq-index]=5000000
  [seq-fold]=3000000
)

reps=3
only_bench=""
only_var=""
timeout_s=${TIMEOUT:-300}

while getopts "r:b:v:t:h" opt; do
  case $opt in
    r) reps=$OPTARG ;;
    b) only_bench=$OPTARG ;;
    v) only_var=$OPTARG ;;
    t) timeout_s=$OPTARG ;;
    h) sed -n '2,12p' "$0"; exit 0 ;;
    *) exit 1 ;;
  esac
done

vars=()
for b in "$here"/bin/v*; do
  [ -x "$b" ] || continue
  n=$(basename "$b")
  if [ -n "$only_var" ]; then
    case ",$only_var," in *",${n%%-*},"*|*",$n,"*) ;; *) continue ;; esac
  fi
  vars+=("$n")
done
[ ${#vars[@]} -gt 0 ] || { echo "no compiled variants in $here/bin" >&2; exit 1; }

benches=()
for f in "$bench"/*.mc; do
  n=$(basename "$f" .mc)
  [ "$n" = noop ] && continue
  if [ -n "$only_bench" ]; then
    case ",$only_bench," in *",$n,"*) ;; *) continue ;; esac
  fi
  benches+=("$n")
done

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Materialize each benchmark, applying a scale override where there is one.
declare -A PROG SHOWN
for b in "${benches[@]}"; do
  src=$bench/$b.mc
  dst=$work/$b.mc
  if [ -n "${SCALE_OVERRIDE[$b]:-}" ]; then
    sed -E "s/^let scale = [0-9]+ in -- SCALE\$/let scale = ${SCALE_OVERRIDE[$b]} in -- SCALE/" "$src" > "$dst"
  else
    cp "$src" "$dst"
  fi
  PROG[$b]=$dst
  SHOWN[$b]=$(sed -nE 's/^let scale = ([0-9]+) in -- SCALE$/\1/p' "$dst")
  [ -n "${SHOWN[$b]}" ] || SHOWN[$b]="-"
done

# Times one run.  The command is deliberately NOT wrapped in `timeout`: the
# `timeout` on this system (uutils coreutils 0.8.0) rounds the child's elapsed
# time up to the next 100ms, which is larger than most of what this suite
# measures -- `timeout 60 /bin/true` reports 107ms for a 4ms command.  A
# background watchdog enforces the limit instead, running beside the child
# rather than between the clock reads.
best_of() {
  local n=$1; shift
  local best="" rc="" i t0 t1 ms pid wd
  for ((i = 0; i < n; i++)); do
    rm -f "$work/killed"
    t0=$(date +%s%N)
    "$@" >/dev/null 2>&1 &
    pid=$!
    { sleep "$timeout_s"; : > "$work/killed"; kill -9 "$pid"; } >/dev/null 2>&1 &
    wd=$!
    wait "$pid"; rc=$?
    t1=$(date +%s%N)
    kill "$wd" >/dev/null 2>&1; wait "$wd" >/dev/null 2>&1
    # A benchmark's own result can be 137, so the marker -- not the exit code --
    # is what says the watchdog fired.
    if [ "$rc" = 137 ] && [ -e "$work/killed" ]; then echo "- x"; return; fi
    ms=$(( (t1 - t0) / 1000000 ))
    if [ -z "$best" ] || [ "$ms" -lt "$best" ]; then best=$ms; fi
  done
  echo "$best $rc"
}

printf '%-20s%10s' benchmark scale
for v in "${vars[@]}"; do printf '%8s' "${v%%-*}"; done
printf '   check\n'
printf '%s\n' "$(printf '%.0s-' $(seq 1 $((30 + 8 * ${#vars[@]} + 10))))"

declare -A total
for v in "${vars[@]}"; do total[$v]=0; done
mismatch=""

for b in "${benches[@]}"; do
  printf '%-20s%10s' "$b" "${SHOWN[$b]}"
  ref=""
  bad=""
  for v in "${vars[@]}"; do
    read -r ms rc < <(best_of "$reps" "$here/bin/$v" "${PROG[$b]}")
    if [ "$ms" = "-" ]; then
      printf '%8s' "t/o"; bad="$bad $v"
      continue
    fi
    printf '%8s' "$ms"
    total[$v]=$(( ${total[$v]} + ms ))
    if [ -z "$ref" ]; then ref=$rc
    elif [ "$rc" != "$ref" ]; then bad="$bad $v"; fi
  done
  if [ -n "$bad" ]; then printf '   MISMATCH:%s\n' "$bad"; mismatch="yes"
  else printf '   ok (exit %s)\n' "$ref"; fi
done

printf '%s\n' "$(printf '%.0s-' $(seq 1 $((30 + 8 * ${#vars[@]} + 10))))"
printf '%-30s' "total ms"
for v in "${vars[@]}"; do printf '%8s' "${total[$v]}"; done
printf '\n'

base=${total[$(printf '%s\n' "${vars[@]}" | grep '^v00' | head -1)]:-0}
if [ "$base" -gt 0 ]; then
  printf '%-30s' "vs baseline"
  for v in "${vars[@]}"; do
    printf '%8s' "$(awk -v a="${total[$v]}" -v b="$base" 'BEGIN{printf "%.2fx", a/b}')"
  done
  printf '\n'
fi

[ -n "$mismatch" ] && echo && echo "WARNING: some variants disagree with the others" >&2
exit 0
