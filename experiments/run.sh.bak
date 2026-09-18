#!/usr/bin/env bash
# Run the MCore micro-benchmarks under the three evaluators and report timings.
#
#   ./run.sh                          # every benchmark, default scales
#   ./run.sh fib loop-sum             # only these benchmarks
#   ./run.sh -s 20 fib                # override the SCALE parameter
#   ./run.sh -r 5 -e fast,boot fib    # 5 repetitions, only some evaluators
#
# Each benchmark reports the *best* wall-clock time of `-r` runs.  Exit codes
# are used as a checksum: the evaluators must agree, otherwise the row is
# flagged with `MISMATCH`.
set -u

here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
root=$(dirname "$here")

MI=${MI:-$root/build/mi}
MI_BOOT=${MI_BOOT:-$root/build/mi-boot}
export MCORE_LIBS="stdlib=$root/src/stdlib"

reps=3
scale=""
evals="fast,eval,boot"
timeout_s=${TIMEOUT:-600}

while getopts "r:s:e:t:h" opt; do
  case $opt in
    r) reps=$OPTARG ;;
    s) scale=$OPTARG ;;
    e) evals=$OPTARG ;;
    t) timeout_s=$OPTARG ;;
    h) sed -n '2,10p' "$0"; exit 0 ;;
    *) exit 1 ;;
  esac
done
shift $((OPTIND - 1))

if [ $# -gt 0 ]; then
  benches=("$@")
else
  benches=()
  for f in "$here"/*.mc; do benches+=("$(basename "$f" .mc)"); done
fi

for tool in "$MI" "$MI_BOOT"; do
  [ -x "$tool" ] || { echo "missing executable: $tool" >&2; exit 1; }
done

case ",$evals," in
  *,fast,*)
    if "$MI" eval --fast-eval "$here/noop.mc" 2>&1 | grep -q 'Unknown option'; then
      echo "$MI does not know --fast-eval; rebuild it (make, or make cheat)," >&2
      echo "or point MI= at one that does." >&2
      exit 1
    fi
    ;;
esac

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Times one run.  The command is deliberately NOT wrapped in `timeout`: the
# `timeout` on this system (uutils coreutils 0.8.0) rounds the child's elapsed
# time up to the next 100ms, which is larger than most of what this suite
# measures -- `timeout 60 /bin/true` reports 107ms for a 4ms command.  A
# background watchdog enforces the limit instead, running beside the child
# rather than between the clock reads.
run_once() {
  local t0 t1 rc pid wd
  rm -f "$work/killed"
  t0=$(date +%s%N)
  "$@" >/dev/null 2>"$work/err" &
  pid=$!
  { sleep "$timeout_s"; : > "$work/killed"; kill -9 "$pid"; } >/dev/null 2>&1 &
  wd=$!
  wait "$pid"; rc=$?
  t1=$(date +%s%N)
  kill "$wd" >/dev/null 2>&1; wait "$wd" >/dev/null 2>&1
  # A benchmark's own result can be 137, so the marker -- not the exit code --
  # is what says the watchdog fired.
  if [ "$rc" = 137 ] && [ -e "$work/killed" ]; then rc=124; fi
  echo "$(( (t1 - t0) / 1000000 )) $rc"
}

best_of() {
  local n=$1; shift
  local best="" rc="" i out ms r
  for ((i = 0; i < n; i++)); do
    out=$(run_once "$@")
    ms=${out% *}; r=${out#* }
    if [ "$r" = 124 ]; then echo "timeout -"; return; fi
    if [ -z "$best" ] || [ "$ms" -lt "$best" ]; then best=$ms; fi
    rc=$r
  done
  echo "$best $rc"
}

label_fast="mi --fast-eval"
label_eval="mi eval"
label_boot="mi-boot eval"

printf '%-20s %6s %14s %14s %14s   %s\n' \
  benchmark scale "$label_fast" "$label_eval" "$label_boot" check
printf '%s\n' "--------------------------------------------------------------------------------------------"

for b in "${benches[@]}"; do
  src=$here/$b.mc
  [ -f "$src" ] || { echo "no such benchmark: $b" >&2; continue; }

  prog=$work/$b.mc
  if [ -n "$scale" ]; then
    sed -E "s/^let scale = [0-9]+ in -- SCALE\$/let scale = $scale in -- SCALE/" "$src" > "$prog"
  else
    cp "$src" "$prog"
  fi
  shown=$(sed -nE 's/^let scale = ([0-9]+) in -- SCALE$/\1/p' "$prog")
  [ -n "$shown" ] || shown="-"

  declare -A ms rcs
  for e in fast eval boot; do ms[$e]="skip"; rcs[$e]=""; done
  case ",$evals," in *,fast,*) read -r ms[fast] rcs[fast] < <(best_of "$reps" "$MI" eval --fast-eval "$prog");; esac
  case ",$evals," in *,eval,*) read -r ms[eval] rcs[eval] < <(best_of "$reps" "$MI" eval "$prog");; esac
  case ",$evals," in *,boot,*) read -r ms[boot] rcs[boot] < <(best_of "$reps" "$MI_BOOT" eval "$prog");; esac

  check="ok"
  seen=""
  for e in fast eval boot; do
    r=${rcs[$e]}
    [ -z "$r" ] || [ "$r" = "-" ] && continue
    if [ -z "$seen" ]; then seen=$r
    elif [ "$seen" != "$r" ]; then check="MISMATCH"; fi
  done
  [ "$check" = ok ] && check="ok (exit $seen)"

  fmt() { if [ "$1" = skip ] || [ "$1" = timeout ]; then printf '%14s' "$1"; else printf '%11s ms' "$1"; fi; }
  printf '%-20s %6s ' "$b" "$shown"
  fmt "${ms[fast]}"; fmt "${ms[eval]}"; fmt "${ms[boot]}"
  printf '   %s\n' "$check"
done
