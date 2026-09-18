#!/usr/bin/env bash
# Run the MCore micro-benchmarks under the three evaluators and the native
# compiler, and report timings.
#
#   ./run.sh                          # floors, then both tables
#   ./run.sh fib loop-sum             # only these benchmarks
#   ./run.sh -s 20 fib                # override the SCALE parameter
#   ./run.sh -r 5 -e fast,comp fib    # 5 repetitions, only some backends
#   ./run.sh -p floors                # just the startup floors
#   ./run.sh -p main                  # just the four-backend table
#   ./run.sh -p high                  # just the raised-scale head-to-head
#
# Three passes, each of which can be selected with -p:
#
#   floors  what every backend costs before it evaluates anything, measured
#           with noop.mc.  These differ by an order of magnitude, so they are
#           reported up front rather than buried: `mi` loads and type checks a
#           self-hosted front end, `mi-boot` does not, and a compiled
#           executable does no front-end work at all.
#   main    every benchmark under all four backends at the suite's default
#           scales.  Those scales are set by the *slowest* backend, so the
#           compiled column here often sits near its own floor -- that is the
#           point of the third pass, not a defect of this one.
#   high    `--fast-eval` against compiled code only, at per-benchmark scales
#           raised until `--fast-eval` runs for a few seconds.  This is where
#           the gap between the fast evaluator and native code can actually be
#           read off, since both backends are then far above their floors.
#
# Each benchmark reports the *best* wall-clock time of `-r` runs.  Exit codes
# are used as a checksum: the backends must agree, otherwise the row is
# flagged with `MISMATCH`.
set -u

here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
root=$(dirname "$here")

MI=${MI:-$root/build/mi}
MI_BOOT=${MI_BOOT:-$root/build/mi-boot}
export MCORE_LIBS="stdlib=$root/src/stdlib"
# `mi compile` shells out to ocamlfind, which has to find boot's OCaml library
# in build/lib.  Without this every compile fails with "Package `boot' not
# found" -- the evaluators do not need it, so it is easy to miss.
export OCAMLPATH="$root/build/lib${OCAMLPATH:+:$OCAMLPATH}"

# Scales for the `high` pass, chosen so that `--fast-eval` runs for roughly
# three seconds net of its floor.  Compiled code is several times faster again,
# which still leaves it far above its own ~5 ms floor.  Regenerate these with
# ./calibrate.py if the evaluator's performance changes materially.
declare -A HIGH=(
  [ackermann]=10
  [bitcount]=1800000
  [church-list]=600000
  [closures]=12000
  [collatz]=512821
  [deep-rec]=1500000
  # The compiled side of this one sits ~3 ms above its floor at the scale
  # calibrate.py picks, because the gap here is the widest in the suite.
  # Raised until compiled clears the floor, at the cost of a slower row.
  [env-lookup-deep]=40500000
  [env-lookup-shallow]=40500000
  [fib]=37
  [float-loop]=48669473
  [float-mandel]=960
  [float-points]=7200000
  [loop-sum]=54000000
  [mutual-rec-outer]=68292076
  [mutual-rec]=76896963
  [nested-loops]=6000
  [primes]=1396529
  [records]=6300000
  [seq-build]=3600000
  [seq-fold]=27000000
  [seq-index]=47012393
  [seq-map]=5400000
  [seq-pattern]=11189222
  [seq-set]=32400000
  [seq-sort]=223436
  [strings]=10800000
  [tak]=10
  [tuples]=6300000
)

floors_from_row=0
reps=3
scale=""
evals="fast,eval,boot,comp"
passes="floors,main,high"
timeout_s=${TIMEOUT:-600}

while getopts "r:s:e:p:t:h" opt; do
  case $opt in
    r) reps=$OPTARG ;;
    s) scale=$OPTARG ;;
    e) evals=$OPTARG ;;
    p) passes=$OPTARG ;;
    t) timeout_s=$OPTARG ;;
    h) sed -n '2,32p' "$0"; exit 0 ;;
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

# Builds a native executable once, outside the timing loop, and echoes how long
# the build took.  The compiled row measures only the executable, so `cc` is
# reported in its own column rather than folded into it.
compile_prog() {
  local src=$1 out=$2 t0 t1 rc
  t0=$(date +%s%N)
  "$MI" compile "$src" --output "$out" >/dev/null 2>"$work/cerr"
  rc=$?
  t1=$(date +%s%N)
  echo "$(( (t1 - t0) / 1000000 )) $rc"
}

# Writes $here/$1.mc into $work/$1.mc, rewriting the SCALE line to $2 when $2
# is non-empty, and echoes the scale the program ended up with.
stage() {
  local b=$1 sc=$2 src=$here/$1.mc out=$work/$1.mc shown
  if [ -n "$sc" ]; then
    sed -E "s/^let scale = [0-9]+ in -- SCALE\$/let scale = $sc in -- SCALE/" "$src" > "$out"
  else
    cp "$src" "$out"
  fi
  shown=$(sed -nE 's/^let scale = ([0-9]+) in -- SCALE$/\1/p' "$out")
  echo "${shown:--}"
}

fmt() {
  if [ "$1" = skip ] || [ "$1" = timeout ] || [ "$1" = cc-fail ] || [ "$1" = "-" ]
  then printf '%14s' "$1"; else printf '%11s ms' "$1"; fi
}

# --- floors ----------------------------------------------------------------
# Measured unconditionally: the `high` pass reports net times, which need them.

declare -A floor
stage noop "" >/dev/null   # writes $work/noop.mc; the echoed value is the scale

# Warm the page cache before timing anything.  `mi` is a ~17 MB executable and
# the floors pass is the first thing that touches it, so without this it
# measures the cold fault-in and reports roughly double the steady-state floor
# -- which then gets subtracted from every net figure in the suite.
for _ in 1 2; do
  "$MI" eval --fast-eval "$work/noop.mc" >/dev/null 2>&1
  "$MI" eval "$work/noop.mc"             >/dev/null 2>&1
  "$MI_BOOT" eval "$work/noop.mc"        >/dev/null 2>&1
done

read -r floor[fast] _ < <(best_of "$reps" "$MI" eval --fast-eval "$work/noop.mc")
read -r floor[eval] _ < <(best_of "$reps" "$MI" eval "$work/noop.mc")
read -r floor[boot] _ < <(best_of "$reps" "$MI_BOOT" eval "$work/noop.mc")
read -r floor_cc ccrc < <(compile_prog "$work/noop.mc" "$work/noop.bin")
if [ "$ccrc" = 0 ]; then read -r floor[comp] _ < <(best_of "$reps" "$work/noop.bin")
else floor[comp]="cc-fail"; fi

net() {  # $1 = measured ms, $2 = backend key
  local m=$1 f=${floor[$2]}
  case "$m" in ''|*[!0-9]*) echo "$m"; return;; esac
  case "$f" in ''|*[!0-9]*) echo "$m"; return;; esac
  local n=$(( m - f )); [ "$n" -lt 0 ] && n=0
  echo "$n"
}

case ",$passes," in *,floors,*)
  echo "Startup floors -- noop.mc, best of $reps, nothing to evaluate"
  printf '%s\n' "-------------------------------------------------------------"
  printf '  %-24s %11s ms\n' "mi eval --fast-eval" "${floor[fast]}"
  printf '  %-24s %11s ms\n' "mi eval"             "${floor[eval]}"
  printf '  %-24s %11s ms\n' "mi-boot eval"        "${floor[boot]}"
  printf '  %-24s %11s ms   (cc %s ms)\n' "compiled executable" "${floor[comp]}" "$floor_cc"
  echo
  echo "  Measured on their own these read high: under the sustained load of a full"
  echo "  suite the CPU holds a higher clock and the caches stay hot, so the noop"
  echo "  row of the main pass comes in nearer 30ms.  That row, not this one, is"
  echo "  what the net figures subtract when the main pass runs."
  echo
  echo "  mi loads, symbolizes and type checks a self-hosted front end before it"
  echo "  evaluates anything; mi-boot has no such front end, and the compiled"
  echo "  executable does no front-end work at all.  Every net figure below"
  echo "  subtracts the backend's own floor, not one number for all four."
  echo
;; esac

# --- main pass -------------------------------------------------------------

case ",$passes," in *,main,*)
  echo "All backends, default scales -- best of $reps, startup included"
  printf '%-20s %6s %14s %14s %14s %14s %9s   %s\n' \
    benchmark scale "mi --fast-eval" "mi eval" "mi-boot eval" "mi compile" cc check
  printf '%s\n' "-------------------------------------------------------------------------------------------------------------------"

  for b in "${benches[@]}"; do
    [ -f "$here/$b.mc" ] || { echo "no such benchmark: $b" >&2; continue; }
    shown=$(stage "$b" "$scale")
    prog=$work/$b.mc

    declare -A ms rcs
    for e in fast eval boot comp; do ms[$e]="skip"; rcs[$e]=""; done
    cc="-"
    case ",$evals," in *,fast,*) read -r ms[fast] rcs[fast] < <(best_of "$reps" "$MI" eval --fast-eval "$prog");; esac
    case ",$evals," in *,eval,*) read -r ms[eval] rcs[eval] < <(best_of "$reps" "$MI" eval "$prog");; esac
    case ",$evals," in *,boot,*) read -r ms[boot] rcs[boot] < <(best_of "$reps" "$MI_BOOT" eval "$prog");; esac
    case ",$evals," in
      *,comp,*)
        read -r cc crc < <(compile_prog "$prog" "$work/$b.bin")
        if [ "$crc" != 0 ]; then
          ms[comp]="cc-fail"; rcs[comp]=""
          echo "compile failed for $b:" >&2; sed -n '1,5p' "$work/cerr" >&2
        else
          read -r ms[comp] rcs[comp] < <(best_of "$reps" "$work/$b.bin")
        fi
        ;;
    esac

    check="ok"; seen=""
    for e in fast eval boot comp; do
      r=${rcs[$e]}
      [ -z "$r" ] || [ "$r" = "-" ] && continue
      if [ -z "$seen" ]; then seen=$r
      elif [ "$seen" != "$r" ]; then check="MISMATCH"; fi
    done
    [ "$check" = ok ] && check="ok (exit $seen)"

    # noop is the floor measured under the same conditions as every other row.
    # A floor measured on its own reads high: under the sustained load of a full
    # suite the CPU holds a higher clock and the caches stay hot, so mid-suite
    # noop comes in around 30ms where an isolated measurement of the very same
    # thing gives 40-47ms.  Prefer this one for the net figures.
    if [ "$b" = noop ]; then
      for e in fast eval boot comp; do
        case "${ms[$e]}" in ''|*[!0-9]*) ;; *) floor[$e]=${ms[$e]} ;; esac
      done
      floors_from_row=1
    fi

    printf '%-20s %6s ' "$b" "$shown"
    fmt "${ms[fast]}"; fmt "${ms[eval]}"; fmt "${ms[boot]}"; fmt "${ms[comp]}"
    if [ "$cc" = "-" ]; then printf '%9s' "-"; else printf '%6s ms' "$cc"; fi
    printf '   %s\n' "$check"
  done
  echo
;; esac

# --- high pass -------------------------------------------------------------

case ",$passes," in *,high,*)
  echo "--fast-eval vs compiled, raised scales -- best of $reps, startup included"
  if [ "$floors_from_row" = 1 ]; then src="the noop row of this run"; else src="the floors pass"; fi
  echo "(ratio is net of each backend's floor, ${floor[fast]}ms and ${floor[comp]}ms, from $src)"
  printf '%-20s %12s %14s %14s %9s %9s   %s\n' \
    benchmark scale "--fast-eval" "compiled" cc ratio check
  printf '%s\n' "-------------------------------------------------------------------------------------------------"

  for b in "${benches[@]}"; do
    [ -f "$here/$b.mc" ] || continue
    hs=${HIGH[$b]:-}
    [ -n "$hs" ] || continue
    shown=$(stage "$b" "$hs")
    prog=$work/$b.mc

    read -r hfast hfrc < <(best_of "$reps" "$MI" eval --fast-eval "$prog")
    read -r cc crc < <(compile_prog "$prog" "$work/$b.bin")
    if [ "$crc" != 0 ]; then
      hcomp="cc-fail"; hcrc=""
      echo "compile failed for $b:" >&2; sed -n '1,5p' "$work/cerr" >&2
    else
      read -r hcomp hcrc < <(best_of "$reps" "$work/$b.bin")
    fi

    nf=$(net "$hfast" fast); nc=$(net "$hcomp" comp)
    ratio="-"
    case "$nf$nc" in
      *[!0-9]*) ;;
      *) [ "$nc" -gt 0 ] && ratio=$(python3 -c "print(f'{$nf/$nc:.1f}x')") ;;
    esac

    check="ok"
    if [ -n "$hfrc" ] && [ -n "$hcrc" ] && [ "$hfrc" != "$hcrc" ]; then check="MISMATCH"
    else check="ok (exit ${hfrc:-?})"; fi

    printf '%-20s %12s ' "$b" "$shown"
    fmt "$hfast"; fmt "$hcomp"
    if [ "$crc" != 0 ]; then printf '%9s' "-"; else printf '%6s ms' "$cc"; fi
    printf ' %9s   %s\n' "$ratio" "$check"
  done
;; esac
