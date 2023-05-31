-- perftest-mc.mc

include "common.mc"
include "json.mc"
include "math.mc"

let n_runs = 10

mexpr
let file = get argv 1 in
printLn "[MCore JSON benchmark]";
printLn (join ["loading file ", file, "..."]);

let contents: String = readFile file in

printLn (join ["measuring over ", int2string n_runs, " runs"]);

recursive let measure = lam times. lam i.
  if eqi i n_runs then (
  	times
  ) else (
  	printLn (join ["Run ", int2string (addi i 1), "/", int2string n_runs]);
  	let t_start = wallTimeMs () in
  	let obj = jsonParseExn contents in
  	let t_end = wallTimeMs () in
  	let acc = snoc times (subf t_end t_start) in
  	measure acc (addi i 1)
  )
in

let times = measure [] 0 in

let avg = divf (foldl addf 0.0 times) (int2float (length times)) in
let min = foldl minf (head times) (tail times) in
let max = foldl maxf (head times) (tail times) in

printLn (join ["avg: ", float2string avg, " ms | min: ", float2string min, " ms | max: ", float2string max, " ms"]);

()
