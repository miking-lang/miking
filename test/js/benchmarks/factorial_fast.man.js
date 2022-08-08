const { repeat } = require("./benchmarkcommon");

// let rec fact n = if n = 0 then 1 else n * fact (n - 1)
// let _ = Benchmarkcommon.repeat (fun () -> fact 100)

function fact(n, acc) {
  if (n === 0) return acc;
  else return fact(n - 1, n * acc);
}

repeat(() => fact(100, 1));
