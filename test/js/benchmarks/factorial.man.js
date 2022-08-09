const { repeat } = require("./benchmarkcommon");

// let rec fact n = if n = 0 then 1 else n * fact (n - 1)
// let _ = Benchmarkcommon.repeat (fun () -> fact 100)

function fact(n) {
  if (n === 0) return 1;
  else return n * fact(n - 1);
}

repeat(() => fact(1000));
