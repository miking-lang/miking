const { repeat, utest } = require("./benchmarkcommon");

function fact(n, acc) {
  if (n === 0) return acc;
  else return fact(n - 1, n * acc);
}

const r = repeat(() => fact(20, 1));
utest(r, 2432902008176640000);

