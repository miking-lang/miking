function repeat(f) {
  const n = parseInt(process.argv[2]);
  let prev = f(0);
  if (isNaN(n)) {
    console.log("Invalid number of iterations! Missing argument, expected an integer.");
    process.exit(1);
  }
  for (let i = 1; i < n; i++) prev = f(i);
  return prev;
}

function utest(lhs, rhs, cmp = (l, r) => l === r) {
  if (!cmp(lhs, rhs)) {
    throw new Error("Unit test assertion failed! Parameters: " + lhs + " " + rhs);
  }
  return true;
}

module.exports = { repeat, utest };
