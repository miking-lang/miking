function repeat(f) {
  const n = parseInt(process.argv[2]);
  let prev = f();
  if (isNaN(n)) {
    console.log("Invalid number of iterations! Missing argument, expected an integer.");
    process.exit(1);
  }
  for (let i = 1; i < n; i++) prev = f();
  return prev;
}

function utest(condition) {
  if (!condition) {
    throw new Error("Unit test assertion failed!");
  }
}

module.exports = { repeat, utest };
