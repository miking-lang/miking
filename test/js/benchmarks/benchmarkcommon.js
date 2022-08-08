function repeat(f) {
  const times = parseInt(process.argv[2]);
  if (isNaN(times)) {
    console.log("Invalid number of iterations! Missing argument, expected an integer.");
    process.exit(1);
  }
  for (let i = 0; i < times; i++) f();
}

module.exports = { repeat };
