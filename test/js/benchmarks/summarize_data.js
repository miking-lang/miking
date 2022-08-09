const fs = require("fs");

const ROOT = process.cwd().substring(0, process.cwd().indexOf("miking")) + "miking/";
const BUILD = ROOT + "build/";
const BENCH = ROOT + "test/js/benchmarks/";
const PLOTS = BENCH + "plots/";
const SUMMARY_FILE_NAME = "summary.dat";

function main(args) {
  // Find all .dat files in th current directory
  // and collect the benchmark names and the iterations from the file names (benchmark-name_iterations.dat)
  // Then sort the benchmark names and the iterations in ascending order
  // and collect the benchmark names and the iterations in a .dat file for all benchmarks
  const files = fs.readdirSync(process.cwd());
  let benchmarks = [];
  for (const file of files) {
    if (file.endsWith(".dat") && file !== SUMMARY_FILE_NAME) {
      const name = file.substring(0, file.lastIndexOf("_"));
      const iterations = parseInt(file.substring(file.lastIndexOf("_") + 1, file.length - 4));
      benchmarks.push({ name, iterations });
    }
  }

  if (benchmarks.length === 0) {
    console.log("No benchmarks found to summarize.");
    return;
  } else {
    console.log("Found", benchmarks.length, "benchmarks!");
  }

  let longestName = 0;
  benchmarks = benchmarks.map(benchmark => {
    // benchmark.title = '"' + benchmark.name.replace(/_/g, " ") + "\\n(" + benchmark.iterations + " iter)\"";
    benchmark.title = '"' + benchmark.name.replace(/_/g, "\\n") + '"';
    longestName = Math.max(longestName, benchmark.title.length);
    return benchmark;
  });

  const summaryFile = PLOTS + SUMMARY_FILE_NAME;
  if (fs.existsSync(summaryFile)) fs.unlinkSync(summaryFile);
  fs.writeFileSync(summaryFile, `"Benchmark name"`.padEnd(longestName + 4, " ") + `"mi eval"\t"boot eval"\t"node (manual)"\t"node (compiled)"\t"bun (manual)"\t"bun (compiled)"\n`);
  for (const benchmark of benchmarks) {
    const file = `${BENCH}${benchmark.name}_${benchmark.iterations}.dat`;
    const lines = fs.readFileSync(file, "utf8").split("\n");
    let data = benchmark.title.padEnd(longestName + 5, " ");
    for (const line of lines) {
      if (line.startsWith("#")) continue;
      if (line.trim().length === 0) continue;
      const idx = line.lastIndexOf(" ");
      // const name = line.substring(0, idx); // Should line up with the predefined names
      const value = line.substring(idx + 1);
      data += value.padEnd(10, " ");
    }
    fs.appendFileSync(summaryFile, data.trimEnd() + "\n");
  }
}

if (require.main === module) {
  main(process.argv.slice(2));
}
