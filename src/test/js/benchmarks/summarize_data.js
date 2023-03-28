const fs = require("fs");

const ROOT = process.cwd().substring(0, process.cwd().indexOf("miking")) + "miking/";
const BENCH = `${ROOT}/test/js/benchmarks`;
const PLOTS = `${BENCH}/plots`;
const SUMMARY_FILE_NAME = "summary.dat";

function main() {
  // Find all .dat files in th current directory
  // and collect the benchmark names and the iterations from the file names (benchmark-name_iterations.dat)
  // Then sort the benchmark names and the iterations in ascending order
  // and collect the benchmark names and the iterations in a .dat file for all benchmarks
  const files = fs.readdirSync(process.cwd());
  const benchmarks = [];
  let longestName = 0;
  for (const file of files) {
    if (file.endsWith(".dat") && file !== SUMMARY_FILE_NAME) {
      const name = file.substring(0, file.lastIndexOf("_"));
      const iterations = parseInt(file.substring(file.lastIndexOf("_") + 1, file.length - 4));
      const title = '"' + name.replace(/_/g, " ") + "\\n(" + iterations + " iter)\"";
      longestName = Math.max(longestName, title.length);

      const lines = fs.readFileSync(file, "utf8").split("\n");
      const data = [];
      const names = []
      for (const line of lines) {
        if (line.startsWith("#") || line.trim().length === 0) continue;
        const idx = line.lastIndexOf(" ");
        const name = line.substring(0, idx).trim(); // Should line up with the predefined names
        const value = line.substring(idx + 1);
        names.push(name);
        data.push(value); // += value.padEnd(10, " ");
      }
      benchmarks.push({ name, title, iterations, names, data, nameCount: names.length });
    }
  }

  if (benchmarks.length === 0) {
    console.log("No benchmarks found to summarize.");
    return;
  } else if (!benchmarks.every(b => b.nameCount === benchmarks[0].nameCount)) {
    console.log("Benchmarks have different number of names.");
    return;
  } else {
    console.log("Found", benchmarks.length, "benchmarks!");
  }

  // Setup the summary file
  const summaryFile = `${PLOTS}/${SUMMARY_FILE_NAME}`;
  if (fs.existsSync(summaryFile)) fs.unlinkSync(summaryFile);
  const namesStr = benchmarks[0].names.join("\t"); // All names are the same, so just use the first one
  // const names = `"mi eval"\t"boot eval"\t"ocaml (compiled)"\t"node (manual)"\t"node (compiled)"\t"node (compiled+opt)"\t"bun (manual)"\t"bun (compiled)"\t"bun (compiled+opt)"\n`
  fs.writeFileSync(summaryFile, `"Benchmark name"`.padEnd(longestName + 4, " ") + namesStr + "\n");

  for (const benchmark of benchmarks) {
    let result = "";
    result += benchmark.title.padEnd(longestName + 4, " ");
    for (let i = 0; i < benchmark.names.length; i++) {
      value = benchmark.data[i].toString();
      result += " " + value.padEnd(benchmark.names[i].length - value.length + 1, " ") + "\t";
    }
    result = result.trimEnd();
    fs.appendFileSync(summaryFile, result + "\n");
  }
}

if (require.main === module) {
  main(process.argv.slice(2));
}
