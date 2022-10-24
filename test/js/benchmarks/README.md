# JavaScript Benchmarks

To run the benchmarks, first install the following dependencies:

* [Node.js](https://nodejs.org/en/)	*- Required for running the benchmarks*
* [Bun](https://bun.sh/)			*- Optional, but recommended*
<!-- * [Deno](https://deno.land/)		*- Optional, but recommended* -->

It is also recommended to download the most recent version of the [Google Closure Compiler](https://mvnrepository.com/artifact/com.google.javascript/closure-compiler) and extract it to the root of the benchmark directory. Also make sure to rename it to `closure-compiler.jar`.

## Running the benchmarks

To run all benchmarks, use the following command:

```bash
./run_all
```

To run a specific benchmark, use the following command:

```bash
./run <benchmark_name> <iterations>
```

To clean up the benchmark directory from any output `.dat` files, use the following command:

```bash
./clean_dat
```

To collect the benchmark results and generate a report, use the following command:

```bash
./summarize
```

The `summarize` command will generate a `.dat` file containing the collected benchmark results from any existing benchmark `.dat` files in the benchmark directory. It automatically generates a plot of the benchmark results using [gnuplot](http://www.gnuplot.info/) and saves it to `benchmarks/plots/summary.png`.

## Extending the benchmarks
If the optimized JS code fails to run due to an external constant is accidentally renamed, you must update the `externs.js` file to include the new constant and give it a temporary value.
