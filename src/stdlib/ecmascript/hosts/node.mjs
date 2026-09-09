// A reference runtime environment for programs compiled by the Miking
// `ecmascript` backend, implemented for Node.
//
// This file is an ordinary hand-written module, not compiler output, and the
// compiler has no knowledge of it. A compiled program takes its environment as
// an argument on every execution, so an embedder is free to pass something
// else entirely as long as it provides these operations.
//
// Only effectful operations belong here. Pure intrinsics such as `addi` are
// compiled inline or imported from the runtime module, and are never injected.

import { inspect } from "node:util";

export function nodeEnv() {
  return {
    // Writes a string with no trailing newline
    print: (s) => {
      process.stdout.write(s);
    },

    printError: (s) => {
      process.stderr.write(s);
    },

    // Renders any value for debugging, terminated with a newline.
    dprint: (v) => {
      process.stdout.write(inspect(v, { depth: null }) + "\n");
    },

    flushStdout: () => {},

    exit: (code) => {
      process.exit(code);
    },

    argv: () => process.argv.slice(1),
  };
}
