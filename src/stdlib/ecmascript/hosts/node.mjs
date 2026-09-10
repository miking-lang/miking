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
import * as fs from "node:fs";
import { execSync } from "node:child_process";

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

    // Node exposes no synchronous flush for stdout or stderr.
    flushStdout: () => {},
    flushStderr: () => {},

    exit: (code) => {
      process.exit(code);
    },

    // MExpr's `error` aborts; it never returns a value.
    error: (msg) => {
      throw new Error(msg);
    },

    argv: () => process.argv.slice(1),

    // Reads one line from stdin, without its terminator.
    readLine: () => {
      const buf = Buffer.alloc(1);
      const out = [];
      while (fs.readSync(0, buf, 0, 1, null) === 1) {
        if (buf[0] === 0x0a) break;
        out.push(buf[0]);
      }
      return Buffer.from(out).toString("utf8");
    },

    readFile: (path) => fs.readFileSync(path, "utf8"),
    writeFile: (path, data) => {
      fs.writeFileSync(path, data);
    },
    fileExists: (path) => fs.existsSync(path),
    deleteFile: (path) => {
      fs.rmSync(path, { force: true });
    },

    // Returns the command's exit status, as MExpr's `command` does.
    command: (cmd) => {
      try {
        execSync(cmd, { stdio: "inherit" });
        return 0;
      } catch (e) {
        return typeof e.status === "number" ? e.status : 1;
      }
    },

    wallTimeMs: () => Date.now(),

    // Node has no synchronous sleep; this busy-waits, which is what a
    // blocking `sleepMs` requires.
    sleepMs: (ms) => {
      const end = Date.now() + ms;
      while (Date.now() < end) {}
    },

    randIntU: (lo, hi) => lo + Math.floor(Math.random() * (hi - lo)),

    // Math.random cannot be seeded; a host needing reproducible randomness
    // should supply its own generator.
    randSetSeed: (_seed) => {},
  };
}
