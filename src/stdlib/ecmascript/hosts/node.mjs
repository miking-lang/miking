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
import { execSync, spawnSync } from "node:child_process";

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

    // Reads exactly `n` bytes from stdin and returns the text together with
    // the number of *bytes* consumed, which is not the number of characters.
    //
    // The reference implementation reads exactly `n` bytes or nothing at all:
    // it uses OCaml's `really_input_string`, whose End_of_file case yields the
    // empty string rather than a short read. A partial read therefore reports
    // ("", 0) here too.
    readBytesAsString: (n) => {
      if (n < 0) {
        throw new RangeError("readBytesAsString: argument must not be negative");
      }
      const buf = Buffer.alloc(n);
      let got = 0;
      while (got < n) {
        let r = 0;
        try {
          r = fs.readSync(0, buf, got, n - got, null);
        } catch (e) {
          if (e.code === "EAGAIN") continue;
          if (e.code === "EOF") break;
          throw e;
        }
        if (r === 0) break;
        got += r;
      }
      return got < n ? ["", 0] : [buf.toString("utf8"), got];
    },

    // MExpr's `exec` is `execvp`: it replaces the running process and never
    // returns. Node cannot replace its own image, so the nearest faithful
    // behaviour is to run the program to completion and exit with its status.
    // A caller cannot tell the difference except by observing this process's
    // pid.
    exec: (program, args) => {
      const r = spawnSync(program, args, { stdio: "inherit" });
      if (r.error) throw r.error;
      process.exit(r.status === null ? 1 : r.status);
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
