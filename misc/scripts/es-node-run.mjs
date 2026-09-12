#!/usr/bin/env node
// Runs a module produced by the Miking `ecmascript` backend under Node.
//
// The backend emits a module whose default export takes a runtime environment,
// so something has to supply one. This is that something for Node; it is a
// sample host, not part of the compiler.
//
// Usage: node misc/scripts/es-node-run.mjs <module.mjs> [args...]

import { pathToFileURL } from "node:url";
import { nodeEnv } from "../../src/stdlib/ecmascript/hosts/node.mjs";

const target = process.argv[2];
if (target === undefined) {
  process.stderr.write("usage: es-node-run.mjs <module.mjs> [args...]\n");
  process.exit(1);
}

const { default: main } = await import(pathToFileURL(target).href);
// The program's arguments start at its own path, as they would for a binary.
main(nodeEnv({argv: process.argv.slice(2)}));
