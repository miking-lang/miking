#!/usr/bin/env node

import { nodeEnv } from "../../misc/node/node-env.mjs";
import main from "./mi-es-lite.mjs";

const argv = process.argv.slice(1);
const env = nodeEnv({argv});

main(env);
