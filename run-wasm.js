// Assume add.wasm file exists that contains a single function adding 2 provided arguments
const fs = require('node:fs');

const wasmBuffer = fs.readFileSync(process.argv[2]);
WebAssembly.instantiate(wasmBuffer).then(wasmModule => {
  // Exported function live under instance.exports
  const { main } = wasmModule.instance.exports;
  console.log(main());
});