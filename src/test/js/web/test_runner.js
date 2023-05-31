const { JSDOM, VirtualConsole } = require('jsdom');
const virtualConsole = new VirtualConsole();
virtualConsole.sendTo(console);

/**
 * Run a web script file in a virtual DOM environment using the headless browser `jsdom`.
 * @param {string} path Full path to the web script file to execute.
 */
function runWebFile(path) {
  new JSDOM(`<body><script src="file:${path}"/></body>`, {
    url: "https://localhost/",
    contentType: "text/html",
    runScripts: "dangerously",
    resources: "usable",
    virtualConsole,
  });
}

function main(args) {
  if (args.length !== 1) {
    console.error("Usage: node test_runner.js <file>");
    process.exit(1);
  }
  runWebFile(`${process.cwd()}/${args[0]}`);
}

if (require.main === module) {
  main(process.argv.slice(2));
}
