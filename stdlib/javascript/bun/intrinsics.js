const MExpr_Bun_JS_Intrinsics = Object.freeze({
  print: async msg => await Bun.write(Bun.stdout, MExpr_JS_Intrinsics.ensureString(msg)),
  exit: code => process.exit(code),
  argv: () => Bun.argv.slice(2),
});
