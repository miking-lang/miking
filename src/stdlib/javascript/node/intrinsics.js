const MExpr_Node_JS_Intrinsics = Object.freeze({
  print: msg => process.stdout.write(MExpr_JS_Intrinsics.ensureString(msg)),
  exit: code => process.exit(code),
  argv: () => process.argv.slice(1),
});
