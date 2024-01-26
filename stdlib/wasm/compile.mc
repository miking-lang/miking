include "mexpr/pprint.mc"

let compileMCoreToWasm = lam ast.
    use MExprPrettyPrint in
    printLn (expr2str ast);
    printLn "At some point, this should do things...";
    ""