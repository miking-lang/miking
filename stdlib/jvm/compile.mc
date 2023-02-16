include "mexpr/ast.mc"
include "string.mc"
include "jvm/ast.mc"

lang MExprJVMCompile = MExprAst + JVMAst

    -- go through AST and translate to JVM bytecode

    sem toJSONExpr : JVMEnv -> Expr -> JVMEnv
    sem toJSONExpr env =
    | TmSeq {tms = tms} -> { env with bytecode = concat env.bytecode [(createBString "LDC" (_charSeq2String tms))]}
    | TmConst { val = val } -> 
        let bc = (match val with CInt { val = val } then (createBInt "LDC" val)
        else never)
        in { env with bytecode = concat env.bytecode [bc] }
    | TmApp { lhs = lhs, rhs = rhs } -> 
        match lhs with TmConst { val = val } then 
            match val with CPrint _ then 
                -- push this to stack
                let this = { env with bytecode = concat env.bytecode [(createBApply "GETSTATIC" "java/lang/System" "out" "Ljava/io/PrintStream;")] } in
                -- push args to stack
                let args = (toJSONExpr this rhs) in
                -- call function
                { args with bytecode = concat args.bytecode [(createBApply "INVOKEVIRTUAL" "java/io/PrintStream" "print" "(Ljava/lang/String;)V")] }
            else 
                let rhsEnv = (toJSONExpr env rhs) in
                let valEnv = (toJSONConst env val) in
                { env with bytecode = (concat rhsEnv.bytecode valEnv.bytecode) }
        else match lhs with TmApp { lhs = l, rhs = r } then
            (toJSONExpr (toJSONExpr env rhs) lhs)
        else never
    | a -> 
        (print "unknown\n");
        {bytecode = []}

    sem toJSONConst : JVMEnv -> Const -> JVMEnv
    sem toJSONConst env =
    | CAddi _ -> { env with bytecode = concat env.bytecode [(createBEmpty "IADD")] }
    | a -> 
        (print "unknown\n");
        {bytecode = []}

end

-- TODO: count local variables and stack size
let compileMCoreToJVM = lam ast. 
    use MExprJVMCompile in
    -- empty constructor
    let defaultConstructor = createFunction "constructor" "()V" [(createBInt "ALOAD" 0), (createBApply "INVOKESPECIAL" "java/lang/Object" "<init>" "()V"), (createBEmpty "RETURN")] in
    let env = {bytecode = []} in
    let compiledEnv = (toJSONExpr env ast) in
    let bytecode = (concat compiledEnv.bytecode [(createBEmpty "RETURN")]) in
    let mainFunc = (createFunction "main" "([Ljava/lang/String;)V" bytecode) in 
    let prog = createProg [(createClass "Hello" [] defaultConstructor [mainFunc])] in

    (print (toStringProg prog));
    "aaa"
