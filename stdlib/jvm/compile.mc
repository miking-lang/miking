include "mexpr/ast.mc"
include "string.mc"
include "jvm/ast.mc"
include "javascript/util.mc"
include "seq.mc"
include "pmexpr/utils.mc"

lang MExprJVMCompile = MExprAst + JVMAst

    type JVMEnv = {
        bytecode : [Bytecode]}


    -- go through AST and translate to JVM bytecode

    sem toJSONExpr : JVMEnv -> Expr -> JVMEnv
    sem toJSONExpr env =
    | TmSeq {tms = tms} -> { env with bytecode = snoc env.bytecode (createBString "LDC" (_charSeq2String tms))}
    | TmConst { val = val } -> 
        let bc = (match val with CInt { val = val } then [(createBInt "LDC" val)]
        else (toJSONConst env val).bytecode)
        in { env with bytecode = concat env.bytecode bc }
    | TmApp { lhs = lhs, rhs = rhs } & app-> 
        let f = collectAppArguments app in
        let envList = (map (toJSONExpr env) f.1) in
        let args = foldl (lam x. lam y. { x with bytecode = concat x.bytecode y.bytecode }) (head envList) (tail envList) in
            match f.0 with TmConst { val = val } then
                match val with CPrint _ then 
                    { args with bytecode = concat (concat [(createBApply "GETSTATIC" "java/lang/System" "out" "Ljava/io/PrintStream;")] args.bytecode) [(createBApply "INVOKEVIRTUAL" "java/io/PrintStream" "print" "(Ljava/lang/String;)V")] }
                else 
                    let funcEnv = (toJSONExpr env f.0) in
                    { env with bytecode = (concat args.bytecode funcEnv.bytecode) }
            else never
    | a -> 
        (print "unknown\n");
        {bytecode = []}

    sem toJSONConst : JVMEnv -> Const -> JVMEnv
    sem toJSONConst env =
    | CAddi _ -> { env with bytecode = snoc env.bytecode (createBEmpty "IADD") }
    | a -> 
        (print "unknown\n");
        {bytecode = []}

end


let compileMCoreToJVM = lam ast. 
    use MExprJVMCompile in
    -- empty constructor
    let defaultConstructor = createFunction "constructor" "()V" [(createBInt "ALOAD" 0), (createBApply "INVOKESPECIAL" "java/lang/Object" "<init>" "()V"), (createBEmpty "RETURN")] in
    let env = {bytecode = []} in
    let compiledEnv = (toJSONExpr env ast) in
    let bytecode = (snoc compiledEnv.bytecode (createBEmpty "RETURN")) in
    let mainFunc = (createFunction "main" "([Ljava/lang/String;)V" bytecode) in 
    let prog = createProg "pkg/" [(createClass "Hello" "" [] defaultConstructor [mainFunc])] [] in

    (print (toStringProg prog));
    "aaa"
