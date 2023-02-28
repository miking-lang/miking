include "mexpr/ast.mc"
include "string.mc"
include "jvm/ast.mc"
include "javascript/util.mc"
include "seq.mc"
include "pmexpr/utils.mc"

lang MExprJVMCompile = MExprAst + JVMAst

    type VarMap = {
        ident : Name,
        typ : String
    }

    type JVMEnv = {
        bytecode : [Bytecode],
        vars : [VarMap], 
        localVars : Int, -- number of local vars on the JVM
        classes : [Class]
    }

    sem wrapPrimitive : String -> [Bytecode]
    sem wrapPrimitive =
    | "I" -> [createBApply "INVOKESTATIC" "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;"]
    | a -> []

    sem unwrapPrimitive : String -> [Bytecode]
    sem unwrapPrimitive = 
    | "I" -> [createBString "CHECKCAST" "java/lang/Integer", createBApply "INVOKEVIRTUAL" "java/lang/Integer" "intValue" "()I"]
    | a -> []

    -- callConstructor var?

    -- go through AST and translate to JVM bytecode

    sem toJSONExpr : JVMEnv -> Expr -> JVMEnv
    sem toJSONExpr env =
    | TmSeq { tms = tms } -> { env with bytecode = concat env.bytecode [createBString "LDC" (_charSeq2String tms)]} -- only for strings now
    | TmConst { val = val } -> 
        let bc = (match val with CInt { val = val } then [createBInt "LDC" val, createBApply "INVOKESTATIC" "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;"]
        else (toJSONConst env val).bytecode)
        in { env with bytecode = concat env.bytecode bc }
    | TmApp { lhs = lhs, rhs = rhs, ty = ty } ->
        let to = ty in 
        let arg = toJSONExpr {bytecode = [], vars = [], localVars = 1, classes = []} rhs in
        match lhs with TmConst { val = CPrint _ } then
            { env with bytecode = foldl concat env.bytecode [[createBApply "GETSTATIC" "java/lang/System" "out" "Ljava/io/PrintStream;"], arg.bytecode, [createBApply "INVOKEVIRTUAL" "java/io/PrintStream" "print" "(Ljava/lang/String;)V"]] }
        else match lhs with TmConst { val = CAddi _ } then 
            let defaultConstructor = createFunction "constructor" "()V" [(createBInt "ALOAD" 0), (createBApply "INVOKESPECIAL" "java/lang/Object" "<init>" "()V"), (createBEmpty "RETURN")] in
            let name = (concat "Func" (int2string (length env.classes))) in
            let add = createClass name "pkg/Function" [] defaultConstructor [createFunction "apply" "(Ljava/lang/Object;)Ljava/lang/Object;" (foldl concat [createBInt "ALOAD" 1] [unwrapPrimitive "I", arg.bytecode, unwrapPrimitive "I", [createBEmpty "IADD"], wrapPrimitive "I", [createBEmpty "ARETURN"]])] in
            let res = { env with classes = snoc env.classes add, bytecode = foldl concat env.bytecode [[createBString "NEW" (concat "pkg/" name), createBEmpty "DUP" , createBApply "INVOKESPECIAL" (concat "pkg/" name) "<init>" "()V"]] } in
            res            
        else
            let fun = toJSONExpr env lhs in 
            { fun with bytecode = foldl concat env.bytecode [fun.bytecode, arg.bytecode, [createBApply "INVOKEINTERFACE" "pkg/Function" "apply" "(Ljava/lang/Object;)Ljava/lang/Object;"]] }
    | TmLet { ident = ident, body = body, inexpr = inexpr, tyBody = tyBody } -> 
        let b = toJSONExpr env body in
        match tyBody with TyArrow _ then 
            never -- add function types
        else 
            let javaTyp = getJavaType tyBody in
            let store = (match javaTyp with "I" then createBInt (concat "ISTORE_" (int2string env.localVars)) env.localVars
                else never) -- add other types
            in toJSONExpr { env with localVars = addi env.localVars 1, vars = snoc env.vars { ident = ident, typ = javaTyp }, bytecode = concat env.bytecode (snoc b.bytecode store) } inexpr
    --| TmLam { ident = ident, body = body } ->
    | TmVar _ -> 
        (print "TmVar\n");
        env
    | a -> 
        (print "unknown expr\n");
        env


    sem getJavaType : Type -> String
    sem getJavaType =
    | TyInt _ -> "I"
    | a -> ""

    sem toJSONConst : JVMEnv -> Const -> JVMEnv
    sem toJSONConst env =
    | a -> 
        (print "unknown const\n");
        env

end

let compileMCoreToJVM = lam ast. 
    use MExprJVMCompile in
    -- empty constructor
    let defaultConstructor = createFunction "constructor" "()V" [createBInt "ALOAD" 0, createBApply "INVOKESPECIAL" "java/lang/Object" "<init>" "()V", createBEmpty "RETURN"] in
    let objToObj = createInterface "Function" [] [createFunction "apply" "(Ljava/lang/Object;)Ljava/lang/Object;" []] in 
    let env = {bytecode = [], vars = [], localVars = 1, classes = [] } in
    let compiledEnv = (toJSONExpr env ast) in
    --let bytecode = concat compiledEnv.bytecode [createBEmpty "RETURN"] in
    let bytecode = concat compiledEnv.bytecode [createBEmpty "POP", createBEmpty "RETURN"] in
    --let bytecode = concat compiledEnv.bytecode [createBInt "ASTORE" env.localVars, createBApply "GETSTATIC" "java/lang/System" "out" "Ljava/io/PrintStream;", createBInt "ALOAD" env.localVars, createBApply "INVOKEVIRTUAL" "java/io/PrintStream" "print" "(Ljava/lang/Object;)V", createBEmpty "RETURN"] in -- should not print out result!
    let mainFunc = createFunction "main" "([Ljava/lang/String;)V" bytecode in 
    let prog = createProg "pkg/" (snoc compiledEnv.classes (createClass "Hello" "" [] defaultConstructor [mainFunc])) [objToObj] in

    (print (toStringProg prog));
    "aaa"
