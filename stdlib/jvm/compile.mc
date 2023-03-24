include "mexpr/ast.mc"
include "mexpr/pprint.mc"
include "string.mc"
include "jvm/ast.mc"
include "javascript/util.mc"
include "seq.mc"
include "pmexpr/utils.mc"
include "jvm/constants.mc"
include "stdlib.mc"
include "sys.mc"
include "map.mc"
include "mexpr/cmp.mc"
include "mexpr/lamlift.mc"
include "mexpr/type-annot.mc"
include "mexpr/type-lift.mc"

lang MExprJVMCompile = MExprAst + JVMAst + MExprPrettyPrint + MExprCmp

    type JVMEnv = {
        bytecode : [Bytecode],
        vars : Map Name Int, 
        fieldVars : Map Name Field,
        localVars : Int, -- number of local vars on the JVM
        classes : [Class],
        name : String,
        nextClass : String,
        recordMap : Map Type (Map SID Int),
        adtTags : Map Name Int
    }

    -- go through AST and translate to JVM bytecode

    sem toJSONExpr : JVMEnv -> Expr -> JVMEnv
    sem toJSONExpr env =
    | TmSeq { tms = tms } -> { env with bytecode = concat env.bytecode [ldcString_ (_charSeq2String tms)]} -- only for strings now
    | TmConst { val = val } -> 
        let bc = (match val with CInt { val = val } then 
            concat [ldcLong_ val] wrapInteger_
        else match val with CFloat { val = val } then
            concat [ldcFloat_ val] wrapFloat_ 
        else match val with CBool { val = val } then 
            match val with true then
                concat [ldcInt_ 1] wrapBoolean_
            else 
                concat [ldcInt_ 0] wrapBoolean_
        else match val with CChar { val = val } then
            wrapChar_ [ldcInt_ (char2int val)]
        else never)
        in { env with bytecode = concat env.bytecode bc }
    | TmApp { lhs = lhs, rhs = rhs, ty = ty } ->
        let to = ty in 
        let arg = toJSONExpr { env with bytecode = [], classes = [] } rhs in
        match lhs with TmConst _ then 
            match lhs with TmConst { val = CPrint _ } then
                { env with 
                    bytecode = foldl concat env.bytecode 
                        [[getstatic_ "java/lang/System" "out" "Ljava/io/PrintStream;"], 
                        arg.bytecode, 
                        [invokevirtual_ "java/io/PrintStream" "print" "(Ljava/lang/String;)V"],
                        [ldcInt_ 1],
                        wrapInteger_], -- change this to () later 
                    classes = concat env.classes arg.classes }
            -- this could be a Map?
            else match lhs with TmConst { val = CAddi _ } then 
                applyArithI_ "Addi" env arg 
            else match lhs with TmConst { val = CSubi _ } then 
                applyArithI_ "Subi" env arg
            else match lhs with TmConst { val = CMuli _ } then 
                applyArithI_ "Muli" env arg
            else match lhs with TmConst { val = CDivi _ } then 
                applyArithI_ "Divi" env arg
            else match lhs with TmConst { val = CModi _ } then 
                applyArithI_ "Modi" env arg
            else match lhs with TmConst { val = CAddf _ } then 
                applyArithF_ "Addf" env arg 
            else match lhs with TmConst { val = CSubf _ } then 
                applyArithF_ "Subf" env arg
            else match lhs with TmConst { val = CMulf _ } then 
                applyArithF_ "Mulf" env arg
            else match lhs with TmConst { val = CDivf _ } then 
                applyArithF_ "Divf" env arg
            else match lhs with TmConst { val = CEqi _ } then
                applyArithI_ "Eqi" env arg
            else match lhs with TmConst { val = CNeqi _ } then
                applyArithI_ "Neqi" env arg
            else match lhs with TmConst { val = CLti _ } then
                applyArithI_ "Lti" env arg
            else match lhs with TmConst { val = CGti _ } then
                applyArithI_ "Gti" env arg
            else match lhs with TmConst { val = CLeqi _ } then
                applyArithI_ "Leqi" env arg
            else match lhs with TmConst { val = CGeqi _ } then
                applyArithI_ "Geqi" env arg
            else match lhs with TmConst { val = CEqf _ } then
                applyArithF_ "Eqf" env arg
            else match lhs with TmConst { val = CNeqf _ } then
                applyArithF_ "Neqf" env arg
            else match lhs with TmConst { val = CLtf _ } then
                applyArithF_ "Ltf" env arg
            else match lhs with TmConst { val = CGtf _ } then
                applyArithF_ "Gtf" env arg
            else match lhs with TmConst { val = CLeqf _ } then
                applyArithF_ "Leqf" env arg
            else match lhs with TmConst { val = CGeqf _ } then
                applyArithF_ "Geqf" env arg
            else match lhs with TmConst { val = CSlli _ } then
                applyArithI_ "Slli" env arg
            else match lhs with TmConst { val = CSrli _ } then
                applyArithI_ "Srli" env arg
            else match lhs with TmConst { val = CSrai _ } then
                applyArithI_ "Srai" env arg
            else match lhs with TmConst { val = CNegf _ } then
                oneArgOpF_ dneg_ env arg
            else match lhs with TmConst { val = CNegi _ } then
                oneArgOpI_ lneg_ env arg
            else match lhs with TmConst { val = CEqc _ } then
                applyArithC_ "Eqc" env arg
            else 
                (print "Unknown Const!\n");
                env
        -- if type of arg is Record -> Array
        else
            let fun = toJSONExpr env lhs in 
            { fun with 
                bytecode = foldl concat fun.bytecode 
                    [arg.bytecode, 
                    [checkcast_ object_T],
                    [invokeinterface_ (concat pkg_ "Function") "apply" "(Ljava/lang/Object;)Ljava/lang/Object;"]], 
                    classes = concat fun.classes arg.classes }
    | TmLet { ident = ident, body = body, inexpr = inexpr, tyBody = tyBody } -> 
        let b = toJSONExpr { env with fieldVars = mapEmpty nameCmp } body in
        toJSONExpr { b with 
                        bytecode = snoc b.bytecode (astore_ env.localVars), 
                        fieldVars = mapEmpty nameCmp, 
                        localVars = addi 1 env.localVars, 
                        vars = mapInsert ident env.localVars env.vars } inexpr
    | TmLam { ident = ident, body = body } -> 
        let className = env.nextClass in
        let newField = (createField (nameGetStr ident) object_LT) in
        let nextClass = createName_ "Func" in
        let bodyEnv = toJSONExpr { env with bytecode = [], name = className, nextClass = nextClass, fieldVars = mapInsert ident newField env.fieldVars } body in 
        let fields = map (lam x. x.1) (mapToSeq env.fieldVars) in
        match body with TmLam _ then
            let putfields = join (mapi (lam i. lam x. [aload_ 0, getfield_ (concat pkg_ className) (getNameField x) object_LT, putfield_ (concat pkg_ nextClass) (getNameField x) object_LT]) fields) in
            let dups = map (lam x. dup_) fields in
            let apply = apply_ (foldl concat bodyEnv.bytecode [dups, [dup_, aload_ 1, putfield_ (concat pkg_ nextClass) (nameGetStr ident) object_LT], putfields]) in
            let funcClass = createClass className (concat pkg_ "Function") (snoc fields newField) defaultConstructor [apply] in
            { env with 
                classes = snoc bodyEnv.classes funcClass,
                bytecode = foldl concat env.bytecode [initClass_ className],
                nextClass = bodyEnv.nextClass }
        else 
            let apply = apply_ bodyEnv.bytecode in
            let funcClass = createClass className (concat pkg_ "Function") fields defaultConstructor [apply] in
            { env with 
                classes = snoc bodyEnv.classes funcClass,
                bytecode = foldl concat env.bytecode [initClass_ className],
                nextClass = bodyEnv.nextClass }
    | TmVar { ident = ident } -> 
        let store = (match mapLookup ident env.vars with Some i then
            [aload_ i]
        else match mapLookup ident env.fieldVars with Some field then 
            -- do fieldlookup
            [aload_ 0, getfield_ (concat pkg_ env.name) (getNameField field) "Ljava/lang/Object;"]
        else
            (print (join ["No identifier! ", nameGetStr ident, "\n"]));
            []) in
        { env with bytecode = concat env.bytecode store }
    | TmMatch { target = target, pat = pat, thn = thn, els = els } -> 
        let targetEnv = toJSONExpr env target in
        jvmPat targetEnv (tyTm target) thn els pat
    | TmRecord { bindings = bindings, ty = ty } ->
        let mapSeq = mapToSeq bindings in
        let len = length mapSeq in
        match mapLookup ty env.recordMap with Some translation then
            let insertBytecode = foldl (
                lam e. lam tup.
                    let expr = (match mapLookup tup.0 bindings with Some e then e else never) in
                    let exprEnv = toJSONExpr { e with bytecode = concat e.bytecode [dup_, ldcInt_ tup.1] } expr in 
                    { e with bytecode = snoc exprEnv.bytecode aastore_, classes = concat e.classes exprEnv.classes }
            ) { env with bytecode = [], classes = [] } (mapToSeq translation) in
            let recordBytecode = concat [ldcInt_ len, anewarray_ object_T] insertBytecode.bytecode in
            { env with 
                bytecode = concat env.bytecode (wrapRecord_ recordBytecode), 
                classes = insertBytecode.classes }
        else
            let sidInt = mapi (lam i. lam tup. (tup.0, i)) mapSeq in
            let sidIntMap = mapFromSeq cmpSID sidInt in
            let insertBytecode = foldl (
                lam e. lam tup.
                    let expr = (match mapLookup tup.0 bindings with Some e then e else never) in
                    let exprEnv = toJSONExpr { e with bytecode = concat e.bytecode [dup_, ldcInt_ tup.1] } expr in 
                    { e with bytecode = snoc exprEnv.bytecode aastore_, classes = concat e.classes exprEnv.classes }
            ) { env with bytecode = [], classes = [] } sidInt in
            let recordBytecode = concat [ldcInt_ len, anewarray_ object_T] insertBytecode.bytecode in
            { env with 
                bytecode = concat env.bytecode (wrapRecord_ recordBytecode), 
                classes = insertBytecode.classes, 
                recordMap = mapInsert ty sidIntMap env.recordMap }
    | TmRecLets _ -> (printLn "TmRecLets"); env
    | TmSeq _ -> (printLn "TmSeq"); env
    | TmRecordUpdate _ -> (printLn "TmRecordUpdate"); env
    | TmType _ -> (printLn "TmType: Should be gone"); env
    | TmConDef _ -> (printLn "TmConDef: Should be gone"); env
    | TmConApp { ident = ident, body = body } -> 
        let constructor = nameGetStr ident in
        let bodyEnv = toJSONExpr { env with bytecode = [], classes = [] } body in
        { env with 
            bytecode = foldl concat 
                env.bytecode
                [initClass_ constructor,
                [dup_],
                bodyEnv.bytecode,
                [putfield_ (concat pkg_ constructor) "value" object_LT]],
            classes = concat bodyEnv.classes env.classes,
            recordMap = foldl (lam acc. lam tup. mapInsert tup.0 tup.1 acc ) env.recordMap (mapToSeq bodyEnv.recordMap) }
    | TmUtest _ -> (printLn "TmUtest"); env
    | TmNever _ -> { env with bytecode = concat env.bytecode [new_ "java/lang/Exception", dup_, ldcString_ "Never Reached!", invokespecial_ "java/lang/Exception" "<init>" "(Ljava/lang/String;)V"] }
    | TmExt _ -> (printLn "TmExt"); env
    | a -> 
        (print "unknown expr\n");
        env

    sem jvmPat : JVMEnv -> Type -> Expr -> Expr -> Pat -> JVMEnv
    sem jvmPat env targetty thn els =
    | PatInt { val = val } ->
        let thnEnv = toJSONExpr { env with bytecode = [], classes = [] } thn in
        let elsEnv = toJSONExpr { env with bytecode = [], classes = [] } els in
        let elsLabel = createName_ "els" in
        let endLabel = createName_ "end" in
        { env with 
            bytecode = foldl concat 
                    env.bytecode 
                    [unwrapInteger_,
                    [ldcLong_ val, 
                    lcmp_, 
                    ifne_ elsLabel], 
                    thnEnv.bytecode, 
                    [goto_ endLabel,
                    label_ elsLabel], 
                    elsEnv.bytecode, 
                    [label_ endLabel]],
            classes = foldl concat env.classes [thnEnv.classes, elsEnv.classes] }
    | PatRecord { bindings = bindings, ty = ty } ->
        match eqi (cmpType targetty ty) 0 with true then
            match mapLookup ty env.recordMap with Some r then 
                let patEnv = foldl 
                        (lam e. lam tup.
                            let sid = tup.0 in
                            let pat = tup.1 in 
                            match pat with PatNamed { ident = ident } then
                                match ident with PName name then 
                                    match mapLookup sid r with Some i then 
                                        { e with 
                                            bytecode = foldl concat e.bytecode [[dup_], unwrapRecord_, [ldcInt_ i, aaload_, astore_ e.localVars]],
                                            localVars = addi 1 e.localVars,
                                            vars = mapInsert name e.localVars e.vars } 
                                    else never
                                else never -- Wildcard!
                            else never) 
                        env
                        (mapToSeq bindings) in
                toJSONExpr { patEnv with bytecode = snoc patEnv.bytecode pop_ } thn 
            else never
        else 
            toJSONExpr env els
    | PatBool { val = val } ->
        let thnEnv = toJSONExpr { env with bytecode = [], classes = [] } thn in
        let elsEnv = toJSONExpr { env with bytecode = [], classes = [] } els in
        let elsLabel = createName_ "els" in
        let endLabel = createName_ "end" in
        let boolVal = (match val with true then 1 else 0) in
        { env with 
            bytecode = foldl concat 
                    env.bytecode 
                    [unwrapBoolean_,
                    [ldcInt_ boolVal,
                    ificmpne_ elsLabel], 
                    thnEnv.bytecode, 
                    [goto_ endLabel,
                    label_ elsLabel], 
                    elsEnv.bytecode, 
                    [label_ endLabel]],
            classes = foldl concat env.classes [thnEnv.classes, elsEnv.classes] }
    | PatChar { val = val } ->
        let thnEnv = toJSONExpr { env with bytecode = [], classes = [] } thn in
        let elsEnv = toJSONExpr { env with bytecode = [], classes = [] } els in
        let elsLabel = createName_ "els" in
        let endLabel = createName_ "end" in
        let charVal = char2int val in
        { env with 
            bytecode = foldl concat 
                    env.bytecode 
                    [unwrapChar_,
                    [ldcInt_ charVal,
                    ificmpne_ elsLabel], 
                    thnEnv.bytecode, 
                    [goto_ endLabel,
                    label_ elsLabel], 
                    elsEnv.bytecode, 
                    [label_ endLabel]],
            classes = foldl concat env.classes [thnEnv.classes, elsEnv.classes] }
    | PatCon { ident = ident, subpat = subpat } ->
        let tag = (match mapLookup ident env.adtTags with Some t then t else never) in
        let elsLabel = createName_ "els" in
        let endLabel = createName_ "end" in
        match subpat with PatNamed { ident = id } then 
            match id with PName name then 
                let patEnv = { env with 
                                bytecode = foldl concat 
                                    env.bytecode 
                                    [[dup_,
                                    invokevirtual_ (concat pkg_ (nameGetStr ident)) "getTag" "()I",
                                    ldcInt_ tag,
                                    ificmpne_ elsLabel, 
                                    getfield_ (concat pkg_ (nameGetStr ident)) "value" object_LT,
                                    astore_ env.localVars]],
                                localVars = addi 1 env.localVars,
                                vars = mapInsert name env.localVars env.vars } in
                let thnEnv = toJSONExpr patEnv thn in
                let elsEnv = toJSONExpr { patEnv with bytecode = [], classes = [] } els in
                { thnEnv with 
                    bytecode = foldl concat 
                        thnEnv.bytecode
                        [[goto_ endLabel,
                        label_ elsLabel,
                        pop_], 
                        elsEnv.bytecode,
                        [label_ endLabel]],
                    classes = concat thnEnv.classes elsEnv.classes }
            else never
        else never 
    | a -> 
        (printLn "Unknown Pat"); 
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

let collectADTTypes = lam tlMapping. 
    use MExprJVMCompile in
    foldl (lam acc. lam tup. 
            let t = tup.1 in 
            match t with TyVariant { constrs = constrs } then -- ADT
                let classes = acc.1 in
                let interfaces = acc.0 in
                let name = nameGetStr tup.0 in
                let interf = createInterface name [] [createFunction "getTag" "()I" []] in
                let constrClasses = foldli (lam acc. lam i. lam tup.
                                        let tagLookup = mapInsert tup.0 i acc.2 in
                                        let interfName = acc.0 in 
                                        let classes = acc.1 in
                                        let constrName = nameGetStr tup.0 in
                                        let class = createClass
                                                        constrName
                                                        (concat pkg_ interfName)
                                                        [createField "value" object_LT]
                                                        defaultConstructor
                                                        [createFunction 
                                                            "getTag"
                                                            "()I"
                                                            [ldcInt_ i,
                                                            ireturn_]] in
                                        (interfName, snoc classes class, tagLookup)) (name, [], mapEmpty nameCmp) (mapToSeq constrs) in
                let tagLookup = foldl (lam a. lam tup. mapInsert tup.0 tup.1 a) acc.2 (mapToSeq constrClasses.2) in
                (snoc interfaces interf, concat classes constrClasses.1, tagLookup)
            else -- record
                acc
            ) ([], [], mapEmpty nameCmp) tlMapping

let compileJVMEnv = lam ast.
    use MExprJVMCompile in
    use MExprTypeLift in
    let tl = typeLift ast in
    let adt = collectADTTypes tl.0 in
    let tlAst = tl.1 in
    let objToObj = createInterface "Function" [] [createFunction "apply" "(Ljava/lang/Object;)Ljava/lang/Object;" []] in 
    let env = { bytecode = [], vars = mapEmpty nameCmp, localVars = 1, classes = [], fieldVars = mapEmpty nameCmp, name = "Main", nextClass = createName_ "Func", recordMap = mapEmpty cmpType, adtTags = adt.2 } in
    let compiledEnv = (toJSONExpr env tlAst) in
    --let bytecode = concat compiledEnv.bytecode [pop_, return_] in
    let bytecode = concat compiledEnv.bytecode [astore_ 0, getstatic_ "java/lang/System" "out" "Ljava/io/PrintStream;", aload_ 0, invokevirtual_ "java/io/PrintStream" "print" "(Ljava/lang/Object;)V", return_] in
    let mainFunc = createFunction "main" "([Ljava/lang/String;)V" bytecode in 
    let constClasses = concat constClassList_ adt.1 in
    let prog = createProg pkg_ (snoc (concat compiledEnv.classes constClasses) (createClass "Main" "" [] defaultConstructor [mainFunc])) (snoc adt.0 objToObj) in
    prog 

let compileMCoreToJVM = lam ast. 
    use MExprJVMCompile in
    use MExprLambdaLift in
    use MExprTypeAnnot in
    use MExprTypeCheck in
    let typeFix = typeCheck ast in -- types dissapear in patern lowering
    let liftedAst = liftLambdas typeFix in
    let jvmProgram = compileJVMEnv liftedAst in
    (print (toStringProg jvmProgram));
    "aaa"

let getJarFiles = lam tempDir.
    (sysRunCommand ["curl", "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-core/2.14.2/jackson-core-2.14.2.jar", "--output", (concat tempDir "jackson-core-2.14.2.jar")] "" ".");
    (sysRunCommand ["curl", "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-databind/2.14.2/jackson-databind-2.14.2.jar", "--output", (concat tempDir "jackson-databind-2.14.2.jar")] "" ".");
    (sysRunCommand ["curl", "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-annotations/2.14.2/jackson-annotations-2.14.2.jar", "--output", (concat tempDir "jackson-annotations-2.14.2.jar")] "" ".");
    (sysRunCommand ["curl", "https://repo1.maven.org/maven2/org/ow2/asm/asm/9.4/asm-9.4.jar", "--output", (concat tempDir "asm-9.4.jar")] "" ".");
    ()

let compileJava = lam outDir. lam jarPath.
    let cfmClass = (concat stdlibLoc "/jvm/codegen/ClassfileMaker.java") in
    let jsonParserClass = (concat stdlibLoc "/jvm/codegen/Parser.java") in
    let classpath = (join [jarPath, "jackson-annotations-2.14.2.jar:", jarPath, "jackson-core-2.14.2.jar:", jarPath, "jackson-databind-2.14.2.jar:", jarPath, "asm-9.4.jar"]) in
    (sysRunCommand ["javac", "-cp", classpath, cfmClass, jsonParserClass, "-d", outDir] "" ".");
    ()

let modifyMainClassForTest = lam prog.
    use MExprJVMCompile in
    match prog with JVMProgram p in
    let mainClass = get p.classes (subi (length p.classes) 1) in
    match mainClass with Class m in
    let mainFunc = get m.functions 0 in
    match mainFunc with Function f in
    let bytecodes = subsequence f.bytecode 0 (subi (length f.bytecode) 2) in
    let modifiedMainFunc = createFunction f.name f.descriptor (concat bytecodes [astore_ 0, getstatic_ "java/lang/System" "out" "Ljava/io/PrintStream;", aload_ 0, invokevirtual_ "java/io/PrintStream" "print" "(Ljava/lang/Object;)V", return_]) in
    let modifiedMainClass = createClass m.name m.implements m.fields m.constructor [modifiedMainFunc] in
    createProg p.package (snoc (subsequence p.classes 0 (subi (length p.classes) 1)) modifiedMainClass) p.interfaces
    

let prepareForTests = lam path.
    match sysCommandExists "java" with false then 
        error "java needs to be installed\n"
        ()
    else
        (match sysFileExists path with true then
            (sysDeleteDir path);
            (sysRunCommand ["mkdir", path] "" ".");
            (sysRunCommand ["mkdir", (concat path "jar/")] "" ".");
            (sysRunCommand ["mkdir", (concat path "out/")] "" ".");
            ()
        else 
            (sysRunCommand ["mkdir", path] "" ".");
            (sysRunCommand ["mkdir", (concat path "jar/")] "" ".");
            (sysRunCommand ["mkdir", (concat path "out/")] "" ".");
            ());
        (getJarFiles (concat path "jar/"));
        (compileJava (concat path "out/") (concat path "jar/"));
        ()

let jvmTmpPath = "/tmp/miking-jvm-backend/"

let testJVM = lam ast.
    use MExprJVMCompile in
    use MExprLambdaLift in
    use MExprTypeAnnot in
    use MExprTypeCheck in
    let typeFix = typeCheck ast in
    let liftedAst = liftLambdas typeFix in
    let jvmProgram = compileJVMEnv liftedAst in
    let testJVMProgram = modifyMainClassForTest jvmProgram in
    let json = sysTempFileMake () in
    writeFile json (toStringProg testJVMProgram);
    let jarPath = (concat jvmTmpPath "jar/") in
    let classpath = (join [":", jarPath, "jackson-annotations-2.14.2.jar:", jarPath, "jackson-core-2.14.2.jar:", jarPath, "jackson-databind-2.14.2.jar:", jarPath, "asm-9.4.jar"]) in
    (sysRunCommand ["java", "-cp", (join [jvmTmpPath, "out/", classpath]), "codegen/Parser", json] "" jvmTmpPath);
    let results = sysRunCommand ["java", "pkg.Main"] "" jvmTmpPath in
    sysDeleteDir json;
    results.stdout

-- tests

mexpr
prepareForTests jvmTmpPath;

-- integer operations
utest testJVM (addi_ (int_ 1) (int_ 1)) with "2" in
utest testJVM (subi_ (int_ 0) (int_ 1)) with "-1" in
utest testJVM (divi_ (int_ 10) (int_ 5)) with "2" in
utest testJVM (muli_ (int_ 2) (int_ (negi 1))) with "-2" in
utest testJVM (modi_ (int_ 10) (int_ 2)) with "0" in
utest testJVM (negi_ (int_ 1)) with "-1" in 
utest testJVM (slli_ (int_ 3) (int_ 2)) with "12" in 
utest testJVM (srli_ (int_ 24) (int_ 3)) with "3" in 
utest testJVM (srai_ (negi_ (int_ 24)) (int_ 3)) with "-3" in 

-- integer boolean operations
utest testJVM (lti_ (int_ 20) (int_ 10)) with "false" in
utest testJVM (gti_ (int_ 20) (int_ 10)) with "true" in
utest testJVM (eqi_ (int_ 10) (int_ 10)) with "true" in
utest testJVM (neqi_ (int_ 10) (int_ 10)) with "false" in
utest testJVM (leqi_ (int_ 20) (int_ 20)) with "true" in
utest testJVM (geqi_ (int_ 1) (int_ 9)) with "false" in

-- float boolean operations
utest testJVM (ltf_ (float_ 10.0) (float_ 10.5)) with "true" in
utest testJVM (gtf_ (float_ 20.0) (float_ 10.0)) with "true" in
utest testJVM (eqf_ (float_ 10.0) (float_ 10.0)) with "true" in
utest testJVM (neqf_ (float_ 10.0) (float_ 10.0)) with "false" in
utest testJVM (leqf_ (float_ 0.505) (float_ 0.505)) with "true" in
utest testJVM (geqf_ (float_ 1.5) (float_ 1.0)) with "true" in

-- float operations
utest testJVM (addf_ (float_ 1.5) (float_ 1.0)) with "2.5" in
utest testJVM (subf_ (float_ 0.5) (float_ 1.0)) with "-0.5" in
utest testJVM (divf_ (float_ 5.0) (float_ 10.0)) with "0.5" in
utest testJVM (mulf_ (float_ 2.2) (float_ (negf 1.0))) with "-2.2" in
utest testJVM (negf_ (float_ 1.5)) with "-1.5" in

-- char operations
utest testJVM (eqc_ (char_ 'a') (char_ 'a')) with "true" in

-- lambdas and let ins
utest testJVM (bindall_ [ulet_ "g" (ulam_ "f" (ulam_ "x" (ulam_ "y" (appf2_ (var_ "f") (var_ "x") (var_ "y"))))), subi_ (int_ 3) (int_ 2)]) with "1" in
utest testJVM (bindall_ [ulet_ "a" (int_ 1), ulet_ "b" (int_ 1), addi_ (var_ "a") (var_ "b")]) with "2" in

-- pattern matching
utest testJVM (match_ (int_ 1) (pint_ 1) (int_ 10) (negi_ (int_ 10))) with "10" in
utest testJVM (match_ (int_ 1) (pint_ 5) (int_ 10) (negi_ (int_ 10))) with "-10" in
utest testJVM (match_ (bool_ true) (pbool_ true) (bool_ true) (bool_ false)) with "true" in
utest testJVM (match_ (bool_ false) (pbool_ true) (bool_ true) (bool_ false)) with "false" in
utest testJVM (match_ (char_ 'a') (pchar_ 'a') (bool_ true) (bool_ false)) with "true" in
utest testJVM (match_ (char_ 'a') (pchar_ 'b') (bool_ true) (bool_ false)) with "false" in
utest (
    use MExprAst in
    let target = record_add "a" (int_ 10) (record_ (tyrecord_ [("a", tyint_)]) [("a", int_ 10)]) in
    let bindings = mapInsert (stringToSid "a") (pvar_ "a") (mapEmpty cmpSID) in
    let pat = PatRecord { bindings = bindings, info = NoInfo (), ty = tyrecord_ [("a", tyint_)] } in
    let thn = var_ "a" in
    let els = never_ in
    testJVM (match_ target pat thn els)) with "10" in

-- never
utest testJVM never_ with "java.lang.Exception: Never Reached!" in

sysDeleteDir jvmTmpPath 

