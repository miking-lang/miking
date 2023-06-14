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
include "mexpr/shallow-patterns.mc"
include "stringid.mc"
include "mexpr/record.mc"

let isConstSeq_ = use MExprAst in
    lam seq.
        foldl
            (lam acc. lam expr.
                match acc with true then
                    match expr with TmConst _ then
                        true
                    else
                        false
                else
                    false)
            true
            seq

lang MExprJVMCompile = MExprAst + JVMAst + MExprPrettyPrint + MExprCmp

    type JVMEnv = {
        bytecode : [Bytecode],
        vars : Map Name Int,
        fieldVars : Map Name Field,
        localVars : Int, -- number of local vars on the JVM
        classes : [Class],
        name : String,
        nextClass : String,
        recordMap : Map Name (Map SID Int),
        adtTags : Map Name (String, Int),
        globalFuncMap : Map Name String,
        constSeqBC : [Function]
    }

    -- go through AST and translate to JVM bytecode

    sem toJSONExpr : JVMEnv -> Expr -> JVMEnv
    sem toJSONExpr env =
    | TmSeq { tms = tms } ->
        let vb = "scala/collection/immutable/VectorBuilder" in
        match isConstSeq_ tms with true then
            let funcName = createName_ "mkConstSeq" in
            let bc = foldl
                    (lam acc. lam expr.
                        let exprEnv = toJSONExpr { acc with bytecode = snoc acc.bytecode dup_ } expr in
                        { exprEnv with bytecode = concat exprEnv.bytecode [checkcast_ object_T, invokevirtual_ vb "$plus$eq" "(Ljava/lang/Object;)Lscala/collection/mutable/Growable;", pop_] })
                    { env with bytecode = [new_ vb, dup_, invokespecial_ vb "<init>" "()V"] }
                    tms in
            let seqFunc = createFunction funcName "()Lscala/collection/immutable/Vector;" (concat bc.bytecode [invokevirtual_ vb "result" "()Lscala/collection/immutable/Vector;", areturn_]) in
            { env with
                    bytecode = foldl concat
                                env.bytecode
                                [initClass_ "SeqClass",
                                [invokevirtual_ (concat pkg_ "SeqClass") funcName "()Lscala/collection/immutable/Vector;"]],
                    constSeqBC = snoc env.constSeqBC seqFunc }
        else
            let e = foldl
                    (lam acc. lam expr.
                        let exprEnv = toJSONExpr { acc with bytecode = snoc acc.bytecode dup_ } expr in
                        { exprEnv with bytecode = concat exprEnv.bytecode [checkcast_ object_T, invokevirtual_ vb "$plus$eq" "(Ljava/lang/Object;)Lscala/collection/mutable/Growable;", pop_] })
                    { env with bytecode = concat env.bytecode [new_ vb, dup_, invokespecial_ vb "<init>" "()V"] }
                    tms in
            { e with bytecode = snoc e.bytecode (invokevirtual_ vb "result" "()Lscala/collection/immutable/Vector;") }
    | TmConst { val = val, ty = ty } ->
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
        else match val with CArgv _ then
            [getstatic_ (concat pkg_ "Main") "argv" "Lscala/collection/immutable/Vector;"]
        else match val with CAddi _ then
            initClass_ "Addi_INTRINSIC$"
        else match val with CSubi _ then
            initClass_ "Subi_INTRINSIC$"
        else match val with CMuli _ then
            initClass_ "Muli_INTRINSIC$"
        else match val with CModi _ then
            initClass_ "Modi_INTRINSIC$"
        else match val with CDivi _ then
            initClass_ "Divi_INTRINSIC$"
        else match val with CAddf _ then
            initClass_ "Addf_INTRINSIC$"
        else match val with CSubf _ then
            initClass_ "Subf_INTRINSIC$"
        else match val with CMulf _ then
            initClass_ "Mulf_INTRINSIC$"
        else match val with CDivf _ then
            initClass_ "Divf_INTRINSIC$"
        else match val with CEqi _ then
            initClass_ "Eqi_INTRINSIC$"
        else match val with CNegi _ then
            initClass_ "Negi_INTRINSIC"
        else match val with CLti _ then
            initClass_ "Lti_INTRINSIC$"
        else match val with CGti _ then
            initClass_ "Gti_INTRINSIC$"
        else match val with CLeqi _ then
            initClass_ "Leqi_INTRINSIC$"
        else match val with CGeqi _ then
            initClass_ "Geqi_INTRINSIC$"
        else match val with CEqf _ then
            initClass_ "Eqf_INTRINSIC$"
        else match val with CNegf _ then
            initClass_ "Negf_INTRINSIC"
        else match val with CLtf _ then
            initClass_ "Ltf_INTRINSIC$"
        else match val with CGtf _ then
            initClass_ "Gtf_INTRINSIC$"
        else match val with CLeqf _ then
            initClass_ "Leqf_INTRINSIC$"
        else match val with CGeqf _ then
            initClass_ "Geqf_INTRINSIC$"
        else match val with CSlli _ then
            initClass_ "Slli_INTRINSIC$"
        else match val with CSrli _ then
            initClass_ "Srli_INTRINSIC$"
        else match val with CSrai _ then
            initClass_ "Srai_INTRINSIC$"
        else match val with CNeqi _ then
            initClass_ "Neqi_INTRINSIC$"
        else match val with CNeqf _ then
            initClass_ "Neqf_INTRINSIC$"
        else match val with CEqc _ then
            initClass_ "Eqc_INTRINSIC$"
        else match val with CPrint _ then
            initClass_ "Print_INTRINSIC"
        else match val with CRandIntU _ then
            initClass_ "Rand_INTRINSIC$"
        else match val with CRandSetSeed _ then
            initClass_ "RandSetSeed_INTRINSIC"
        else match val with CFloorfi _ then
            initClass_ "Floorfi_INTRINSIC"
        else match val with CCeilfi _ then
            initClass_ "Ceilfi_INTRINSIC"
        else match val with CRoundfi _ then
            initClass_ "Roundfi_INTRINSIC"
        else match val with CInt2float _ then
            initClass_ "Int2float_INTRINSIC"
        else match val with CChar2Int _ then
            initClass_ "Char2Int_INTRINSIC"
        else match val with CInt2Char _ then
            initClass_ "Int2Char_INTRINSIC"
        else match val with CStringIsFloat _ then
            initClass_ "StringIsFloat_INTRINSIC"
        else match val with CString2float _ then
            initClass_ "String2Float_INTRINSIC"
        else match val with CGensym _ then
            initClass_ "GenSymIntrinsic_INTRINSIC"
        else match val with CSym2hash _ then
            initClass_ "Sym2Hash_INTRINSIC"
        else match val with CReverse _ then
            initClass_ "Reverse_INTRINSIC"
        else match val with CHead _ then
            initClass_ "Head_INTRINSIC"
        else match val with CTail _ then
            initClass_ "Tail_INTRINSIC"
        else match val with CLength _ then
            initClass_ "Length_INTRINSIC"
        else match val with CFileExists _ then
            initClass_ "FileExists_INTRINSIC"
        else match val with CFileRead _ then
            initClass_ "FileRead_INTRINSIC"
        else match val with CFloat2string _ then
            initClass_ "Float2String_INTRINSIC"
        else match val with CExit _ then
            initClass_ "Exit_INTRINSIC"
        else match val with CPrintError _ then
            initClass_ "PrintError_INTRINSIC"
        else match val with CFileDelete _ then
            initClass_ "FileDelete_INTRINSIC"
        else match val with CError _ then
            initClass_ "Error_INTRINSIC"
        else match val with CFlushStderr _ then
            initClass_ "FlushStderr_INTRINSIC"
        else match val with CFlushStdout _ then
            initClass_ "FlushStdout_INTRINSIC"
        else match val with CCommand _ then
            initClass_ "Command_INTRINSIC"
        else match val with CSleepMs _ then
            initClass_ "SleepMs_INTRINSIC"
        else match val with CWallTimeMs _ then
            initClass_ "WallTimeMs_INTRINSIC"
        else match val with CRef _ then
            initClass_ "RefIntrinsic_INTRINSIC"
        else match val with CDeRef _ then
            initClass_ "DeRef_INTRINSIC"
        else match val with CEqsym _ then
            initClass_ "Eqsym_INTRINSIC$"
        else match val with CCons _ then
            initClass_ "Cons_INTRINSIC$"
        else match val with CGet _ then
            initClass_ "Get_INTRINSIC$"
        else match val with CSnoc _ then
            initClass_ "Snoc_INTRINSIC$"
        else match val with CConcat _ then
            initClass_ "Concat_INTRINSIC$"
        else match val with CMap _ then
            initClass_ "Map_INTRINSIC$"
        else match val with CMapi _ then
            initClass_ "Mapi_INTRINSIC$"
        else match val with CIter _ then
            initClass_ "Iter_INTRINSIC$"
        else match val with CIteri _ then
            initClass_ "Iteri_INTRINSIC$"
        else match val with CReadLine _ then
            initClass_ "ReadLine_INTRINSIC"
        else match val with CIsList _ then
            initClass_ "IsList_INTRINSIC"
        else match val with CIsRope _ then
            initClass_ "IsRope_INTRINSIC"
        else match val with CSplitAt _ then
            initClass_ "SplitAt_INTRINSIC$"
        else match val with CCreate _ then
            initClass_ "Create_INTRINSIC$"
        else match val with CCreateList _ then
            initClass_ "CreateList_INTRINSIC$"
        else match val with CCreateRope _ then
            initClass_ "CreateRope_INTRINSIC$"
        else match val with CFoldl _ then
            initClass_ "Foldl_INTRINSIC$"
        else match val with CFoldr _ then
            initClass_ "Foldr_INTRINSIC$"
        else match val with CSubsequence _ then
            initClass_ "SubSequence_INTRINSIC$"
        else match val with CNull _ then
            initClass_ "Null_INTRINSIC"
        else match val with CModRef _ then
            initClass_ "ModRef_INTRINSIC$"
        else match val with CFileWrite _ then
            initClass_ "FileWrite_INTRINSIC$"
        else match val with CDPrint _ then
            initClass_ "DPrint_INTRINSIC"
        else match val with CSet _ then
            initClass_ "Set_INTRINSIC$"
        else never) in
        { env with bytecode = concat env.bytecode bc }
    | TmApp { lhs = lhs, rhs = rhs, ty = ty } ->
        let arg = toJSONExpr { env with bytecode = [], classes = [], constSeqBC = [] } rhs in
        let fun = toJSONExpr env lhs in
        { fun with
            bytecode = foldl concat fun.bytecode
                [arg.bytecode,
                [checkcast_ object_T],
                [invokeinterface_ (concat pkg_ "Function") "apply" "(Ljava/lang/Object;)Ljava/lang/Object;"]],
                classes = concat fun.classes arg.classes,
                constSeqBC = concat fun.constSeqBC arg.constSeqBC }
    | TmLet { ident = ident, body = body, inexpr = inexpr, tyBody = tyBody } ->
        let funcmap = (match body with TmLam _ then
                            mapInsert ident env.nextClass env.globalFuncMap
                        else match tyBody with TyArrow _ then 
                            mapInsert ident env.nextClass env.globalFuncMap
                        else
                            env.globalFuncMap) in
        let b = toJSONExpr env body in
        toJSONExpr { b with
                        bytecode = snoc b.bytecode (astore_ env.localVars),
                        localVars = addi 1 env.localVars,
                        vars = mapInsert ident env.localVars env.vars,
                        globalFuncMap = funcmap } inexpr
    | TmLam { ident = ident, body = body } ->
        let className = env.nextClass in
        let newField = (createField (nameGetStr ident) object_LT) in
        let nextClass = createName_ "Func" in
        let bodyEnv = toJSONExpr
            { env with
                bytecode = [],
                name = className,
                nextClass = nextClass,
                fieldVars = mapInsert ident newField env.fieldVars,
                vars = mapInsert ident 1 (mapEmpty nameCmp),
                localVars = 2 } body in
        let fields = map (lam x. x.1) (mapToSeq env.fieldVars) in
        match body with TmLam _ then
            let putfields = join (mapi (lam i. lam x. [aload_ 0, getfield_ (concat pkg_ className) (getNameField x) object_LT, putfield_ (concat pkg_ nextClass) (getNameField x) object_LT]) fields) in
            let dups = map (lam x. dup_) fields in
            let apply = apply_ (foldl concat bodyEnv.bytecode [dups, [dup_, aload_ 1, putfield_ (concat pkg_ nextClass) (nameGetStr ident) object_LT], putfields]) in
            let funcClass = createClass className (concat pkg_ "Function") (snoc fields newField) defaultConstructor [apply] in
            { env with
                classes = snoc bodyEnv.classes funcClass,
                constSeqBC = bodyEnv.constSeqBC,
                bytecode = foldl concat env.bytecode [initClass_ className],
                nextClass = bodyEnv.nextClass }
        else
            let apply = apply_ bodyEnv.bytecode in
            let funcClass = createClass className (concat pkg_ "Function") fields defaultConstructor [apply] in
            { env with
                classes = snoc bodyEnv.classes funcClass,
                constSeqBC = bodyEnv.constSeqBC,
               bytecode = foldl concat env.bytecode [initClass_ className],
                fieldVars = mapEmpty nameCmp,
                nextClass = bodyEnv.nextClass }
    | TmVar { ident = ident } ->
        let store = (match mapLookup ident env.vars with Some i then
            [aload_ i]
        else match mapLookup ident env.fieldVars with Some field then
            -- do fieldlookup
            [aload_ 0, getfield_ (concat pkg_ env.name) (getNameField field) "Ljava/lang/Object;"]
        else match mapLookup ident env.globalFuncMap with Some global then
            (initClass_ global)
        else
            (print (join ["No identifier! ", nameGetStr ident, "\n"]));
            []) in
        { env with bytecode = concat env.bytecode store }
    | TmMatch { target = target, pat = pat, thn = thn, els = els } ->
        let targetEnv = toJSONExpr env target in
        jvmPat targetEnv (tyTm target) thn els pat
    | TmRecord { bindings = bindings, ty = ty } ->
        let realTy = unwrapType ty in
        match realTy with TyCon { ident = name } then
            let len = length (mapToSeq bindings) in
            match mapLookup name env.recordMap with Some translation then
                let insertBytecode =
                    foldl
                    (lam e. lam tup.
                        let sid = tup.0 in
                        let i = tup.1 in
                        let expr = (match mapLookup sid bindings with Some e then e else never) in
                        let exprEnv = toJSONExpr { e with bytecode = concat e.bytecode [dup_, ldcInt_ i] } expr in
                        { e with bytecode = snoc exprEnv.bytecode aastore_, classes = concat e.classes exprEnv.classes, constSeqBC = exprEnv.constSeqBC })
                    { env with bytecode = [], classes = [], constSeqBC = [] }
                    (mapToSeq translation) in
                let recordBytecode = concat [ldcInt_ len, anewarray_ object_T] insertBytecode.bytecode in
                { env with
                    bytecode = concat env.bytecode (wrapRecord_ recordBytecode),
                    classes = concat env.classes insertBytecode.classes,
                    constSeqBC = concat env.constSeqBC insertBytecode.constSeqBC,
                    recordMap = mapUnion env.recordMap insertBytecode.recordMap }
            else never
        else
            { env with
                bytecode = concat env.bytecode nothing_ }
    | TmRecLets { bindings = bindings, inexpr = inexpr } ->
        let e = foldl
                (lam acc. lam expr.
                    match expr with { ident = ident, body = body } then
                        match body with TmLam _ then
                            (mapInsert ident acc.1 acc.0, createName_ "Func", mapInsert ident acc.1 acc.2)
                        else
                            acc
                    else never)
                (env.globalFuncMap, env.nextClass, mapEmpty nameCmp)
                bindings in
        let nextClass = e.1 in
        let funcMap = e.0 in
        let funcBindings = e.2 in
        let b = foldl
                    (lam acc. lam el.
                        match el with { ident = ident, body = body } then
                            match body with TmLam _ then
                                match mapLookup ident funcBindings with Some funcName then
                                    let bodyEnv = toJSONExpr { acc with nextClass = funcName, fieldVars = mapEmpty nameCmp } body in
                                    { bodyEnv with bytecode = subsequence bodyEnv.bytecode 0 (subi (length bodyEnv.bytecode) 3) } 
                                else never
                            else
                                let bodyEnv = toJSONExpr acc body in
                                { bodyEnv with
                                        bytecode = concat acc.bytecode [astore_ acc.localVars],
                                        localVars = addi acc.localVars 1,
                                        fieldVars = mapEmpty nameCmp,
                                        vars = mapInsert ident acc.localVars acc.vars }
                        else
                            never)
                    { env with
                        globalFuncMap = funcMap }
                    bindings in
        toJSONExpr { b with fieldVars = mapEmpty nameCmp } inexpr
    | TmRecordUpdate { rec = rec, key = key, value = value, ty = ty } ->
        let realTy = unwrapType ty in
        let name = (match realTy with TyCon { ident = ident } then ident else never) in
        let mapping = (match mapLookup name env.recordMap with Some map then map else never) in
        let inew = (match mapLookup key mapping with Some i then i else never) in
        let valueEnv = toJSONExpr { env with bytecode = [], classes = [], constSeqBC = [] } value in
        let recEnv = toJSONExpr env rec in
        let arr = env.localVars in
        let len = addi env.localVars 1 in 
        let newarr = addi env.localVars 2 in 
        let i = addi env.localVars 3 in 
        let startLabel = createName_ "start" in
        let endLabel = createName_ "end" in
        { recEnv with
            bytecode = foldl concat
                recEnv.bytecode
                [unwrapRecord_,
                [dup_,
                astore_ arr,
                arraylength_, 
                dup_,
                istore_ len,
                anewarray_ object_T,
                astore_ newarr,
                ldcInt_ 0,
                istore_ i,
                label_ startLabel,
                iload_ i,
                iload_ len,
                ificmpge_ endLabel,
                aload_ newarr,
                iload_ i,
                aload_ arr,
                iload_ i,
                aaload_,
                aastore_,
                iload_ i,
                ldcInt_ 1,
                iadd_,
                istore_ i,
                goto_ startLabel,
                label_ endLabel,
                aload_ newarr,
                ldcInt_ inew],
                valueEnv.bytecode,
                [aastore_],
                wrapRecord_ [aload_ newarr]],
            classes = concat recEnv.classes valueEnv.classes,
            constSeqBC = concat recEnv.constSeqBC valueEnv.constSeqBC }
    | TmType _ -> (error "TmType: Should be gone"); env
    | TmConDef _ -> (error "TmConDef: Should be gone"); env
    | TmConApp { ident = ident, body = body } ->
        let constructor = nameGetStr ident in
        let bodyEnv = toJSONExpr { env with bytecode = [], classes = [], constSeqBC = [] } body in
        { env with
            bytecode = foldl concat
                env.bytecode
                [initClass_ constructor,
                [dup_],
                bodyEnv.bytecode,
                [checkcast_ object_T, putfield_ (concat pkg_ constructor) "value" object_LT]],
            classes = concat bodyEnv.classes env.classes,
            constSeqBC = concat bodyEnv.constSeqBC env.constSeqBC,
            recordMap = mapUnion env.recordMap bodyEnv.recordMap }
    | TmUtest _ -> (error "TmUtest"); env
    | TmNever _ -> { env with bytecode = foldl concat
                            env.bytecode
                            [[getstatic_ "java/lang/System" "err" "Ljava/io/PrintStream;",
                            ldcString_ "Never Reached!",
                            invokevirtual_ "java/io/PrintStream" "print" "(Ljava/lang/String;)V",
                            ldcInt_ 1,
                            invokestatic_ "java/lang/System" "exit" "(I)V"],
                            nothing_] }
    | TmExt _ -> (error "TmExt"); env
    | a ->
        (error "unknown expr\n");
        env

    sem jvmPat : JVMEnv -> Type -> Expr -> Expr -> Pat -> JVMEnv
    sem jvmPat env targetty thn els =
    | PatInt { val = val } ->
        let thnEnv = toJSONExpr { env with bytecode = [], classes = [], constSeqBC = [] } thn in
        let elsEnv = toJSONExpr { env with bytecode = [], classes = [], constSeqBC = [] } els in
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
            classes = foldl concat env.classes [thnEnv.classes, elsEnv.classes],
            constSeqBC = foldl concat env.constSeqBC [thnEnv.constSeqBC, elsEnv.constSeqBC] }
    | PatRecord { bindings = bindings, ty = ty } ->
        let realTy = unwrapType ty in
        match realTy with TyCon _ then
            let name = (match realTy with TyCon { ident = ident } then ident else never) in
            match eqi (cmpType targetty ty) 0 with true then
                match mapLookup name env.recordMap with Some r then
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
                                    else -- Wildcard!
                                        e
                                else never)
                            env
                            (mapToSeq bindings) in
                    toJSONExpr { patEnv with bytecode = snoc patEnv.bytecode pop_ } thn
                else never
            else
                toJSONExpr env els
        else -- match () with () 
            toJSONExpr { env with bytecode = snoc env.bytecode pop_ } thn
    | PatBool { val = val } ->
        let thnEnv = toJSONExpr { env with bytecode = [], classes = [], constSeqBC = [] } thn in
        let elsEnv = toJSONExpr { env with bytecode = [], classes = [], constSeqBC = [] } els in
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
            classes = foldl concat env.classes [thnEnv.classes, elsEnv.classes],
            constSeqBC = foldl concat env.constSeqBC [thnEnv.constSeqBC, elsEnv.constSeqBC] }
    | PatChar { val = val } ->
        let thnEnv = toJSONExpr { env with bytecode = [], classes = [], constSeqBC = [] } thn in
        let elsEnv = toJSONExpr { env with bytecode = [], classes = [], constSeqBC = [] } els in
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
            classes = foldl concat env.classes [thnEnv.classes, elsEnv.classes],
            constSeqBC = foldl concat env.constSeqBC [thnEnv.constSeqBC, elsEnv.constSeqBC] }
    | PatCon { ident = ident, subpat = subpat } ->
        let typeTag = (match mapLookup ident env.adtTags with Some tup then tup else never) in
        let t = typeTag.0 in
        let tag = typeTag.1 in
        let elsLabel = createName_ "els" in
        let endLabel = createName_ "end" in
        let adtClassName = (concat pkg_ (nameGetStr ident)) in
        match subpat with PatNamed { ident = id } then
            match id with PName name then
                let patEnv = { env with
                                bytecode = foldl concat
                                    env.bytecode
                                    [[dup_,
                                    instanceof_ (concat pkg_ t),
                                    ifeq_ elsLabel, -- jump if 0
                                    dup_,
                                    checkcast_ (concat pkg_ t),
                                    invokeinterface_ (concat pkg_ t) "getTag" "()I",
                                    ldcInt_ tag,
                                    ificmpne_ elsLabel,
                                    checkcast_ adtClassName,
                                    getfield_ adtClassName "value" object_LT,
                                    astore_ env.localVars]],
                                localVars = addi 1 env.localVars,
                                vars = mapInsert name env.localVars env.vars } in
                let thnEnv = toJSONExpr patEnv thn in
                let elsEnv = toJSONExpr { patEnv with bytecode = [], classes = [], constSeqBC = [] } els in
                { thnEnv with
                    bytecode = foldl concat
                        thnEnv.bytecode
                        [[goto_ endLabel,
                        label_ elsLabel,
                        pop_],
                        elsEnv.bytecode,
                        [label_ endLabel]],
                    classes = concat thnEnv.classes elsEnv.classes,
                    constSeqBC = concat thnEnv.constSeqBC elsEnv.constSeqBC }
            else -- wildcard
                let patEnv = { env with
                                bytecode = foldl concat
                                    env.bytecode
                                    [[dup_,
                                    instanceof_ (concat pkg_ t),
                                    ifeq_ elsLabel, -- jump if 0
                                    dup_,
                                    checkcast_ (concat pkg_ t),
                                    invokeinterface_ (concat pkg_ t) "getTag" "()I",
                                    ldcInt_ tag,
                                    ificmpne_ elsLabel,
                                    pop_]] } in
                let thnEnv = toJSONExpr patEnv thn in
                let elsEnv = toJSONExpr { patEnv with bytecode = [], classes = [], constSeqBC = [] } els in
                { thnEnv with
                    bytecode = foldl concat
                        thnEnv.bytecode
                        [[goto_ endLabel,
                        label_ elsLabel,
                        pop_],
                        elsEnv.bytecode,
                        [label_ endLabel]],
                    classes = concat thnEnv.classes elsEnv.classes,
                    constSeqBC = concat thnEnv.constSeqBC elsEnv.constSeqBC }
        else never
    | PatSeqTot { pats = pats } ->
        let endLabel = createName_ "end" in
        let elsLabel = createName_ "els" in
        let len = length pats in
        let patEnv = foldli
            (lam acc. lam i. lam pat.
                match pat with PatNamed { ident = ident } then
                    match ident with PName name then
                        { acc with
                            bytecode = concat
                                acc.bytecode
                                [dup_,
                                checkcast_ seq_T,
                                ldcInt_ i,
                                invokevirtual_ seq_T "apply" (methodtype_T "I" object_LT),
                                astore_ acc.localVars],
                            localVars = addi 1 acc.localVars,
                            vars = mapInsert name acc.localVars acc.vars }
                    else never
                else never)
            { env with
                bytecode = concat
                    env.bytecode
                    [dup_,
                    checkcast_ seq_T,
                    invokevirtual_ seq_T "length" "()I",
                    ldcInt_ len,
                    ificmpne_ elsLabel] }
            pats in
        let thnEnv = toJSONExpr { patEnv with bytecode = snoc patEnv.bytecode pop_ } thn in
        let elsEnv = toJSONExpr { patEnv with bytecode = [], classes = [], constSeqBC = [] } els in
        { thnEnv with
            bytecode = foldl concat
                thnEnv.bytecode
                [[goto_ endLabel,
                label_ elsLabel,
                pop_],
                elsEnv.bytecode,
                [label_ endLabel]],
            classes = concat thnEnv.classes elsEnv.classes,
            constSeqBC = concat thnEnv.constSeqBC elsEnv.constSeqBC }
    | PatSeqEdge { prefix = prefix, middle = middle, postfix = postfix } ->
        -- calculate length less
        let endLabel = createName_ "end" in
        let elsLabel = createName_ "els" in
        let len = addi (length prefix) (length postfix) in
        let prefixEnv = foldli
            (lam acc. lam i. lam pat.
                match pat with PatNamed { ident = ident } then
                    match ident with PName name then
                        { acc with
                            bytecode = concat
                                acc.bytecode
                                [dup_,
                                checkcast_ seq_T,
                                ldcInt_ i,
                                invokevirtual_ seq_T "apply" (methodtype_T "I" object_LT),
                                astore_ acc.localVars],
                            localVars = addi 1 acc.localVars,
                            vars = mapInsert name acc.localVars acc.vars }
                    else -- wildcard
                        acc
                else never)
            { env with
                bytecode = concat
                    env.bytecode
                    [dup_,
                    checkcast_ seq_T,
                    invokevirtual_ seq_T "length" "()I",
                    ldcInt_ len,
                    ificmplt_ elsLabel] }
            prefix in
        let middleEnv =
            (match middle with PName name then
                { prefixEnv with
                    bytecode = concat
                        prefixEnv.bytecode
                        [dup_,
                        checkcast_ seq_T,
                        dup_,
                        astore_ prefixEnv.localVars,
                        ldcInt_ (length prefix),
                        aload_ prefixEnv.localVars,
                        invokevirtual_ seq_T "length" "()I",
                        ldcInt_ (length postfix),
                        isub_,
                        invokevirtual_ seq_T "slice" (methodtype_T "II" object_LT),
                        astore_ prefixEnv.localVars],
                    localVars = addi 1 prefixEnv.localVars,
                    vars = mapInsert name prefixEnv.localVars prefixEnv.vars }
            else -- wildcard
                prefixEnv) in
        let postfixEnv = foldli
            (lam acc. lam i. lam pat.
                match pat with PatNamed { ident = ident } then
                    match ident with PName name then
                        { acc with
                            bytecode = concat
                                acc.bytecode
                                [dup_,
                                checkcast_ seq_T,
                                dup_,
                                invokevirtual_ seq_T "length" "()I",
                                ldcInt_ (subi (length postfix) i),
                                isub_,
                                invokevirtual_ seq_T "apply" (methodtype_T "I" object_LT),
                                astore_ acc.localVars],
                            localVars = addi 1 acc.localVars,
                            vars = mapInsert name acc.localVars acc.vars }
                    else -- wildcard
                        acc
                else never)
            middleEnv
            postfix in
        let thnEnv = toJSONExpr { postfixEnv with bytecode = snoc postfixEnv.bytecode pop_ } thn in
        let elsEnv = toJSONExpr { postfixEnv with bytecode = [], classes = [], constSeqBC = [] } els in
        { thnEnv with
            bytecode = foldl concat
                thnEnv.bytecode
                [[goto_ endLabel,
                label_ elsLabel,
                pop_],
                elsEnv.bytecode,
                [label_ endLabel]],
            classes = concat thnEnv.classes elsEnv.classes,
            constSeqBC = concat thnEnv.constSeqBC elsEnv.constSeqBC }
    | PatNamed { ident = ident } ->
        match ident with PName name then
            toJSONExpr
                { env with
                    bytecode = snoc env.bytecode (astore_ env.localVars),
                    vars = mapInsert name env.localVars env.vars,
                    localVars = addi 1 env.localVars }
                thn
        else
            toJSONExpr { env with bytecode = snoc env.bytecode pop_ } thn
    | PatAnd _ ->
        (error "Unknown PatAnd");
        env
    | PatOr _ ->
        (error "Unknown PatOr");
        env
    | PatNot _ ->
        (error "Unknown PatNot");
        env
    | a ->
        (error "Unknown Pat");
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

lang CombinedLang = MExprLowerNestedPatterns + MExprPrettyPrint + MExprJVMCompile + MExprLambdaLift + MExprTypeCheck end

let collectADTTypes = lam tlMapping.
    use MExprJVMCompile in
    foldl (lam acc. lam tup.
            let t = tup.1 in
            match t with TyVariant { constrs = constrs } then -- ADT
                let classes = acc.1 in
                let interfaces = acc.0 in
                let name = concat (nameGetStr tup.0) "_TYPE_INTERFACE" in
                let interf = createInterface name [] [createFunction "getTag" "()I" []] in
                let constrClasses = foldli (lam acc. lam i. lam tup.
                                        let interfName = acc.0 in
                                        let tagLookup = mapInsert tup.0 (interfName, i) acc.2 in
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


let collectRecords = lam records.
    let recordMap = foldl
        (lam recordMap. lam tup.
            let name = tup.1 in
            let sidTypeMap = tup.0 in
            let sidList = map (lam tup. tup.0) (mapToSeq sidTypeMap) in
            let orderedSidList = recordOrderedLabels sidList in
            let mapping =
                (foldli
                    (lam map. lam i. lam sid.
                        mapInsert sid i map)
                    (mapEmpty cmpSID)
                    orderedSidList) in
            mapInsert name mapping recordMap)
        (mapEmpty nameCmp)
        (mapToSeq records) in
    recordMap

let compileJVMEnv = lam ast.
    use MExprJVMCompile in
    use MExprTypeLift in

    -- using typeLiftExpr to get all record keys
    let emptyTypeLiftEnv : TypeLiftEnv = {
      typeEnv = [],
      records = mapEmpty (mapCmp cmpType),
      seqs = mapEmpty cmpType,
      tensors = mapEmpty cmpType,
      variants = mapEmpty nameCmp
    } in

    let tl = (match typeLiftExpr emptyTypeLiftEnv ast with (tlEnv, t) then
                let typeEnv = _replaceVariantNamesInTypeEnv tlEnv in
                (typeEnv, t, tlEnv.records)
            else never) in
    let recordMap = collectRecords tl.2 in
    let adt = collectADTTypes tl.0 in
    let tlAst = tl.1 in
    let objToObj = createInterface "Function" [] [createFunction "apply" "(Ljava/lang/Object;)Ljava/lang/Object;" []] in
    let env = {
            bytecode = setArgvBC_,
            vars = mapEmpty nameCmp,
            localVars = 1,
            classes = [],
            fieldVars = mapEmpty nameCmp,
            name = "Main",
            nextClass = createName_ "Func",
            recordMap = recordMap,
            adtTags = adt.2,
            globalFuncMap = mapEmpty nameCmp,
            constSeqBC = [] } in
    let compiledEnv = (toJSONExpr env tlAst) in
    let bytecode = concat compiledEnv.bytecode [pop_, return_] in
    --let bytecode = concat compiledEnv.bytecode [astore_ 0, getstatic_ "java/lang/System" "out" "Ljava/io/PrintStream;", aload_ 0, invokevirtual_ "java/io/PrintStream" "print" "(Ljava/lang/Object;)V", return_] in
    let mainFunc = createFunction "main" "([Ljava/lang/String;)V" bytecode in
    let constClasses = foldl concat constClassList_ [adt.1, [constSeqClass_ compiledEnv.constSeqBC]] in
    let prog = createProg pkg_ (snoc (concat compiledEnv.classes constClasses) (createClass "Main" "" [] defaultConstructor [mainFunc])) (snoc adt.0 objToObj) in
    prog

lang MExprJVMCompileLang = MExprJVMCompile + MExprLambdaLift + MExprTypeCheck + MExprPrettyPrint end

let getJarFiles = lam tempDir.
    (sysRunCommand ["curl", "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-core/2.14.2/jackson-core-2.14.2.jar", "--output", (concat tempDir "jackson-core-2.14.2.jar")] "" ".");
    (sysRunCommand ["curl", "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-databind/2.14.2/jackson-databind-2.14.2.jar", "--output", (concat tempDir "jackson-databind-2.14.2.jar")] "" ".");
    (sysRunCommand ["curl", "https://repo1.maven.org/maven2/com/fasterxml/jackson/core/jackson-annotations/2.14.2/jackson-annotations-2.14.2.jar", "--output", (concat tempDir "jackson-annotations-2.14.2.jar")] "" ".");
    (sysRunCommand ["curl", "https://repo1.maven.org/maven2/org/ow2/asm/asm/9.4/asm-9.4.jar", "--output", (concat tempDir "asm-9.4.jar")] "" ".");
    (sysRunCommand ["curl", "https://repo1.maven.org/maven2/org/scala-lang/scala-library/2.13.10/scala-library-2.13.10.jar", "--output", (concat tempDir "scala-library-2.13.10.jar")] "" ".");
    ()

let compileJava = lam outDir. lam jarPath.
    let cfmClass = (concat stdlibLoc "/jvm/codegen/ClassfileMaker.java") in
    let jsonParserClass = (concat stdlibLoc "/jvm/codegen/Parser.java") in
    let cwfClass = (concat stdlibLoc "/jvm/codegen/ClassWriterF.java") in
    let classpath = (join [jarPath, "jackson-annotations-2.14.2.jar:", jarPath, "jackson-core-2.14.2.jar:", jarPath, "jackson-databind-2.14.2.jar:", jarPath, "asm-9.4.jar"]) in
    (sysRunCommand ["javac", "-cp", classpath, cfmClass, jsonParserClass, cwfClass, "-d", outDir] "" ".");
    ()


let prepare = lam path.
    match sysCommandExists "java" with false then 
        error "java needs to be installed\n"
        ()
    else
        (match sysFileExists (concat path "jar/") with true then
            ()
        else
            (sysRunCommand ["mkdir", (concat path "jar/")] "" ".");
            (getJarFiles (concat path "jar/"));
            ());
        (match sysFileExists (concat path "/out") with true then 
            ()
        else 
            (sysRunCommand ["mkdir", (concat path "out/")] "" ".");
            (compileJava (concat path "out/") (concat path "jar/"));
            ());
        ()

let trimSourcePath = lam path.
    let path = subsequence path 0 (subi (length path) 3) in 
    match (foldl (lam acc. lam letter. match acc with true then true else eqc letter '/') false path) with true then
        (foldli 
            (lam acc. lam i. lam letter. 
                match acc.1 with true then 
                    acc 
                else
                    match eqc letter '/' with true then 
                    (subsequence path (subi (length path) i) (subi (length path) 3), true) 
                    else 
                    acc) 
            (path, false)
            (reverse path)).0
    else 
        path

let compileMCoreToJVM = lam ast. lam sourcePath. lam options.
    use MExprJVMCompileLang in
    let typeFix = typeCheck ast in -- types dissapear in pattern lowering
    let liftedAst = liftLambdas typeFix in
    let jvmProgram = compileJVMEnv liftedAst in
    let path = concat stdlibLoc "/jvm/" in
    let json = sysTempFileMake () in
    writeFile json (toStringProg jvmProgram);
    (prepare path);
    let jarPath = concat path "jar/" in 
    let classpath = (join [":", jarPath, "jackson-annotations-2.14.2.jar:", jarPath, "jackson-core-2.14.2.jar:", jarPath, "jackson-databind-2.14.2.jar:", jarPath, "asm-9.4.jar"]) in
    (sysRunCommand ["java", "-cp", (join [path, "out/", classpath]), "codegen/Parser", json] "" ".");
    sysDeleteDir json;
    --create run script
    let outputPath = (match options.output with Some path then
                            (sysRunCommand ["mkdir", path] "" ".");
                            (sysRunCommand ["mv", pkg_, join [path, "/", pkg_]] "" ".");
                            concat path "/"
                        else "") in
    (createRunScript_ (concat outputPath (trimSourcePath sourcePath)));
    "pkg/"

