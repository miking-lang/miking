include "jvm/ast.mc"


let pkg_ = "pkg/"

-- Instructions --

let aload_ = use JVMAst in 
    lam i. createBInt "ALOAD" i

let astore_ = use JVMAst in
    lam i. createBInt "ASTORE" i

let lload_ = use JVMAst in
    lam i. createBInt "LLOAD" i

let lstore_ = use JVMAst in
    lam i. createBInt "LSTORE" i

let ldcInt_ = use JVMAst in
    lam i. createBInt "LDC" i

let ldcString_ = use JVMAst in
    lam s. createBString "LDC" s

-- loads double on JVM
let ldcFloat_ = use JVMAst in
    lam i. createBFloat "LDC" i

let ldcLong_ = use JVMAst in
    lam i. createBLong "LDC" i

let return_ = use JVMAst in
    createBEmpty "RETURN"

let ireturn_ = use JVMAst in
    createBEmpty "IRETURN"

let pop_ = use JVMAst in
    createBEmpty "POP"

let lshl_ = use JVMAst in
    createBEmpty "LSHL"

let lshr_ = use JVMAst in
    createBEmpty "LSHR"

let lushr_ = use JVMAst in
    createBEmpty "LUSHR"

let ladd_ = use JVMAst in
    createBEmpty "LADD"

let dadd_ = use JVMAst in
    createBEmpty "DADD"

let lsub_ = use JVMAst in 
    createBEmpty "LSUB"

let dsub_ = use JVMAst in 
    createBEmpty "DSUB"

let lmul_ = use JVMAst in 
    createBEmpty "LMUL"

let dmul_ = use JVMAst in 
    createBEmpty "DMUL"

let ldiv_ = use JVMAst in 
    createBEmpty "LDIV"

let ddiv_ = use JVMAst in 
    createBEmpty "DDIV"

let lrem_ = use JVMAst in 
    createBEmpty "LREM"

let lneg_ = use JVMAst in 
    createBEmpty "LNEG"

let dneg_ = use JVMAst in 
    createBEmpty "DNEG"

let dup_ = use JVMAst in
    createBEmpty "DUP"

let areturn_ = use JVMAst in
    createBEmpty "ARETURN"

let pop_ = use JVMAst in
    createBEmpty "POP"

let invokespecial_ = use JVMAst in
    lam owner. lam name. lam descriptor. createBApply "INVOKESPECIAL" owner name descriptor

let getstatic_ = use JVMAst in
    lam owner. lam name. lam descriptor. createBApply "GETSTATIC" owner name descriptor

let getfield_ = use JVMAst in
    lam owner. lam name. lam descriptor. createBApply "GETFIELD" owner name descriptor

let putfield_ = use JVMAst in
    lam owner. lam name. lam descriptor. createBApply "PUTFIELD" owner name descriptor

let invokevirtual_ = use JVMAst in 
    lam owner. lam name. lam descriptor. createBApply "INVOKEVIRTUAL" owner name descriptor

let invokeinterface_ = use JVMAst in
    lam owner. lam name. lam descriptor. createBApply "INVOKEINTERFACE" owner name descriptor

let invokestatic_ = use JVMAst in
    lam owner. lam name. lam descriptor. createBApply "INVOKESTATIC" owner name descriptor

let new_ = use JVMAst in
    lam name. createBString "NEW" name

let checkcast_ = use JVMAst in
    lam name. createBString "CHECKCAST" name

let ifeq_ = use JVMAst in 
    lam label. createBString "IFEQ" label

let ifne_ = use JVMAst in 
    lam label. createBString "IFNE" label

let iflt_ = use JVMAst in 
    lam label. createBString "IFLT" label   

let ifgt_ = use JVMAst in 
    lam label. createBString "IFGT" label   

let ifle_ = use JVMAst in 
    lam label. createBString "IFLE" label   

let ifge_ = use JVMAst in 
    lam label. createBString "IFGE" label  

let ificmpeq_ = use JVMAst in 
    lam label. createBString "IF_ICMPEQ" label

let ificmpne_ = use JVMAst in 
    lam label. createBString "IF_ICMPNE" label

let label_ = use JVMAst in 
    lam name. createBString "LABEL" name

let dcmp_= use JVMAst in
    createBEmpty "DCMP"

let lcmp_ = use JVMAst in 
    createBEmpty "LCMP"

let goto_ = use JVMAst in 
    lam label. createBString "GOTO" label

let anewarray_ = use JVMAst in 
    lam t. createBString "ANEWARRAY" t 

let aastore_ = use JVMAst in 
    createBEmpty "AASTORE"

let aaload_ = use JVMAst in
    createBEmpty "AALOAD"
---

let jvmTrue = 1

let jvmFalse = 0

---

let type_LT = lam x. join ["L", x, ";"]

let methodtype_T = lam arg. lam ret. join ["(", arg, ")", ret]

let object_T = "java/lang/Object"

let object_LT = type_LT object_T

let integer_T = "java/lang/Long" 

let integer_LT = type_LT integer_T

let float_T = "java/lang/Double" 

let float_LT = type_LT float_T

let boolean_T = "java/lang/Boolean"

let boolean_LT = type_LT boolean_T

let arraytype_ = lam at. concat "[" at

let char_T = concat pkg_ "CharWrap"

let char_LT = type_LT char_T

----

let initClass_ = 
    lam name. 
        [new_ (concat pkg_ name), dup_, invokespecial_ (concat pkg_ name) "<init>" "()V"]

let apply_ = use JVMAst in 
    lam bytecode.
    createFunction "apply" (methodtype_T object_LT object_LT) (concat bytecode [areturn_])

let wrapInteger_ = 
    [invokestatic_ integer_T "valueOf" (methodtype_T "J" integer_LT)]

let unwrapInteger_ = 
    [checkcast_ integer_T, invokevirtual_ integer_T "longValue" "()J"]

let wrapFloat_ = 
    [invokestatic_ float_T "valueOf" (methodtype_T "D" float_LT)]

let unwrapFloat_ = 
    [checkcast_ float_T, invokevirtual_ float_T "doubleValue" "()D"]

let wrapBoolean_ = 
    [invokestatic_ boolean_T "valueOf" (methodtype_T "Z" boolean_LT)]

let unwrapBoolean_ = 
    [checkcast_ boolean_T, invokevirtual_ boolean_T "booleanValue" "()Z"]

let wrapRecord_ =
    lam recordArray.
    foldl concat [new_ (concat pkg_ "Record")] [[dup_], recordArray, [invokespecial_ (concat pkg_ "Record") "<init>" (methodtype_T (arraytype_ object_LT) "V")]]

let unwrapRecord_ = 
    [getfield_ (concat pkg_ "Record") "array" (arraytype_ object_LT)]

let wrapChar_ = 
    lam char.
    foldl concat (initClass_ "CharWrap") [[dup_], char, [putfield_ char_T "charInt" "I"]]

let unwrapChar_ = 
    [checkcast_ char_T, getfield_ char_T "charInt" "I"]

let defaultConstructor = use JVMAst in
    createFunction "constructor" "()V" [aload_ 0, invokespecial_ "java/lang/Object" "<init>" "()V", return_]

let createName_ = 
    lam prefix. concat prefix (create 6 (lam. randAlphanum ())) -- maybe longer?


let arithClassI_ = use JVMAst in
    lam name. lam op. 
    let freeVar = "var" in
    let varTy = integer_LT in
    createClass 
        name 
        (concat pkg_"Function") 
        [createField freeVar varTy] 
        defaultConstructor 
        [createFunction 
            "apply" 
            "(Ljava/lang/Object;)Ljava/lang/Object;" 
            (foldl concat 
                [aload_ 0, 
                getfield_ (concat pkg_ name) freeVar varTy] 
                [unwrapInteger_, 
                [aload_ 1], 
                unwrapInteger_, 
                op, 
                wrapInteger_, 
                [areturn_]])]

let arithClassF_ = use JVMAst in
    lam name. lam op.
    let freeVar = "var" in
    let varTy = float_LT in
    createClass 
        name 
        (concat pkg_"Function") 
        [createField freeVar varTy] 
        defaultConstructor 
        [createFunction 
            "apply" 
            "(Ljava/lang/Object;)Ljava/lang/Object;" 
            (foldl concat 
                [aload_ 0, 
                getfield_ (concat pkg_ name) freeVar varTy] 
                [unwrapFloat_, 
                [aload_ 1], 
                unwrapFloat_, 
                op, 
                wrapFloat_, 
                [areturn_]])]

let arithClassIB_ = use JVMAst in 
    lam name. lam op. lam label.
    let freeVar = "var" in
    let varTy = integer_LT in
    createClass 
        name 
        (concat pkg_"Function") 
        [createField freeVar varTy] 
        defaultConstructor 
        [createFunction 
            "apply" 
            "(Ljava/lang/Object;)Ljava/lang/Object;" 
            (foldl concat 
                [ldcInt_ 1,
                aload_ 0, 
                getfield_ (concat pkg_ name) freeVar varTy] 
                [unwrapInteger_, 
                [aload_ 1], 
                unwrapInteger_, 
                op,
                [pop_, 
                ldcInt_ 0,
                label_ label],
                wrapBoolean_,
                [areturn_]])]

let arithClassFB_ = use JVMAst in 
    lam name. lam op. lam label.
    let freeVar = "var" in
    let varTy = float_LT in
    createClass 
        name 
        (concat pkg_"Function") 
        [createField freeVar varTy] 
        defaultConstructor 
        [createFunction 
            "apply" 
            "(Ljava/lang/Object;)Ljava/lang/Object;" 
            (foldl concat 
                [ldcInt_ 1,
                aload_ 0, 
                getfield_ (concat pkg_ name) freeVar varTy] 
                [unwrapFloat_, 
                [aload_ 1], 
                unwrapFloat_, 
                op,
                [pop_, 
                ldcInt_ 0,
                label_ label],
                wrapBoolean_,
                [areturn_]])]

let arithClassIjavaI_ = use JVMAst in
    lam name. lam op.
    let freeVar = "var" in
    let varTy = integer_LT in
    createClass
        name
        (concat pkg_ "Function")
        [createField freeVar varTy]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [aload_ 0, 
                getfield_ (concat pkg_ name) freeVar varTy] 
                [unwrapInteger_, 
                [aload_ 1,
                checkcast_ "java/lang/Long"], 
                [invokevirtual_ "java/lang/Long" "intValue" "()I"], 
                op, 
                wrapInteger_, 
                [areturn_]])]

let arithClassCB_ = use JVMAst in
    lam name. lam op. lam label.
    let freeVar = "var" in
    let varTy = char_LT in
    createClass
        name
        (concat pkg_ "Function")
        [createField freeVar varTy]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [ldcInt_ 1,
                aload_ 0, 
                getfield_ (concat pkg_ name) freeVar varTy] 
                [unwrapChar_, 
                [aload_ 1], 
                unwrapChar_, 
                op,
                [pop_, 
                ldcInt_ 0,
                label_ label],
                wrapBoolean_,
                [areturn_]])]

let subiClass_ = arithClassI_ "Subi" [lsub_]

let subfClass_ = arithClassF_ "Subf" [dsub_]

let addiClass_ = arithClassI_ "Addi" [ladd_]

let addfClass_ = arithClassF_ "Addf" [dadd_]

let muliClass_ = arithClassI_ "Muli" [lmul_]

let mulfClass_ = arithClassF_ "Mulf" [dmul_]

let diviClass_ = arithClassI_ "Divi" [ldiv_] 

let divfClass_ = arithClassF_ "Divf" [ddiv_] 

let modiClass_ = arithClassI_ "Modi" [lrem_] 

let slliClass_ = arithClassIjavaI_ "Slli" [lshl_] 

let srliClass_ = arithClassIjavaI_ "Srli" [lushr_] 

let sraiClass_ = arithClassIjavaI_ "Srai" [lshr_] 

let eqiClass_ = arithClassIB_ "Eqi" [lcmp_, ifeq_ "end"] "end"

let neqiClass_ = arithClassIB_ "Neqi" [lcmp_, ifne_ "end"] "end"

let ltiClass_ = arithClassIB_ "Lti" [lcmp_, iflt_ "end"] "end"

let gtiClass_ = arithClassIB_ "Gti" [lcmp_, ifgt_ "end"] "end"

let leqiClass_ = arithClassIB_ "Leqi" [lcmp_, ifle_ "end"] "end"

let geqiClass_ = arithClassIB_ "Geqi" [lcmp_, ifge_ "end"] "end"

let eqfClass_ = arithClassFB_ "Eqf" [dcmp_, ifeq_ "end"] "end"

let neqfClass_ = arithClassFB_ "Neqf" [dcmp_, ifne_ "end"] "end"

let ltfClass_ = arithClassFB_ "Ltf" [dcmp_, iflt_ "end"] "end"

let gtfClass_ = arithClassFB_ "Gtf" [dcmp_, ifgt_ "end"] "end"

let leqfClass_ = arithClassFB_ "Leqf" [dcmp_, ifle_ "end"] "end"

let geqfClass_ = arithClassFB_ "Geqf" [dcmp_, ifge_ "end"] "end"

let endL = createName_ "end" 
let eqcClass_ = arithClassCB_ "Eqc" [ificmpeq_ endL] endL

let recordConstructor = use JVMAst in
    createFunction 
        "constructor" 
        (methodtype_T (arraytype_ object_LT) "V") 
            [aload_ 0, 
            invokespecial_ object_T "<init>" "()V", 
            aload_ 0, 
            aload_ 1, 
            putfield_ (concat pkg_ "Record") "array" (arraytype_ object_LT),
            return_]

let recordClass_ = use JVMAst in 
    createClass 
        "Record" 
        "" 
        [createField "array" (arraytype_ object_LT)]
        recordConstructor
        [] 

let charClass_ = use JVMAst in 
    createClass     
        "CharWrap"
        ""
        [createField "charInt" "I"]
        defaultConstructor
        []

let constClassList_ = 
    [addiClass_, 
    subiClass_, 
    muliClass_, 
    diviClass_, 
    modiClass_,
    addfClass_, 
    subfClass_, 
    mulfClass_, 
    divfClass_,
    slliClass_,
    srliClass_,
    sraiClass_,
    eqiClass_,
    neqiClass_,
    ltiClass_,
    gtiClass_,
    leqiClass_,
    geqiClass_,
    eqfClass_,
    neqfClass_,
    ltfClass_,
    gtfClass_,
    leqfClass_,
    geqfClass_,
    eqcClass_,
    recordClass_,
    charClass_]

let applyArithF_ = use JVMAst in
    lam name. lam env. lam arg. 
    { env with 
        bytecode = foldl concat env.bytecode 
            [initClass_ name, 
            [dup_], 
            arg.bytecode,
            [checkcast_ float_T, 
            putfield_ (concat pkg_ name) "var" float_LT]],
        classes = concat env.classes arg.classes } 

let applyArithI_ = use JVMAst in
    lam name. lam env. lam arg. 
    { env with 
        bytecode = foldl concat env.bytecode 
            [initClass_ name, 
            [dup_], 
            arg.bytecode,
            [checkcast_ integer_T, 
            putfield_ (concat pkg_ name) "var" integer_LT]],
        classes = concat env.classes arg.classes } 

let applyArithC_ = use JVMAst in
    lam name. lam env. lam arg. 
    { env with 
        bytecode = foldl concat env.bytecode 
            [initClass_ name, 
            [dup_], 
            arg.bytecode,
            [checkcast_ char_T, 
            putfield_ (concat pkg_ name) "var" char_LT]],
        classes = concat env.classes arg.classes } 

let oneArgOpI_ = 
    lam op. lam env. lam arg.
    { env with 
        bytecode = foldl concat env.bytecode 
            [arg.bytecode,
            unwrapInteger_,
            [op],
            wrapInteger_], 
        classes = concat env.classes arg.classes }

let oneArgOpF_ = 
    lam op. lam env. lam arg.
    { env with 
        bytecode = foldl concat env.bytecode 
            [arg.bytecode,
            unwrapFloat_,
            [op],
            wrapFloat_], 
        classes = concat env.classes arg.classes }

-- change charwrap to either CharWrap with an integer or Integer class