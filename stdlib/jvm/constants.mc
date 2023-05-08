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

let iadd_ = use JVMAst in
    createBEmpty "IADD"

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

let ificmpge_ = use JVMAst in 
    lam label. createBString "IF_ICMPGE" label

let ificmplt_ = use JVMAst in 
    lam label. createBString "IF_ICMPLT" label

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

let instanceof_ = use JVMAst in
    lam t. createBString "INSTANCEOF" t

let d2l_ = use JVMAst in
    createBEmpty "D2L"

let l2d_ = use JVMAst in 
    createBEmpty "L2D"

let pop2_ = use JVMAst in
    createBEmpty "POP2"

let istore_ = use JVMAst in
    lam i. createBInt "ISTORE" i

let iload_ = use JVMAst in
    lam i. createBInt "ILOAD" i

let i2l_ = use JVMAst in
    createBEmpty "I2L"

let l2i_ = use JVMAst in 
    createBEmpty "L2I"

let arraylength_ = use JVMAst in 
    createBEmpty "ARRAYLENGTH"

let putstatic_ = use JVMAst in
    lam owner. lam name. lam desc. createBApply "PUTSTATIC" owner name desc

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

let seq_T = "scala/collection/immutable/Vector"

let seq_LT = type_LT seq_T

let ref_T = concat pkg_ "Ref"

let ref_LT = type_LT "Ref"

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
    [checkcast_ (concat pkg_ "Record"), getfield_ (concat pkg_ "Record") "array" (arraytype_ object_LT)]

let wrapChar_ = 
    lam char.
    foldl concat (initClass_ "CharWrap") [[dup_], char, [putfield_ char_T "charInt" "I"]]

let unwrapChar_ = 
    [checkcast_ char_T, getfield_ char_T "charInt" "I"]

let defaultConstructor = use JVMAst in
    createFunction "constructor" "()V" [aload_ 0, invokespecial_ "java/lang/Object" "<init>" "()V", return_]

let nothing_ = use JVMAst in
    wrapRecord_ [ldcInt_ 0, anewarray_ object_T]

let createName_ = 
    lam prefix. concat prefix (create 6 (lam. randAlphanum ())) -- maybe longer?

let charseq2Str_ = use JVMAst in 
    [checkcast_ seq_T, invokevirtual_ "scala/collection/immutable/Vector" "mkString" "()Ljava/lang/String;"]

let string2charseq_ = use JVMAst in
    lam localVar.
    let str = localVar in
    let arr = addi localVar 1 in
    let len = addi localVar 2 in
    let i = addi localVar 3 in
    let charInt = addi localVar 4 in
    let endLabel = createName_ "end" in
    let startLabel = createName_ "start" in 
    foldl concat 
        [astore_ str]
        [[new_ "scala/collection/immutable/VectorBuilder",
        dup_,
        invokespecial_ "scala/collection/immutable/VectorBuilder" "<init>" "()V",
        astore_ arr,
        aload_ str,
        invokevirtual_ "java/lang/String" "length" "()I",
        istore_ len,
        ldcInt_ 0,
        istore_ i,
        label_ startLabel,
        iload_ i,
        iload_ len,
        ificmpge_ endLabel,
        aload_ arr,
        aload_ str,
        iload_ i,
        invokevirtual_ "java/lang/String" "codePointAt" "(I)I",
        istore_ charInt],
        wrapChar_ [iload_ charInt],
        [invokevirtual_ "scala/collection/immutable/VectorBuilder" "$plus$eq" "(Ljava/lang/Object;)Lscala/collection/mutable/Growable;",
        pop_,
        iload_ i,
        iload_ charInt,
        invokestatic_ "java/lang/Character" "charCount" "(I)I",
        iadd_,
        istore_ i,
        goto_ startLabel,
        label_ endLabel,
        aload_ arr,
        invokevirtual_ "scala/collection/immutable/VectorBuilder" "result" "()Lscala/collection/immutable/Vector;"]]

let arithClassI_ = use JVMAst in
    lam name. lam op. 
    let freeVar = "var" in
    let varTy = object_LT in
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
                getfield_ (concat pkg_ name) freeVar varTy,
                checkcast_ integer_T] 
                [unwrapInteger_, 
                [aload_ 1], 
                unwrapInteger_, 
                op, 
                wrapInteger_, 
                [areturn_]])]

let arithClassF_ = use JVMAst in
    lam name. lam op.
    let freeVar = "var" in
    let varTy = object_LT in
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
                getfield_ (concat pkg_ name) freeVar varTy,
                checkcast_ float_T] 
                [unwrapFloat_, 
                [aload_ 1], 
                unwrapFloat_, 
                op, 
                wrapFloat_, 
                [areturn_]])]

let arithClassIB_ = use JVMAst in 
    lam name. lam op. lam label.
    let freeVar = "var" in
    let varTy = object_LT in
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
                getfield_ (concat pkg_ name) freeVar varTy,
                checkcast_ integer_T] 
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
    let varTy = object_LT in
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
                getfield_ (concat pkg_ name) freeVar varTy,
                checkcast_ float_T] 
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
    let varTy = object_LT in
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
                getfield_ (concat pkg_ name) freeVar varTy,
                checkcast_ integer_T] 
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
    let varTy = object_LT in
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
                getfield_ (concat pkg_ name) freeVar varTy,
                checkcast_ char_T] 
                [unwrapChar_, 
                [aload_ 1], 
                unwrapChar_, 
                op,
                [pop_, 
                ldcInt_ 0,
                label_ label],
                wrapBoolean_,
                [areturn_]])]

let randClass_ = use JVMAst in
    createClass -- Random(max - min) + min
            "Rand" 
            (concat pkg_ "Function") 
            [createField "var" object_LT] 
            defaultConstructor 
            [createFunction
                "apply"
                (methodtype_T object_LT object_LT)
                (foldl concat
                    [getstatic_ (concat pkg_ "Main") "random" "Ljava/util/Random;",
                    aload_ 1]
                    [unwrapInteger_,
                    [aload_ 0,
                    getfield_ (concat pkg_ "Rand") "var" object_LT,
                    checkcast_ integer_T],
                    unwrapInteger_,
                    [lsub_,
                    invokevirtual_ "java/util/Random" "nextLong" "(J)J",
                    aload_ 0,
                    getfield_ (concat pkg_ "Rand") "var" object_LT,
                    checkcast_ integer_T],
                    unwrapInteger_,
                    [ladd_],
                    wrapInteger_,
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
        [(createFunction
            "toString"
            "()Ljava/lang/String;"
                [new_ "java/lang/String",
                dup_,
                aload_ 0,
                getfield_ (concat pkg_ "CharWrap") "charInt" "I",
                invokestatic_ "java/lang/Character" "toChars" "(I)[C",
                invokespecial_ "java/lang/String" "<init>" "([C)V", 
                areturn_])]

let refClass_ = use JVMAst in 
    createClass
        "Ref"
        ""
        [createField "ref" "Ljava/lang/Object;"]
        defaultConstructor
        []


let symbolClass_ = use JVMAst in 
    createClass
        "Symbol"
        ""
        [createField "symbolInt" "I"]
        defaultConstructor
        []

let genSymbolClass_ = use JVMAst in 
    createClass
        "GenSym"
        ""
        [createField "symbolInt" "I"]
        defaultConstructor
        [(createFunction
            "newSymbol"
            (methodtype_T "" (type_LT (concat pkg_ "Symbol")))
                [aload_ 0, 
                ldcInt_ 1,
                aload_ 0, 
                getfield_ (concat pkg_ "GenSym") "symbolInt" "I",
                iadd_,
                dup_, 
                istore_ 1,
                putfield_ (concat pkg_ "GenSym") "symbolInt" "I",
                new_ (concat pkg_ "Symbol"),
                dup_,
                invokespecial_ (concat pkg_ "Symbol") "<init>" "()V",
                dup_,
                iload_ 1, 
                putfield_ (concat pkg_ "Symbol") "symbolInt" "I",
                areturn_])]

let eqSymClass_ = use JVMAst in
    let endLabel = createName_ "end" in
    createClass 
        "EqSym"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [ldcInt_ 0]
                [[aload_ 0,
                getfield_ (concat pkg_ "EqSym") "var" object_LT,
                checkcast_ (concat pkg_ "Symbol"),
                getfield_ (concat pkg_ "Symbol") "symbolInt" "I",
                aload_ 1,
                checkcast_ (concat pkg_ "Symbol"),
                getfield_ (concat pkg_ "Symbol") "symbolInt" "I",
                ificmpne_ endLabel,
                pop_,
                ldcInt_ 1,
                label_ endLabel],
                wrapBoolean_,
                [areturn_]])]

let consClass_ = use JVMAst in
    createClass
        "Cons"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [aload_ 1]
                [[checkcast_ seq_T,
                aload_ 0,
                getfield_ (concat pkg_ "Cons") "var" object_LT,
                invokevirtual_ seq_T "$plus$colon" (methodtype_T object_LT object_LT),
                areturn_]])]

let snocClass_ = use JVMAst in
    createClass
        "Snoc"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [aload_ 0,
                getfield_ (concat pkg_ "Snoc") "var" object_LT]
                [[checkcast_ seq_T,
                aload_ 1,
                invokevirtual_ seq_T "$colon$plus" (methodtype_T object_LT object_LT),
                areturn_]])]

let getClass_ = use JVMAst in 
    createClass
        "Get"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [aload_ 0,
                getfield_ (concat pkg_ "Get") "var" object_LT]
                [[checkcast_ seq_T,
                aload_ 1],
                unwrapInteger_,
                [l2i_,
                invokevirtual_ seq_T "apply" (methodtype_T "I" object_LT),
                areturn_]])]

let concatClass_ = use JVMAst in
    createClass
        "Concat"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [aload_ 0,
                getfield_ (concat pkg_ "Concat") "var" object_LT,
                checkcast_ seq_T]
                [[aload_ 1,
                checkcast_ seq_T,
                invokevirtual_ seq_T "$plus$plus" (methodtype_T "Lscala/collection/IterableOnce;" object_LT),
                areturn_]])]

let mapClass_ = use JVMAst in 
    let func = 2 in
    let seq = 1 in
    let i = 3 in 
    let len = 4 in 
    let vb = 5 in
    let startLabel = createName_ "start" in
    let endLabel = createName_ "end" in
    createClass
        "Map"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [aload_ 0]
                [[getfield_ (concat pkg_ "Map") "var" object_LT,
                astore_ func,
                ldcInt_ 0,
                istore_ i,
                aload_ seq,
                checkcast_ seq_T,
                invokevirtual_ seq_T "length" "()I",
                istore_ len,
                new_ "scala/collection/immutable/VectorBuilder",
                dup_, 
                invokespecial_ "scala/collection/immutable/VectorBuilder" "<init>" "()V",
                astore_ vb,
                label_ startLabel,
                iload_ i,
                iload_ len,
                ificmpge_ endLabel,
                aload_ vb,
                aload_ func,
                checkcast_ (concat pkg_ "Function"),
                aload_ seq,
                checkcast_ seq_T,
                iload_ i,
                invokevirtual_ seq_T "apply" (methodtype_T "I" object_LT),
                invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                invokevirtual_ "scala/collection/immutable/VectorBuilder" "$plus$eq" "(Ljava/lang/Object;)Lscala/collection/mutable/Growable;",
                pop_,
                iload_ i,
                ldcInt_ 1,
                iadd_,
                istore_ i,
                goto_ startLabel,
                label_ endLabel,
                aload_ vb,
                invokevirtual_ "scala/collection/immutable/VectorBuilder" "result" "()Lscala/collection/immutable/Vector;",
                areturn_]])]

let mapiClass_ = use JVMAst in 
    let func = 2 in
    let seq = 1 in
    let i = 3 in 
    let len = 4 in 
    let vb = 5 in
    let startLabel = createName_ "start" in
    let endLabel = createName_ "end" in
    createClass
        "Mapi"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [aload_ 0]
                [[getfield_ (concat pkg_ "Mapi") "var" object_LT,
                astore_ func,
                ldcInt_ 0,
                istore_ i,
                aload_ seq,
                checkcast_ seq_T,
                invokevirtual_ seq_T "length" "()I",
                istore_ len,
                new_ "scala/collection/immutable/VectorBuilder",
                dup_, 
                invokespecial_ "scala/collection/immutable/VectorBuilder" "<init>" "()V",
                astore_ vb,
                label_ startLabel,
                iload_ i,
                iload_ len,
                ificmpge_ endLabel,
                aload_ vb,
                aload_ func,
                checkcast_ (concat pkg_ "Function"),
                iload_ i,
                i2l_],
                wrapInteger_,
                [invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                aload_ seq,
                checkcast_ seq_T,
                iload_ i,
                invokevirtual_ seq_T "apply" (methodtype_T "I" object_LT),
                invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                invokevirtual_ "scala/collection/immutable/VectorBuilder" "$plus$eq" "(Ljava/lang/Object;)Lscala/collection/mutable/Growable;",
                pop_,
                iload_ i,
                ldcInt_ 1,
                iadd_,
                istore_ i,
                goto_ startLabel,
                label_ endLabel,
                aload_ vb,
                invokevirtual_ "scala/collection/immutable/VectorBuilder" "result" "()Lscala/collection/immutable/Vector;",
                areturn_]])]

let iterClass_ = use JVMAst in 
    let func = 2 in
    let seq = 1 in
    let i = 3 in 
    let len = 4 in 
    let vb = 5 in
    let startLabel = createName_ "start" in
    let endLabel = createName_ "end" in
    createClass
        "Iter"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [aload_ 0]
                [[getfield_ (concat pkg_ "Iter") "var" object_LT,
                astore_ func,
                ldcInt_ 0,
                istore_ i,
                aload_ seq,
                checkcast_ seq_T,
                invokevirtual_ seq_T "length" "()I",
                istore_ len,
                label_ startLabel,
                iload_ i,
                iload_ len,
                ificmpge_ endLabel,
                aload_ func,
                checkcast_ (concat pkg_ "Function"),
                aload_ seq,
                checkcast_ seq_T,
                iload_ i,
                invokevirtual_ seq_T "apply" (methodtype_T "I" object_LT),
                invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                pop_,
                iload_ i,
                ldcInt_ 1,
                iadd_,
                istore_ i,
                goto_ startLabel,
                label_ endLabel],
                nothing_,
                [areturn_]])]

let iteriClass_ = use JVMAst in 
    let func = 2 in
    let seq = 1 in
    let i = 3 in 
    let len = 4 in 
    let vb = 5 in
    let startLabel = createName_ "start" in
    let endLabel = createName_ "end" in
    createClass
        "Iteri"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [aload_ 0]
                [[getfield_ (concat pkg_ "Iteri") "var" object_LT,
                astore_ func,
                ldcInt_ 0,
                istore_ i,
                aload_ seq,
                checkcast_ seq_T,
                invokevirtual_ seq_T "length" "()I",
                istore_ len,
                label_ startLabel,
                iload_ i,
                iload_ len,
                ificmpge_ endLabel,
                aload_ func,
                checkcast_ (concat pkg_ "Function"),
                iload_ i,
                i2l_],
                wrapInteger_,
                [invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                aload_ seq,
                checkcast_ seq_T,
                iload_ i,
                invokevirtual_ seq_T "apply" (methodtype_T "I" object_LT),
                invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                pop_,
                iload_ i,
                ldcInt_ 1,
                iadd_,
                istore_ i,
                goto_ startLabel,
                label_ endLabel],
                nothing_,
                [areturn_]])]

            
let splitAtClass_ = use JVMAst in 
    createClass
        "SplitAt"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [aload_ 0,
                getfield_ (concat pkg_ "SplitAt") "var" object_LT,
                checkcast_ seq_T]
                [[aload_ 1],
                unwrapInteger_,
                [l2i_,
                invokevirtual_ seq_T "splitAt" "(I)Lscala/Tuple2;",
                astore_ 1,
                new_ (concat pkg_ "Record"),
                dup_,
                dup_,
                ldcInt_ 2,
                anewarray_ object_T,
                dup_,
                dup_,
                ldcInt_ 0,
                aload_ 1,
                getfield_ "scala/Tuple2" "_1" object_LT,
                aastore_,
                ldcInt_ 1,
                aload_ 1,
                getfield_ "scala/Tuple2" "_2" object_LT,
                aastore_,
                invokespecial_ (concat pkg_ "Record") "<init>" "([Ljava/lang/Object;)V",
                areturn_]])]

let createClass_ = use JVMAst in 
    let i = 2 in
    let len = 3 in 
    let vb = 4 in
    let startLabel = createName_ "start" in
    let endLabel = createName_ "end" in
    createClass
        "Create"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [ldcInt_ 0,
                istore_ i]
                [[aload_ 0,
                getfield_ (concat pkg_ "Create") "var" object_LT],
                unwrapInteger_,
                [l2i_,
                istore_ len,
                new_ "scala/collection/immutable/VectorBuilder",
                dup_,
                invokespecial_ "scala/collection/immutable/VectorBuilder" "<init>" "()V",
                astore_ vb,
                label_ startLabel,
                iload_ i,
                iload_ len,
                ificmpge_ endLabel,
                aload_ vb,
                aload_ 1,
                iload_ i,
                i2l_],
                wrapInteger_,
                [invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                invokevirtual_ "scala/collection/immutable/VectorBuilder" "$plus$eq" "(Ljava/lang/Object;)Lscala/collection/mutable/Growable;",
                pop_,
                iload_ i,
                ldcInt_ 1,
                iadd_,
                istore_ i,
                goto_ startLabel,
                label_ endLabel,
                aload_ vb,
                invokevirtual_ "scala/collection/immutable/VectorBuilder" "result" "()Lscala/collection/immutable/Vector;",
                areturn_]])]

let createListClass_ = use JVMAst in 
    let i = 2 in
    let len = 3 in 
    let vb = 4 in
    let startLabel = createName_ "start" in
    let endLabel = createName_ "end" in
    createClass
        "CreateList"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [ldcInt_ 0,
                istore_ i]
                [[aload_ 0,
                getfield_ (concat pkg_ "CreateList") "var" object_LT],
                unwrapInteger_,
                [l2i_,
                istore_ len,
                new_ "scala/collection/immutable/VectorBuilder",
                dup_,
                invokespecial_ "scala/collection/immutable/VectorBuilder" "<init>" "()V",
                astore_ vb,
                label_ startLabel,
                iload_ i,
                iload_ len,
                ificmpge_ endLabel,
                aload_ vb,
                aload_ 1,
                iload_ i,
                i2l_],
                wrapInteger_,
                [invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                invokevirtual_ "scala/collection/immutable/VectorBuilder" "$plus$eq" "(Ljava/lang/Object;)Lscala/collection/mutable/Growable;",
                pop_,
                iload_ i,
                ldcInt_ 1,
                iadd_,
                istore_ i,
                goto_ startLabel,
                label_ endLabel,
                aload_ vb,
                invokevirtual_ "scala/collection/immutable/VectorBuilder" "result" "()Lscala/collection/immutable/Vector;",
                areturn_]])]

let createRopeClass_ = use JVMAst in 
    let i = 2 in
    let len = 3 in 
    let vb = 4 in
    let startLabel = createName_ "start" in
    let endLabel = createName_ "end" in
    createClass
        "CreateRope"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [ldcInt_ 0,
                istore_ i]
                [[aload_ 0,
                getfield_ (concat pkg_ "CreateRope") "var" object_LT],
                unwrapInteger_,
                [l2i_,
                istore_ len,
                new_ "scala/collection/immutable/VectorBuilder",
                dup_,
                invokespecial_ "scala/collection/immutable/VectorBuilder" "<init>" "()V",
                astore_ vb,
                label_ startLabel,
                iload_ i,
                iload_ len,
                ificmpge_ endLabel,
                aload_ vb,
                aload_ 1,
                iload_ i,
                i2l_],
                wrapInteger_,
                [invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                invokevirtual_ "scala/collection/immutable/VectorBuilder" "$plus$eq" "(Ljava/lang/Object;)Lscala/collection/mutable/Growable;",
                pop_,
                iload_ i,
                ldcInt_ 1,
                iadd_,
                istore_ i,
                goto_ startLabel,
                label_ endLabel,
                aload_ vb,
                invokevirtual_ "scala/collection/immutable/VectorBuilder" "result" "()Lscala/collection/immutable/Vector;",
                areturn_]])]

let printClass_ = use JVMAst in
    createClass
        "Print"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [getstatic_ "java/lang/System" "out" "Ljava/io/PrintStream;"]
                [[aload_ 1], 
                charseq2Str_,
                [invokevirtual_ "java/io/PrintStream" "print" "(Ljava/lang/String;)V"],
                nothing_,
                [areturn_]])]

let negfClass_ = use JVMAst in
    createClass
        "Negf"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [aload_ 1]
                [unwrapFloat_,
                [dneg_], 
                wrapFloat_,
                [areturn_]])]

let negiClass_ = use JVMAst in
    createClass
        "Negi"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [aload_ 1]
                [unwrapInteger_,
                [lneg_], 
                wrapInteger_,
                [areturn_]])]

let randSetSeedClass_ = use JVMAst in
    createClass
        "RandSetSeed"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [getstatic_ (concat pkg_ "Main") "random" "Ljava/util/Random;"]
                [[aload_ 1],
                unwrapInteger_,
                [invokevirtual_ "java/util/Random" "setSeed" "(J)V"],
                nothing_,
                [areturn_]])]

let floorfiClass_ = use JVMAst in
    createClass
        "Floorfi"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [aload_ 1] 
                [unwrapFloat_,
                [invokestatic_ "java/lang/Math" "floor" "(D)D",
                d2l_],
                wrapInteger_,
                [areturn_]])]

let cielfiClass_ = use JVMAst in
    createClass
        "Cielfi"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [aload_ 1] 
                [unwrapFloat_,
                [invokestatic_ "java/lang/Math" "ciel" "(D)D",
                d2l_],
                wrapInteger_,
                [areturn_]])]
    
let roundfiClass_ = use JVMAst in
    createClass
        "Roundfi"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [aload_ 1]
                [unwrapFloat_,
                [invokestatic_ "java/lang/Math" "round" "(D)J"],
                wrapInteger_,
                [areturn_]])]

let int2floatClass_ = use JVMAst in
    createClass
        "Int2float"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [aload_ 1]
                [unwrapInteger_,
                [l2d_],
                wrapFloat_,
                [areturn_]])]

let char2IntClass_ = use JVMAst in
    createClass
        "Char2Int"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [aload_ 1]
                [unwrapChar_,
                [invokestatic_ integer_T "valueOf" (methodtype_T "I" integer_LT),
                areturn_]])]  
                
let int2charClass_ = use JVMAst in
    createClass
        "Int2Char"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (concat
                (wrapChar_ (foldl concat [aload_ 1] [unwrapInteger_, [l2i_]]))
                [areturn_])]
                    
 
let stringIsFloatClass_ = use JVMAst in
    createClass
        "StringIsFloat"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [aload_ 1]
                [charseq2Str_,
                [astore_ 2],
                [createTryCatch 
                    (foldl concat 
                        [aload_ 2,
                        invokestatic_ "java/lang/Double" "parseDouble" "(Ljava/lang/String;)D",
                        pop2_,
                        ldcInt_ 1]
                        [wrapBoolean_,
                        [astore_ 2]])
                    (foldl concat 
                        [ldcInt_ 0] 
                        [wrapBoolean_, 
                        [astore_ 2]]),
                aload_ 2,
                areturn_]])]  
                
let string2FloatClass_ = use JVMAst in
    createClass
        "String2Float"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat 
                [aload_ 1]
                [charseq2Str_,
                [invokestatic_ "java/lang/Double" "parseDouble" "(Ljava/lang/String;)D"],
                wrapFloat_,    
                [areturn_]])]

let genSymClass_ = use JVMAst in
    createClass
        "GenSymIntrinsic"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                [getstatic_ (concat pkg_ "Main") "symbol" (type_LT (concat pkg_ "GenSym")), 
                invokevirtual_ (concat pkg_ "GenSym") "newSymbol" (methodtype_T "" (type_LT (concat pkg_ "Symbol"))),
                areturn_]]

let sym2HashClass_ = use JVMAst in
    createClass
        "Sym2Hash"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat 
                    [aload_ 1]
                    [[checkcast_ (concat pkg_ "Symbol"),
                    getfield_ (concat pkg_ "Symbol") "symbolInt" "I",
                    i2l_],
                    wrapInteger_,
                    [areturn_]])]


let reverseClass_ = use JVMAst in
    createClass
        "Reverse"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [aload_ 1]
                [[checkcast_ seq_T,
                invokevirtual_ seq_T "reverse" (methodtype_T "" object_LT),
                areturn_]])]

let headClass_ = use JVMAst in
    createClass
        "Head"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [aload_ 1]
                    [[checkcast_ seq_T,
                    invokevirtual_ seq_T "head" (methodtype_T "" object_LT),
                    areturn_]])]

let tailClass_ = use JVMAst in
    createClass
        "Tail"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [aload_ 1]
                    [[checkcast_ seq_T, 
                    invokevirtual_ seq_T "tail" (methodtype_T "" seq_LT),
                    areturn_]])]

let lengthClass_ = use JVMAst in
    createClass
        "Length"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [aload_ 1]
                    [[checkcast_ seq_T, 
                    invokevirtual_ seq_T "length" (methodtype_T "" "I"),
                    i2l_],
                    wrapInteger_,
                    [areturn_]])]

let fileExistsClass_ = use JVMAst in
    createClass
        "FileExists"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [new_ "java/io/File",
                    dup_,
                    aload_ 1]
                    [charseq2Str_,
                    [invokespecial_ "java/io/File" "<init>" "(Ljava/lang/String;)V",
                    invokevirtual_ "java/io/File" "exists" "()Z"],
                    wrapBoolean_,
                    [areturn_]])]

let fileReadClass_ = use JVMAst in
    let fileRead = 2 in 
    let str = 3 in
    let i = 4 in
    let len = 5 in
    let startLabel = createName_ "start" in
    let endLabel = createName_ "end" in
    createClass
        "FileRead"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [aload_ 1]
                    [charseq2Str_,
                    [ldcInt_ 0,
                    anewarray_ "java/lang/String",
                    invokestatic_ "java/nio/file/Paths" "get" "(Ljava/lang/String;[Ljava/lang/String;)Ljava/nio/file/Path;",
                    invokestatic_ "java/nio/file/Files" "readAllLines" "(Ljava/nio/file/Path;)Ljava/util/List;",
                    astore_ fileRead,
                    new_ "java/lang/StringBuilder",
                    dup_,
                    invokespecial_ "java/lang/StringBuilder" "<init>" "()V",
                    astore_ str,
                    ldcInt_ 0,
                    istore_ i,
                    aload_ fileRead,
                    invokeinterface_ "java/util/List" "size" "()I",
                    istore_ len,
                    label_ startLabel,
                    iload_ i,
                    iload_ len,
                    ificmpge_ endLabel,
                    aload_ str,
                    aload_ fileRead,
                    iload_ i,
                    invokeinterface_ "java/util/List" "get" "(I)Ljava/lang/Object;",
                    checkcast_ "java/lang/String",
                    invokevirtual_ "java/lang/StringBuilder" "append" "(Ljava/lang/String;)Ljava/lang/StringBuilder;",
                    pop_,
                    aload_ str,
                    ldcString_ "\\n",
                    invokevirtual_ "java/lang/StringBuilder" "append" "(Ljava/lang/String;)Ljava/lang/StringBuilder;",
                    pop_,
                    iload_ i,
                    ldcInt_ 1,
                    iadd_,
                    istore_ i,
                    goto_ startLabel,
                    label_ endLabel,
                    aload_ str,
                    invokevirtual_ "java/lang/StringBuilder" "toString" "()Ljava/lang/String;"],
                    string2charseq_ 6,
                    [areturn_]])]

let float2StringClass_ = use JVMAst in
    createClass
        "Float2String"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [aload_ 1]
                    [unwrapFloat_,
                    [invokestatic_ "java/lang/String" "valueOf" "(D)Ljava/lang/String;"],
                    string2charseq_ 2,
                    [areturn_]])]

let exitClass_ = use JVMAst in
    createClass
        "Exit"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [aload_ 1]
                    [unwrapInteger_,
                    [l2i_,
                    invokestatic_ "java/lang/System" "exit" "(I)V"],
                    nothing_,
                    [areturn_]])]

let printErrorClass_ = use JVMAst in
    createClass
        "PrintError"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [getstatic_ "java/lang/System" "err" "Ljava/io/PrintStream;"]
                    [[aload_ 1],
                    charseq2Str_,
                    [invokevirtual_ "java/io/PrintStream" "print" "(Ljava/lang/String;)V"],
                    nothing_,
                    [areturn_]])]

let fileDeleteClass_ = use JVMAst in
    createClass
        "FileDelete"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [new_ "java/io/File",
                    dup_,
                    aload_ 1]
                    [charseq2Str_,
                    [invokespecial_ "java/io/File" "<init>" "(Ljava/lang/String;)V",
                    invokevirtual_ "java/io/File" "delete" "()Z"],
                    wrapBoolean_,
                    [areturn_]])]

let errorClass_ = use JVMAst in
    createClass
        "Error"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [getstatic_ "java/lang/System" "err" "Ljava/io/PrintStream;"]
                    [[aload_ 1],
                    charseq2Str_,
                    [invokevirtual_ "java/io/PrintStream" "print" "(Ljava/lang/String;)V",
                    ldcInt_ 1,
                    invokestatic_ "java/lang/System" "exit" "(I)V"],
                    nothing_,
                    [areturn_]])]

let flushStderrClass_ = use JVMAst in
    createClass
        "FlushStderr"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [getstatic_ "java/lang/System" "err" "Ljava/io/PrintStream;"]
                    [[invokevirtual_ "java/io/PrintStream" "flush" "()V"],
                    nothing_,
                    [areturn_]])]

let flushStdoutClass_ = use JVMAst in
    createClass
        "FlushStdout"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [getstatic_ "java/lang/System" "out" "Ljava/io/PrintStream;"]
                    [[invokevirtual_ "java/io/PrintStream" "flush" "()V"],
                    nothing_,
                    [areturn_]])]

let commandClass_ = use JVMAst in
    createClass
        "Command"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [createTryCatch
                        (foldl concat 
                            [invokestatic_ "java/lang/Runtime" "getRuntime" "()Ljava/lang/Runtime;"]
                            [[aload_ 1],
                            charseq2Str_,
                            [invokevirtual_ "java/lang/Runtime" "exec" "(Ljava/lang/String;)Ljava/lang/Process;",
                            invokevirtual_ "java/lang/Process" "waitFor" "()I",
                            i2l_]])
                        [ldcLong_ 1]]
                    [wrapInteger_,
                    [areturn_]])]

let sleepMsClass_ = use JVMAst in
    createClass
        "SleepMs"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [aload_ 1]
                    [unwrapInteger_,
                    [invokestatic_ "java/lang/Thread" "sleep" "(J)V"],
                    nothing_,
                    [areturn_]])]

let wallTimeMsClass_ = use JVMAst in
    createClass
        "WallTimeMs"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [aload_ 1]
                    [[pop_,
                    invokestatic_ "java/lang/System" "currentTimeMillis" "()J"],
                    wrapInteger_,
                    [areturn_]])]

let refIntrinsicClass_ = use JVMAst in
    createClass
        "RefIntrinsic"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    (initClass_ "Ref")
                    [[dup_, 
                    aload_ 1,
                    putfield_ ref_T "ref" object_LT,
                    areturn_]])]

let deRefClass_ = use JVMAst in
    createClass
        "DeRef"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [aload_ 1]
                    [[checkcast_ (concat pkg_ "Ref"),
                    getfield_ ref_T "ref" object_LT,
                    areturn_]])]

let readLineClass_ = use JVMAst in
    createClass
        "ReadLine"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [aload_ 1]
                    [[pop_,
                    new_ "java/util/Scanner",
                    dup_,
                    getstatic_ "java/lang/System" "in" "Ljava/io/InputStream;",
                    invokespecial_ "java/util/Scanner" "<init>" "(Ljava/io/InputStream;)V",
                    invokevirtual_ "java/util/Scanner" "nextLine" "()Ljava/lang/String;"],
                    string2charseq_ 2,
                    [areturn_]])]

let isListClass_ = use JVMAst in
    createClass
        "IsList"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [ldcInt_ 1]
                    [wrapBoolean_,
                    [areturn_]])]

let isRopeClass_ = use JVMAst in
    createClass
        "IsRope"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [ldcInt_ 0]
                    [wrapBoolean_,
                    [areturn_]])]
            
let foldlClass_ = use JVMAst in
    let seq = 2 in 
    let len = 3 in
    let i = 4 in
    let func = 5 in
    let acc = 6 in
    let startLabel = createName_ "start" in
    let endLabel = createName_ "end" in
    createClass
        "Foldl"
        (concat pkg_ "Function")
        [createField "var$" object_LT, 
        createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat
                    [aload_ 1,
                    checkcast_ seq_T]
                    [[dup_,
                    astore_ seq,
                    invokevirtual_ seq_T "length" (methodtype_T "" "I"),
                    istore_ len,
                    ldcInt_ 0,
                    istore_ i,
                    aload_ 0,
                    getfield_ (concat pkg_ "Foldl") "var" object_LT,
                    astore_ func,   
                    aload_ 0,
                    getfield_ (concat pkg_ "Foldl") "var$" object_LT,
                    astore_ acc, 
                    label_ startLabel,
                    iload_ i, 
                    iload_ len,
                    ificmpge_ endLabel,
                    aload_ func,
                    aload_ acc,
                    invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                    aload_ seq,
                    iload_ i,
                    invokevirtual_ seq_T "apply" (methodtype_T "I" object_LT),
                    invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                    astore_ acc,
                    iload_ i,
                    ldcInt_ 1,
                    iadd_,
                    istore_ i,
                    goto_ startLabel,
                    label_ endLabel,
                    aload_ acc,
                    areturn_]])]

let foldrClass_ = use JVMAst in
    let seq = 2 in 
    let len = 3 in
    let i = 4 in
    let func = 5 in
    let acc = 6 in
    let startLabel = createName_ "start" in
    let endLabel = createName_ "end" in
    createClass
        "Foldr"
        (concat pkg_ "Function")
        [createField "var$" object_LT, 
        createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [aload_ 1,
                checkcast_ seq_T,
                invokevirtual_ seq_T "reverse" (methodtype_T "" object_LT),
                checkcast_ seq_T]
                [[dup_,
                astore_ seq,
                invokevirtual_ seq_T "length" (methodtype_T "" "I"),
                istore_ len,
                ldcInt_ 0,
                istore_ i,
                aload_ 0,
                getfield_ (concat pkg_ "Foldr") "var" object_LT,
                astore_ func,   
                aload_ 0,
                getfield_ (concat pkg_ "Foldr") "var$" object_LT,
                astore_ acc, 
                label_ startLabel,
                iload_ i, 
                iload_ len,
                ificmpge_ endLabel,
                aload_ func,
                aload_ acc,
                invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                aload_ seq,
                iload_ i,
                invokevirtual_ seq_T "apply" (methodtype_T "I" object_LT),
                invokeinterface_ (concat pkg_ "Function") "apply" (methodtype_T object_LT object_LT),
                astore_ acc,
                iload_ i,
                ldcInt_ 1,
                iadd_,
                istore_ i,
                goto_ startLabel,
                label_ endLabel,
                aload_ acc,
                areturn_]])]

let subsequenceClass_ = use JVMAst in
    createClass
        "SubSequence"
        (concat pkg_ "Function")
        [createField "var" object_LT,
        createField "var$" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [aload_ 0, 
                getfield_ (concat pkg_ "SubSequence") "var" object_LT,
                checkcast_ seq_T]
                [[aload_ 0,
                getfield_ (concat pkg_ "SubSequence") "var$" object_LT],
                unwrapInteger_,
                [l2i_,
                aload_ 1],
                unwrapInteger_,
                [l2i_,
                invokevirtual_ seq_T "slice" (methodtype_T "II" object_LT),
                areturn_]])]

let nullClass_ = use JVMAst in
    let endLabel = createName_ "end" in
    createClass
        "Null"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
                (foldl concat 
                    [ldcInt_ 1,
                    aload_ 1]
                    [[checkcast_ seq_T,
                    invokevirtual_ seq_T "length" (methodtype_T "" "I"),
                    ifeq_ endLabel,
                    pop_,
                    ldcInt_ 0,
                    label_ endLabel],
                    wrapBoolean_,
                    [areturn_]])]

let modRefClass_ = use JVMAst in
    createClass
        "ModRef"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [aload_ 0,
                getfield_ (concat pkg_ "ModRef") "var" object_LT]
                [[checkcast_ ref_T,
                dup_,
                aload_ 1,
                putfield_ ref_T "ref" object_LT,
                areturn_]])]

let fileWriteClass_ = use JVMAst in
    createClass
        "FileWrite"
        (concat pkg_ "Function")
        [createField "var" object_LT]
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                [createTryCatch
                    (foldl concat
                    [new_ "java/io/BufferedWriter",
                    dup_,
                    new_ "java/io/FileWriter"]
                    [[dup_,
                    aload_ 0,
                    getfield_ (concat pkg_ "FileWrite") "var" object_LT],
                    charseq2Str_,
                    [invokespecial_ "java/io/FileWriter" "<init>" "(Ljava/lang/String;)V",
                    invokespecial_ "java/io/BufferedWriter" "<init>" "(Ljava/io/Writer;)V",
                    dup_,
                    aload_ 1],
                    charseq2Str_,
                    [invokevirtual_ "java/io/BufferedWriter" "write" "(Ljava/lang/String;)V",
                    invokevirtual_ "java/io/BufferedWriter" "close" "()V"]])
                    [getstatic_ "java/lang/System" "out" "Ljava/io/PrintStream;",
                    ldcString_ "Something went wrong",
                    invokevirtual_ "java/io/PrintStream" "println" "(Ljava/lang/String;)V"]]
                [nothing_,
                [areturn_]])]


let dprintClass_ = use JVMAst in
    createClass
        "DPrint"
        (concat pkg_ "Function")
        []
        defaultConstructor
        [createFunction
            "apply"
            (methodtype_T object_LT object_LT)
            (foldl concat
                nothing_
                [[areturn_]])]


let twoArgApplyClass_ = use JVMAst in
    lam name.
        createClass
            (concat name "$")
            (concat pkg_ "Function")
            []
            defaultConstructor
            [createFunction
                "apply"
                (methodtype_T object_LT object_LT)
                [new_ (concat pkg_ name),
                dup_,
                invokespecial_ (concat pkg_ name) "<init>" "()V",
                dup_,
                aload_ 1,
                putfield_ (concat pkg_ name) "var" object_LT,
                areturn_]]

let threeArgApplyClass1_ = use JVMAst in
    lam name.
        let nextClass = (concat name "$$") in
        createClass
            (concat name "$")
            (concat pkg_ "Function")
            []
            defaultConstructor
            [createFunction
                "apply"
                (methodtype_T object_LT object_LT)
                [new_ (concat pkg_ nextClass),
                dup_,
                invokespecial_ (concat pkg_ nextClass) "<init>" "()V",
                dup_,
                aload_ 1,
                putfield_ (concat pkg_ nextClass) "var" object_LT,
                areturn_]]

let threeArgApplyClass2_ = use JVMAst in
    lam name.
        let thisClass = (concat name "$$") in
        createClass
            thisClass
            (concat pkg_ "Function")
            [createField "var" object_LT]
            defaultConstructor
            [createFunction
                "apply"
                (methodtype_T object_LT object_LT)
                [new_ (concat pkg_ name),
                dup_,
                invokespecial_ (concat pkg_ name) "<init>" "()V",
                dup_,
                dup_,
                aload_ 1,
                putfield_ (concat pkg_ name) "var$" object_LT,
                aload_ 0,
                getfield_ (concat pkg_ thisClass) "var" object_LT,
                putfield_ (concat pkg_ name) "var" object_LT,
                areturn_]]
                    
let constClassList_ = 
    [addiClass_,
    twoArgApplyClass_ "Addi", 
    subiClass_, 
    twoArgApplyClass_ "Subi", 
    muliClass_, 
    twoArgApplyClass_ "Muli", 
    diviClass_, 
    twoArgApplyClass_ "Divi", 
    modiClass_,
    twoArgApplyClass_ "Modi", 
    addfClass_, 
    twoArgApplyClass_ "Addf", 
    subfClass_, 
    twoArgApplyClass_ "Subf", 
    mulfClass_, 
    twoArgApplyClass_ "Mulf",
    divfClass_,
    twoArgApplyClass_ "Divf",
    slliClass_,
    twoArgApplyClass_ "Slli",
    srliClass_,
    twoArgApplyClass_ "Srli",
    sraiClass_,
    twoArgApplyClass_ "Srai",
    eqiClass_,
    twoArgApplyClass_ "Eqi",
    neqiClass_,
    twoArgApplyClass_ "Neqi",
    ltiClass_,
    twoArgApplyClass_ "Lti",
    gtiClass_,
    twoArgApplyClass_ "Gti",
    leqiClass_,
    twoArgApplyClass_ "Leqi",
    geqiClass_,
    twoArgApplyClass_ "Geqi",
    eqfClass_,
    twoArgApplyClass_ "Eqf",
    neqfClass_,
    twoArgApplyClass_ "Neqf",
    ltfClass_,
    twoArgApplyClass_ "Ltf",
    gtfClass_,
    twoArgApplyClass_ "Gtf",
    leqfClass_,
    twoArgApplyClass_ "Leqf",
    geqfClass_,
    twoArgApplyClass_ "Geqf",
    eqcClass_,
    twoArgApplyClass_ "Eqc",
    recordClass_,
    charClass_,
    randClass_,
    twoArgApplyClass_ "Rand",
    symbolClass_,
    genSymbolClass_,
    refClass_,
    eqSymClass_,
    twoArgApplyClass_ "EqSym",
    consClass_,
    twoArgApplyClass_ "Cons",
    getClass_,
    twoArgApplyClass_ "Get",
    snocClass_,
    twoArgApplyClass_ "Snoc",
    concatClass_,
    twoArgApplyClass_ "Concat",
    mapClass_,
    twoArgApplyClass_ "Map",
    mapiClass_,
    twoArgApplyClass_ "Mapi",
    iterClass_,
    twoArgApplyClass_ "Iter",
    iteriClass_,
    twoArgApplyClass_ "Iteri",
    splitAtClass_,
    twoArgApplyClass_ "SplitAt",
    createClass_,
    twoArgApplyClass_ "Create",
    createListClass_,
    twoArgApplyClass_ "CreateList",
    createRopeClass_,
    twoArgApplyClass_ "CreateRope",
    printClass_,
    negiClass_,
    negfClass_,
    randSetSeedClass_,
    floorfiClass_,
    cielfiClass_,
    roundfiClass_,
    int2floatClass_,
    char2IntClass_,
    int2charClass_,
    stringIsFloatClass_,
    string2FloatClass_,
    genSymClass_,
    sym2HashClass_,
    reverseClass_,
    headClass_,
    tailClass_,
    lengthClass_,
    fileExistsClass_,
    fileReadClass_,
    float2StringClass_,
    exitClass_,
    printErrorClass_,
    fileDeleteClass_,
    errorClass_,
    flushStderrClass_,
    flushStdoutClass_,
    commandClass_,
    sleepMsClass_,
    wallTimeMsClass_,
    refIntrinsicClass_,
    deRefClass_,
    readLineClass_,
    isListClass_,
    isRopeClass_,
    foldlClass_,
    threeArgApplyClass1_ "Foldl",
    threeArgApplyClass2_ "Foldl",
    foldrClass_,
    threeArgApplyClass1_ "Foldr",
    threeArgApplyClass2_ "Foldr",
    subsequenceClass_,
    threeArgApplyClass1_ "SubSequence",
    threeArgApplyClass2_ "SubSequence",
    nullClass_,
    modRefClass_,
    twoArgApplyClass_ "ModRef",
    dprintClass_,
    fileWriteClass_,
    twoArgApplyClass_ "FileWrite"]

let argvBC_ = use JVMAst in -- puts argv in static field 
    let endLabel = createName_ "end" in 
    let startLabel = createName_ "start" in
    (foldl concat 
        [aload_ 0,
        arraylength_, 
        istore_ 1,
        ldcInt_ 0,
        istore_ 2,
        iload_ 1,
        new_ "scala/collection/immutable/VectorBuilder",
        dup_,
        invokespecial_ "scala/collection/immutable/VectorBuilder" "<init>" "()V",
        astore_ 3,
        label_ startLabel,
        iload_ 1,
        iload_ 2,
        ificmpge_ endLabel,
        aload_ 3,
        aload_ 0,
        iload_ 2,
        aaload_]
        [string2charseq_ 4,
        [invokevirtual_ "scala/collection/immutable/VectorBuilder" "$plus$eq" "(Ljava/lang/Object;)Lscala/collection/mutable/Growable;",
        pop_,
        iload_ 2,
        ldcInt_ 1,
        iadd_,
        istore_ 2,
        goto_ startLabel,
        label_ endLabel,
        aload_ 3,
        invokevirtual_ "scala/collection/immutable/VectorBuilder" "result" "()Lscala/collection/immutable/Vector;",
        putstatic_ (concat pkg_ "Main") "argv" "Lscala/collection/immutable/Vector;"]])
