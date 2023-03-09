include "jvm/ast.mc"

-- Instructions --

let aload_ = use JVMAst in 
    lam i. createBInt "ALOAD" i

let astore_ = use JVMAst in
    lam i. createBInt "ASTORE" i

let iload_ = use JVMAst in
    lam i. createBInt "ILOAD" i

let istore_ = use JVMAst in
    lam i. createBInt "ISTORE" i

let ldcInt_ = use JVMAst in
    lam i. createBInt "LDC" i

let ldcString_ = use JVMAst in
    lam s. createBString "LDC" s

let ldcFloat_ = use JVMAst in
    lam i. createBFloat "LDC" i

let return_ = use JVMAst in
    createBEmpty "RETURN"

let iadd_ = use JVMAst in
    createBEmpty "IADD"

let fadd_ = use JVMAst in
    createBEmpty "FADD"

let isub_ = use JVMAst in 
    createBEmpty "ISUB"

let fsub_ = use JVMAst in 
    createBEmpty "FSUB"

let imul_ = use JVMAst in 
    createBEmpty "IMUL"

let fmul_ = use JVMAst in 
    createBEmpty "FMUL"

let idiv_ = use JVMAst in 
    createBEmpty "IDIV"

let fdiv_ = use JVMAst in 
    createBEmpty "FDIV"

let irem_ = use JVMAst in 
    createBEmpty "IREM"

let ineg_ = use JVMAst in 
    createBEmpty "INEG"

let fneg_ = use JVMAst in 
    createBEmpty "FNEG"

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

---

let jvmTrue = 1

let jvmFalse = 0

---

let type_LT = lam x. join ["L", x, ";"]

let methodtype_T = lam arg. lam ret. join ["(", arg, ")", ret]

let object_T = "java/lang/Object"

let object_LT = type_LT object_T

let integer_T = "java/lang/Integer" 

let integer_LT = type_LT integer_T

let float_T = "java/lang/Float" 

let float_LT = type_LT float_T

let boolean_T = "java/lang/Boolean"

let boolean_LT = type_LT boolean_T


----

let pkg_ = "pkg/"

let apply_ = use JVMAst in 
    lam bytecode.
    createFunction "apply" (methodtype_T object_LT object_LT) (concat bytecode [areturn_])

let wrapInteger_ = 
    [invokestatic_ integer_T "valueOf" (methodtype_T "I" integer_LT)]

let unwrapInteger_ = 
    [checkcast_ integer_T, invokevirtual_ integer_T "intValue" "()I"]

let wrapFloat_ = 
    [invokestatic_ float_T "valueOf" (methodtype_T "F" float_LT)]

let unwrapFloat_ = 
    [checkcast_ float_T, invokevirtual_ float_T "floatValue" "()F"]

let wrapBoolean_ = 
    [invokestatic_ boolean_T "valueOf" (methodtype_T "Z" boolean_LT)]

let unwrapBoolean_ = 
    [checkcast_ boolean_T, invokevirtual_ boolean_T "booleanValue" "()Z"]

let defaultConstructor = use JVMAst in
    createFunction "constructor" "()V" [aload_ 0, invokespecial_ "java/lang/Object" "<init>" "()V", return_]

let createName_ = 
    lam prefix. concat prefix (create 3 (lam. randAlphanum ()))

let initClass_ = 
    lam name. 
        [new_ (concat pkg_ name), dup_, invokespecial_ (concat pkg_ name) "<init>" "()V"]


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

let subiClass_ = arithClassI_ "Subi" [isub_]

let subiClass_ = arithClassF_ "Subf" [fsub_]

let addiClass_ = arithClassI_ "Addi" [iadd_]

let addiClass_ = arithClassF_ "Addf" [fadd_]

let muliClass_ = arithClassI_ "Muli" [imul_]

let muliClass_ = arithClassF_ "Mulf" [fmul_]

let diviClass_ = arithClassI_ "Divi" [idiv_] 

let diviClass_ = arithClassF_ "Divf" [fdiv_] 

let modiClass_ = arithClassI_ "Modi" [irem_] 

let applyArithF_ = use JVMAst in
    lam name. lam env. lam argBytecode. 
    { env with 
        bytecode = foldl concat env.bytecode 
            [initClass_ name, 
            [dup_], 
            argBytecode,
            [checkcast_ float_T, 
            putfield_ (concat pkg_ name) "var" float_LT]] } 

let applyArithI_ = use JVMAst in
    lam name. lam env. lam argBytecode. 
    { env with 
        bytecode = foldl concat env.bytecode 
            [initClass_ name, 
            [dup_], 
            argBytecode,
            [checkcast_ integer_T, 
            putfield_ (concat pkg_ name) "var" integer_LT]] } 