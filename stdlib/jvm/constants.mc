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

let return_ = use JVMAst in
    createBEmpty "RETURN"

let iadd_ = use JVMAst in
    createBEmpty "IADD"

let isub_ = use JVMAst in 
    createBEmpty "ISUB"

let imul_ = use JVMAst in 
    createBEmpty "IMUL"

let idiv_ = use JVMAst in 
    createBEmpty "IDIV"

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

let type_LT = lam x. join ["L", x, ";"]

let methodtype_T = lam arg. lam ret. join ["(", arg, ")", ret]

let object_T = "java/lang/Object"

let object_LT = type_LT object_T

let integer_T = "java/lang/Integer" 

let integer_LT = type_LT integer_T

----

let pkg_ = "pkg/"

let apply_ = use JVMAst in 
    lam bytecode.
    createFunction "apply" (methodtype_T object_LT object_LT) (concat bytecode [areturn_])

let wrapInteger_ = 
    [invokestatic_ "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;"]

let unwrapInteger_ = 
    [checkcast_ "java/lang/Integer", invokevirtual_ "java/lang/Integer" "intValue" "()I"]

let defaultConstructor = use JVMAst in
    createFunction "constructor" "()V" [aload_ 0, invokespecial_ "java/lang/Object" "<init>" "()V", return_]

let createName_ = 
    lam prefix. concat prefix (create 3 (lam. randAlphanum ()))

let initClass_ = 
    lam name. 
        [new_ (concat pkg_ name), dup_, invokespecial_ (concat pkg_ name) "<init>" "()V"]


let arithClass_ = use JVMAst in
    lam name. lam op.
    let freeVar = "var" in
    let varTy = "Ljava/lang/Integer;" in
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

let subiClass_ = arithClass_ "Subi" [isub_]

let addiClass_ = arithClass_ "Addi" [iadd_]

let muliClass_ = arithClass_ "Muli" [imul_]

let diviClass_ = arithClass_ "Divi" [idiv_] 

let applyArith_ = use JVMAst in
    lam name. lam env. lam argBytecode. 
    { env with 
    bytecode = foldl concat env.bytecode 
        [initClass_ name, 
        [dup_], 
        argBytecode,
        [checkcast_ integer_T, 
        putfield_ (concat pkg_ name) "var" integer_LT]] } 