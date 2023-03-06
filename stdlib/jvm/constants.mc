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

let ltype_T = lam x. join ["L", x, ";"]

let methodtype_T = lam arg. lam ret. join ["(", arg, ")", ret]

let object_T = "java/lang/Object"

let lobject_T = ltype_T object_T

let integer_T = "java/lang/Integer" 

let linteger_T = ltype_T integer_T

----

let pkg_ = "pkg/"

let apply_ = use JVMAst in 
    lam bytecode.
    createFunction "apply" (methodtype_T lobject_T lobject_T) (concat bytecode [areturn_])

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

let addiClass_ = use JVMAst in
    let name = "Addi" in
    let freeVar = "var" in
    let varTy = "Ljava/lang/Integer;" in
    createClass name (concat pkg_"Function") [createField freeVar varTy] defaultConstructor [createFunction "apply" "(Ljava/lang/Object;)Ljava/lang/Object;" (foldl concat [aload_ 1] [unwrapInteger_, [aload_ 0, getfield_ (concat pkg_ name) freeVar varTy], unwrapInteger_, [iadd_], wrapInteger_, [areturn_]])]