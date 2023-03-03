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

let defaultConstructor = use JVMAst in
    createFunction "constructor" "()V" [createBInt "ALOAD" 0, createBApply "INVOKESPECIAL" "java/lang/Object" "<init>" "()V", createBEmpty "RETURN"]

let createName_ = use JVMAst in
    lam prefix. concat prefix (create 3 (lam. randAlphanum ()))