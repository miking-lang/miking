include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  { expr = arg.expr, ty = arg.ty, libraries = [], cLibraries = [] }

let tymutex_ = tyunknown_

let mutexExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [ ("externalMutexCreate", [
    impl
    { expr = "Mutex.create"
    , ty = tyarrow_ otyunit_ tymutex_
    }]),

    ("externalMutexLock", [
    impl
    { expr = "Mutex.lock"
    , ty = tyarrow_ tymutex_ otyunit_
    }]),

    ("externalMutexRelease", [
    impl
    { expr = "Mutex.unlock"
    , ty = tyarrow_ tymutex_ otyunit_
    }]),

    ("externalMutexTryLock", [
    impl
    { expr = "Mutex.try_lock"
    , ty = tyarrow_ tymutex_ tybool_
    }])
  ]
