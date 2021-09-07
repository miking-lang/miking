include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { ident : String, ty : Type }.
  { ident = arg.ident, ty = arg.ty, libraries = [], cLibraries = [] }

let tyaref_ = lam. tyunknown_
let tygeneric_ = lam. tyunknown_

let atomicExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [ ("externalAtomicMake", [
      impl
      { ident = "Atomic.make"
      , ty = tyarrow_ (tygeneric_ "a") (tyaref_ "a")
      }]),

    ("externalAtomicGet", [
      impl
      { ident = "Atomic.get"
      , ty = tyarrow_ (tyaref_ "a") (tygeneric_ "a")
      }]),

    ("externalAtomicExchange", [
      impl
      { ident = "Atomic.exchange"
      , ty = tyarrows_ [tyaref_ "a", tygeneric_ "a", tygeneric_ "a"]
      }]),

    ("externalAtomicCAS", [
      impl
      { ident = "Atomic.compare_and_set"
      , ty = tyarrows_ [ tyaref_ "a"
                       , tygeneric_ "a"
                       , tygeneric_ "a"
                       , tybool_
                       ]
      }]),

    ("externalAtomicFetchAndAdd", [
      impl
      { ident = "Atomic.fetch_and_add"
      , ty = tyarrows_ [tyaref_ "Int", tyint_, tyint_]
      }])
  ]
