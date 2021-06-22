include "map.mc"
include "ocaml/ast.mc"

let tyaref_ = lam. tyunknown_
let tygeneric_ = lam. tyunknown_

let atomicExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [ ("externalAtomicMake", [
      { ident = "Atomic.make"
      , ty = tyarrow_ (tygeneric_ "a") (tyaref_ "a")
      , libraries = []
      }]),

    ("externalAtomicGet", [
      { ident = "Atomic.get"
      , ty = tyarrow_ (tyaref_ "a") (tygeneric_ "a")
      , libraries = []
      }]),

    ("externalAtomicExchange", [
      { ident = "Atomic.exchange"
      , ty = tyarrows_ [tyaref_ "a", tygeneric_ "a", tygeneric_ "a"]
      , libraries = []
      }]),

    ("externalAtomicCAS", [
      { ident = "Atomic.compare_and_set"
      , ty = tyarrows_ [ tyaref_ "a"
                       , tygeneric_ "a"
                       , tygeneric_ "a"
                       , tybool_
                       ]
      , libraries = []
      }]),

    ("externalAtomicFetchAndAdd", [
      { ident = "Atomic.fetch_and_add"
      , ty = tyarrows_ [tyaref_ "Int", tyint_, tyint_]
      , libraries = []
      }])
  ]
