include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  { expr = arg.expr, ty = arg.ty, libraries = [], cLibraries = [] }

let tyaref_ = lam. tyunknown_
let tygeneric_ = lam. tyunknown_

let atomicExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [ ("externalAtomicMake", [
      impl
      { expr = "Atomic.make"
      , ty = tyarrow_ (tygeneric_ "a") (tyaref_ "a")
      }]),

    ("externalAtomicGet", [
      impl
      { expr = "Atomic.get"
      , ty = tyarrow_ (tyaref_ "a") (tygeneric_ "a")
      }]),

    ("externalAtomicExchange", [
      impl
      { expr = "Atomic.exchange"
      , ty = tyarrows_ [tyaref_ "a", tygeneric_ "a", tygeneric_ "a"]
      }]),

    ("externalAtomicCAS", [
      impl
      { expr = "Atomic.compare_and_set"
      , ty = tyarrows_ [ tyaref_ "a"
                       , tygeneric_ "a"
                       , tygeneric_ "a"
                       , tybool_
                       ]
      }]),

    ("externalAtomicFetchAndAdd", [
      impl
      { expr = "Atomic.fetch_and_add"
      , ty = tyarrows_ [tyaref_ "Int", tyint_, tyint_]
      }])
  ]
