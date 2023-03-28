include "map.mc"
include "ocaml/ast.mc"
include "mutex.ext-ocaml.mc"

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  { expr = arg.expr, ty = arg.ty, libraries = [], cLibraries = [] }

let tycond_ = tyunknown_

let condExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [ ("externalCondCreate", [
    impl
    { expr = "Condition.create"
    , ty = tyarrow_ otyunit_ tycond_
    }]),

    ("externalCondWait", [
    impl
    { expr = "Condition.wait"
    , ty = tyarrows_ [tycond_, tyunknown_, otyunit_]
    }]),

    ("externalCondSignal", [
    impl
    { expr = "Condition.signal"
    , ty = tyarrow_ tycond_ otyunit_
    }]),

    ("externalCondBroadcast", [
    impl
    { expr = "Condition.broadcast"
    , ty = tyarrow_ tycond_ otyunit_
    }])
  ]
