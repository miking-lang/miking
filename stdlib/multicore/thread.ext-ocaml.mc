include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  { expr = arg.expr, ty = arg.ty, libraries = [], cLibraries = [] }

let tyathread_ = lam. tyunknown_
let tygeneric_ = lam. tyunknown_

let threadExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [ ("externalThreadSpawn", [
      impl
      { expr = "Domain.spawn"
      , ty = tyarrow_ (tyarrow_ otyunit_ (tygeneric_ "a")) (tyathread_ "a")
      }]),

    ("externalThreadJoin", [
      impl
      { expr = "Domain.join"
      , ty = tyarrow_ (tyathread_ "a") (tygeneric_ "a")
      }]),

    ("externalThreadGetID", [
      impl
      { expr = "Domain.get_id"
      , ty = tyarrow_ (tyathread_ "a") tyint_
      }]),

    ("externalThreadSelf", [
      impl
      { expr = "Domain.self"
      , ty = tyarrow_ otyunit_ tyint_
      }]),

    ("externalThreadCPURelax", [
      impl
      { expr = "Domain.cpu_relax"
      , ty = tyarrow_ otyunit_ otyunit_
      }])
  ]
