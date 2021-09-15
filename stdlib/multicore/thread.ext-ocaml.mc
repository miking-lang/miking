include "map.mc"
include "ocaml/ast.mc"

let impl = lam arg : { ident : String, ty : Type }.
  { ident = arg.ident, ty = arg.ty, libraries = [], cLibraries = [] }

let tyathread_ = lam. tyunknown_
let tygeneric_ = lam. tyunknown_

let threadExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [ ("externalThreadSpawn", [
      impl
      { ident = "Domain.spawn"
      , ty = tyarrow_ (tyarrow_ otyunit_ (tygeneric_ "a")) (tyathread_ "a")
      , libraries = []
      }]),

    ("externalThreadJoin", [
      impl
      { ident = "Domain.join"
      , ty = tyarrow_ (tyathread_ "a") (tygeneric_ "a")
      }]),

    ("externalThreadGetID", [
      impl
      { ident = "Domain.get_id"
      , ty = tyarrow_ (tyathread_ "a") tyint_
      }]),

    ("externalThreadSelf", [
      impl
      { ident = "Domain.self"
      , ty = tyarrow_ otyunit_ tyint_
      }]),

    ("externalThreadCPURelax", [
      impl
      { ident = "Domain.Sync.cpu_relax"
      , ty = tyarrow_ otyunit_ otyunit_
      }])
  ]
