include "map.mc"
include "ocaml/ast.mc"

let tyathread_ = lam. tyunknown_
let tygeneric_ = lam. tyunknown_


let threadExtMap =
  use OCamlTypeAst in
  mapFromList cmpString
  [ ("externalThreadSpawn", [
      { ident = "Domain.spawn"
      , ty = tyarrow_ (tyarrow_ otyunit_ (tygeneric_ "a")) (tyathread_ "a")
      , libraries = []
      }]),

    ("externalThreadJoin", [
      { ident = "Domain.join"
      , ty = tyarrow_ (tyathread_ "a") (tygeneric_ "a")
      , libraries = []
      }]),

    ("externalThreadGetID", [
      { ident = "Domain.get_id"
      , ty = tyarrow_ (tyathread_ "a") tyint_
      , libraries = []
      }]),

    ("externalThreadSelf", [
      { ident = "Domain.self"
      , ty = tyarrow_ otyunit_ tyint_
      , libraries = []
      }]),

    ("externalThreadWait", [
      { ident = "Domain.Sync.wait"
      , ty = tyarrow_ otyunit_ otyunit_
      , libraries = []
      }]),

    ("externalThreadNotify", [
      { ident = "Domain.Sync.notify"
      , ty = tyarrow_ (tyathread_ "a") otyunit_
      , libraries = []
      }]),

    ("externalThreadCriticalSection", [
      { ident = "Domain.Sync.critical_section"
      , ty = tyarrow_ (tyarrow_ otyunit_ (tygeneric_ "a")) (tyathread_ "a")
      , libraries = []
      }]),

    ("externalThreadCPURelax", [
      { ident = "Domain.Sync.cpu_relax"
      , ty = tyarrow_ otyunit_ otyunit_
      , libraries = []
      }])
  ]
