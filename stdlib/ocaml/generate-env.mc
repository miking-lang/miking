include "name.mc"
include "stringid.mc"
include "ocaml/external-includes.mc"
include "mexpr/cmp.mc"

type GenerateEnv = {
  constrs : Map Name Type,
  records : Map (Map SID Type) Name,
  aliases : Map Name Type,
  exts : Map Name [ExternalImpl]
}

let emptyGenerateEnv = use MExprCmpClosed in {
  constrs = mapEmpty nameCmp,
  records = mapEmpty (mapCmp cmpType),
  aliases = mapEmpty nameCmp,
  exts = mapEmpty nameCmp
}

let objRepr = use OCamlAst in
  lam t. app_ (OTmVarExt {ident = "Obj.repr"}) t
let objMagic = use OCamlAst in
  lam t. app_ (OTmVarExt {ident = "Obj.magic"}) t

let toOCamlType = use MExprAst in
  lam ty : Type.
  recursive let work = lam nested : Bool. lam ty : Type.
    match ty with TyRecord t then
      if or (mapIsEmpty t.fields) nested then tyunknown_
      else TyRecord {t with fields = mapMap (work true) t.fields}
    else tyunknown_
  in work false ty

let ocamlTypedFields = lam fields : Map SID Type.
  mapMap toOCamlType fields
