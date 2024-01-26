include "string.mc"
include "futhark/ast.mc"
include "futhark/ast-builder.mc"
include "futhark/pprint.mc"

lang FutharkForEachRecordPattern = FutharkAst
  sem useRecordFieldsInBody (recId : Name) (fieldData : Map SID (Name, FutType)) =
  | FEVar t ->
    if nameEq recId t.ident then
      let fields : Map SID FutExpr =
        mapMapWithKey
          (lam. lam v : (Name, FutType).
            FEVar {ident = v.0, ty = v.1, info = t.info})
          fieldData in
      FERecord {fields = fields, ty = t.ty, info = t.info}
    else FEVar t
  | FEProj ({target = FEVar {ident = id}} & t) ->
    if nameEq recId id then
      match mapLookup t.label fieldData with Some (fieldId, ty) then
        FEVar {ident = fieldId, ty = ty, info = t.info}
      else FEProj {t with target = useRecordFieldsInBody recId fieldData t.target}
    else FEProj {t with target = useRecordFieldsInBody recId fieldData t.target}
  | FERecordUpdate ({rec = FEVar {ident = id}} & t) ->
    if nameEq recId id then
      let fields : Map SID FutExpr =
        mapMapWithKey
          (lam k : SID. lam v : (Name, FutType).
            if eqSID t.key k then useRecordFieldsInBody recId fieldData t.value
            else FEVar {ident = v.0, ty = v.1, info = t.info})
          fieldData in
      FERecord {fields = fields, ty = t.ty, info = t.info}
    else FERecordUpdate {t with rec = useRecordFieldsInBody recId fieldData t.rec}
  | t -> smap_FExpr_FExpr (useRecordFieldsInBody recId fieldData) t

  sem useRecordPatternInForEachExpr =
  | FEForEach t ->
    match t.param with (FPNamed {ident = PName patId}, e) then
      let ty = tyFutTm e in
      match ty with FTyRecord {fields = fields} then
        let fieldData : Map SID (Name, FutType) =
          mapMapWithKey
            (lam k : SID. lam ty : FutType.
              (nameSym (concat (nameGetStr patId) (sidToString k)), ty))
            fields in
        let info = infoFutTm e in
        let binds : Map SID FutPat =
          mapMapWithKey
            (lam. lam param : (Name, FutType).
              FPNamed {ident = PName param.0, ty = param.1, info = info})
            fieldData in
        let pat = FPRecord {bindings = binds, ty = ty, info = info} in
        let body = useRecordFieldsInBody patId fieldData t.body in
        FEForEach {{t with param = (pat, e)}
                      with body = body}
      else FEForEach {t with body = useRecordPatternInForEachExpr t.body}
    else FEForEach {t with body = useRecordPatternInForEachExpr t.body}
  | t -> smap_FExpr_FExpr useRecordPatternInForEachExpr t

  sem useRecordPatternInForEachDecl =
  | FDeclFun t -> FDeclFun {t with body = useRecordPatternInForEachExpr t.body}
  | t -> t

  sem useRecordPatternInForEach =
  | FProg t -> FProg {t with decls = map useRecordPatternInForEachDecl t.decls}
end

mexpr

use FutharkForEachRecordPattern in
use FutharkPrettyPrint in

let f = nameSym "f" in
let s = nameSym "s" in
let r = nameSym "r" in
let x = nameSym "x" in
let recordTy = futRecordTy_ [("sum", futIntTy_), ("count", futIntTy_)] in
let fDecl = FDeclFun {
  ident = f, entry = false, typeParams = [],
  params = [(s, futUnsizedArrayTy_ futIntTy_)],
  ret = recordTy, info = NoInfo (),
  body =
    futForEach_
      ( nFutPvar_ r
      , withTypeFutTm recordTy 
                      (futRecord_ [("sum", futInt_ 0), ("count", futInt_ 0)]) )
      x (nFutVar_ s)
      (futRecord_
        [ ("sum", futAdd_ (futRecordProj_ (nFutVar_ r) "sum") (nFutVar_ x))
        , ("count", futAdd_ (futRecordProj_ (nFutVar_ r) "count") (futInt_ 1)) ])} in
let sumCount = FProg {decls = [fDecl]} in

let sum = nameSym "rsum" in
let count = nameSym "rcount" in
let fDeclExpected = FDeclFun {
  ident = f, entry = false, typeParams = [],
  params = [(s, futUnsizedArrayTy_ futIntTy_)],
  ret = recordTy, info = NoInfo (),
  body =
    futForEach_
      ( futPrecord_ [("sum", nFutPvar_ sum), ("count", nFutPvar_ count)]
      , futRecord_ [("sum", futInt_ 0), ("count", futInt_ 0)] )
      x (nFutVar_ s)
      (futRecord_
        [ ("sum", futAdd_ (nFutVar_ sum) (nFutVar_ x))
        , ("count", futAdd_ (nFutVar_ count) (futInt_ 1)) ])} in
let expected = FProg {decls = [fDeclExpected]} in

utest printFutProg (useRecordPatternInForEach sumCount)
with printFutProg expected using eqString in

let fDecl = FDeclFun {
  ident = f, entry = false, typeParams = [],
  params = [(s, futUnsizedArrayTy_ futIntTy_)],
  ret = recordTy, info = NoInfo (),
  body =
    futForEach_
      ( nFutPvar_ r
      , withTypeFutTm recordTy
                      (futRecord_ [("sum", futInt_ 0), ("count", futInt_ 0)]) )
      x (nFutVar_ s)
      (futRecordUpdate_ (nFutVar_ r) "sum"
        (futAdd_ (futRecordProj_ (nFutVar_ r) "sum") (nFutVar_ x)))} in
let recordUpdate = FProg {decls = [fDecl]} in

let fDeclExpected = FDeclFun {
  ident = f, entry = false, typeParams = [],
  params = [(s, futUnsizedArrayTy_ futIntTy_)],
  ret = recordTy, info = NoInfo (),
  body =
    futForEach_
      ( futPrecord_ [("sum", nFutPvar_ sum), ("count", nFutPvar_ count)]
      , futRecord_ [("sum", futInt_ 0), ("count", futInt_ 0)] )
      x (nFutVar_ s)
      (futRecord_
        [ ("sum", futAdd_ (nFutVar_ sum) (nFutVar_ x))
        , ("count", nFutVar_ count) ])} in
let expected = FProg {decls = [fDeclExpected]} in

utest printFutProg (useRecordPatternInForEach recordUpdate)
with printFutProg expected using eqString in

let fDecl = FDeclFun {
  ident = f, entry = false, typeParams = [],
  params = [(s, futUnsizedArrayTy_ futIntTy_)],
  ret = recordTy, info = NoInfo (),
  body =
    futForEach_
      ( nFutPvar_ r
      , withTypeFutTm recordTy
                      (futRecord_ [("sum", futInt_ 0), ("count", futInt_ 0)]) )
      x (nFutVar_ s) (nFutVar_ r)} in
let recordVar = FProg {decls = [fDecl]} in

let fDeclExpected = FDeclFun {
  ident = f, entry = false, typeParams = [],
  params = [(s, futUnsizedArrayTy_ futIntTy_)],
  ret = recordTy, info = NoInfo (),
  body =
    futForEach_
      ( futPrecord_ [("sum", nFutPvar_ sum), ("count", nFutPvar_ count)]
      , futRecord_ [("sum", futInt_ 0), ("count", futInt_ 0)] )
      x (nFutVar_ s)
      (futRecord_ [("sum", nFutVar_ sum), ("count", nFutVar_ count)])} in
let expected = FProg {decls = [fDeclExpected]} in

utest printFutProg (useRecordPatternInForEach recordVar)
with printFutProg expected using eqString in

()
