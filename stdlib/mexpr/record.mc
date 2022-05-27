-- record.mc
-- Utilities related to records in MExpr

include "stringid.mc"
include "mexpr/ast.mc"
include "error.mc"

let recordOrderedLabels = lam labels: [SID].
  let isTupleLabel = lam sid.
    let l = sidToString sid in
    if null l then false
    else if eqChar (get l 0) '0' then eqi (length l) 1
    else forAll (lam c. and (geqChar c '0') (leqChar c '9')) l
  in
  -- NOTE(johnwikman, 2022-04-27): cmpString uses shortlex ordering, so this
  -- works fine for comparing string representations of natural numbers.
  let cmpLabel = lam a. lam b. cmpString (sidToString a) (sidToString b) in
  let sortLabel = quickSort cmpLabel in
  match partition isTupleLabel labels with (tupLabels, recLabels) in
  concat (sortLabel tupLabels) (sortLabel recLabels)

let tyRecordOrderedLabels = use RecordTypeAst in
  lam ty: Type.
  match ty with TyRecord {fields = fields} then
    recordOrderedLabels (mapKeys fields)
  else
    errorSingle [infoTy ty] "Not a TyRecord, cannot extract labels."

let tyRecordOrderedFields = use RecordTypeAst in
  lam ty: Type.
  match ty with TyRecord {fields = fields} then
    let labels = recordOrderedLabels (mapKeys fields) in
    map (lam sid. (sid, mapFindExn sid fields)) labels
  else
    errorSingle [infoTy ty] "Not a TyRecord, cannot extract fields."
