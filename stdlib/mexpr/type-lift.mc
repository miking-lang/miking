include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"

type RecordTypes = [Type]
type DataTypes = Map Name (Map Name Type)

let eqDataType = lam a. lam b.
  use MExprEq in
  match a with (i1, ty1) then
    match b with (i2, ty2) then
      and (nameEq i1 i2) (eqType ty1 ty2)
    else never
  else never

lang MExprRecordTypeLift = MExprEq + RecordAst + RecordTypeAst
  sem _liftRecords (acc : RecordTypes) =
  | r & TmRecord t ->
    match t.ty with TyRecord _ then
      let acc = setInsert (eqType assocEmpty) t.ty acc in
      sfold_Expr_Expr _liftRecords acc r
    else error "Cannot lift type of untyped record"
  | t -> sfold_Expr_Expr _liftRecords acc t

  sem liftRecords =
  | t -> _liftRecords [] t
end

-- output: Map Name (Map Name Type)
-- Outer name is name of variant type
-- Inner map contains mapping from constructor name to the value it is applied
-- to
lang MExprVariantTypeLift = TypeAst + DataAst + VarTypeAst + FunTypeAst
  sem _liftVariants (acc : DataTypes) =
  | TmType t ->
    let acc =
      match mapLookup t.ident acc with Some _ then
        acc
      else mapInsert t.ident (mapEmpty nameCmp) acc
    in
    _liftVariants acc t.inexpr
  | TmConDef t ->
    let acc =
      match t.tyIdent with TyArrow {from = from, to = TyVar {ident = ident}} then
        match mapLookup ident acc with Some m then
          let m = mapInsert t.ident from m in
          mapInsert ident m acc
        else error (join ["Constructor ", nameGetStr t.ident,
                          " refers to unknown variant type ", ident])
      else error "Could not lift type of untyped constructor"
    in
    _liftVariants acc t.inexpr
  | t -> sfold_Expr_Expr _liftVariants acc t

  sem liftVariants =
  | t -> _liftVariants (mapEmpty nameCmp) t
end

lang MExprTypeLift = MExprRecordTypeLift + MExprVariantTypeLift

lang TestLang = MExprTypeLift + MExprTypeAnnot

mexpr

use TestLang in

let eqTypes = lam cmp. lam a. lam b.
  let n = length a in
  if eqi n (length b) then
    recursive let work = lam i.
      if eqi i n then true
      else if cmp (get a i) (get b i) then work (addi i 1)
      else false
    in
    work 0
  else false
in

let eqRecordTypes = lam a. lam b.
  eqTypes (eqType assocEmpty) a b
in

let eqVariantTypes = lam a. lam b.
  let seqa = map (lam t. (t.0, mapBindings t.1)) (mapBindings a) in
  let seqb = map (lam t. (t.0, mapBindings t.1)) (mapBindings b) in
  let variantCmp = lam x. lam y.
    and (nameEq x.0 y.0) (eqType assocEmpty x.1 y.1)
  in
  let n = length seqa in
  if eqi n (length seqb) then
    recursive let work = lam i.
      if eqi n i then true
      else
        let lhs = get seqa i in
        let rhs = get seqb i in
        if nameEq lhs.0 rhs.0 then
          if eqTypes variantCmp lhs.1 rhs.1 then
            work (addi i 1)
          else false
        else false
    in
    work 0
  else false
in

let variantMap = lam s.
  foldl (lam acc. lam v.
    match v with (varName, conNameTypePairs) then
      mapInsert varName (mapFromList nameCmp conNameTypePairs) acc
    else never) (mapEmpty nameCmp) s
in

let lift = lam t.
  let t = typeAnnot t in
  (liftRecords t, liftVariants t)
in

let a = record_ [("a", int_ 2), ("b", float_ 1.5)] in
let b = record_ [("c", float_ 2.), ("a", int_ 2)] in
let c = record_ [("b", int_ 2), ("a", float_ 1.5)] in
let aty = tyrecord_ [("a", tyint_), ("b", tyfloat_)] in
let bty = tyrecord_ [("c", tyfloat_), ("a", tyint_)] in
let cty = tyrecord_ [("b", tyint_), ("a", tyfloat_)] in

let unitType = lift unit_ in
utest unitType.0 with [tyunit_] using eqRecordTypes in
utest unitType.1 with mapEmpty nameCmp using eqVariantTypes in

let recordType = lift (bind_ (ulet_ "x" a) (int_ 0)) in
utest recordType.0 with [aty] using eqRecordTypes in
utest recordType.1 with mapEmpty nameCmp using eqVariantTypes in

let distinctRecords = lift (bindall_ [ulet_ "x" a, ulet_ "y" b, (int_ 0)]) in
utest distinctRecords.0 with [aty, bty] using eqRecordTypes in
utest distinctRecords.1 with mapEmpty nameCmp using eqVariantTypes in

let repeatedRecords = lift (bindall_ [
  ulet_ "x" a,
  ulet_ "y" b,
  ulet_ "z" c,
  ulet_ "w" a,
  int_ 0
]) in
utest repeatedRecords.0 with [aty, bty, cty] using eqRecordTypes in
utest repeatedRecords.1 with mapEmpty nameCmp using eqVariantTypes in

let treeName = nameSym "Tree" in
let treeType = ntyvar_ treeName in
let leafName = nameSym "Leaf" in
let leafConType = tyint_ in
let nodeName = nameSym "Node" in
let nodeConType = tytuple_ [treeType, treeType] in
let t = lift (bindall_ [
  ntype_ treeName tyunknown_,
  ncondef_ leafName (tyarrow_ leafConType treeType),
  ncondef_ nodeName (tyarrow_ nodeConType treeType),
  int_ 0
]) in
let expectedVariants = [(treeName, [
  (leafName, leafConType),
  (nodeName, nodeConType)
])] in
utest t.0 with [] using eqRecordTypes in
utest t.1 with variantMap expectedVariants using eqVariantTypes in

let exprName = nameSym "Expr" in
let exprType = ntyvar_ exprName in
let intName = nameSym "Int" in
let intConType = tyint_ in
let floatName = nameSym "Float" in
let floatConType = tyfloat_ in
let addName = nameSym "Add" in
let addConType = tyrecord_ [("lhs", exprType), ("rhs", exprType)] in
let t = lift (bindall_ [
  ntype_ exprName tyunknown_,
  ncondef_ intName (tyarrow_ intConType exprType),
  ncondef_ floatName (tyarrow_ floatConType exprType),
  ncondef_ addName (tyarrow_ addConType exprType),
  nconapp_ addName (record_ [
    ("lhs", nconapp_ intName (int_ 5)),
    ("rhs", nconapp_ floatName (float_ 2.718))
  ])
]) in
let exprVariantType = TyVariant {constrs = [intName, floatName, addName]} in
let expectedVariants = [(exprName, [
  (intName, intConType),
  (floatName, floatConType),
  (addName, addConType)
])] in
utest t.0 with [addConType] using eqRecordTypes in
utest t.1 with variantMap expectedVariants using eqVariantTypes in

()
