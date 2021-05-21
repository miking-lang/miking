include "mexpr/type.mc"
include "stringid.mc"
include "ocaml/external-includes.mc"
include "ocaml/ast.mc"
include "ocaml/intrinsics-ops.mc"
include "ocaml/generate-env.mc"

lang OCamlDataConversion = OCamlAst + MExprAst

let _requiresConversion =
  use OCamlDataConversion in
  lam env : GenerateEnv. lam info. lam ty1. lam ty2.
  recursive let recur = lam ty1. lam ty2.
    let tt = (ty1, ty2) in
    match tt with
      (TyUnknown _, _) | (_, TyUnknown _) |
      (TyApp {lhs = TyVar _}, _) | (_, TyApp {lhs = TyVar _}) |
      (OTyParam _, _) | (_, OTyParam _) |
      (TyInt _, TyInt _) | (TyFloat _, TyFloat _) | (TyBool _, TyBool _)
    then
      false
    else match tt with
      (OTyTuple {tys = tys}, TyVar {ident = ident})
    then
      match mapLookup ident env.constrs with Some (TyRecord {fields = fields})
      then
        let fs =
          mapi (lam i. lam ty2. lam.
                let sid = stringToSid (int2string i) in
                match mapLookup sid fields with Some ty1 then
                  recur ty1 ty2
                else
                  infoErrorExit info "Incompatible tuple types")
             tys
        in
        any (lam f. f ()) fs
      else false
    else match tt with
      (TyVar {ident = ident}, OTyTuple {tys = tys})
    then
      match mapLookup ident env.constrs with Some (TyRecord {fields = fields})
      then
        let fs =
          mapi (lam i. lam ty1. lam.
                let sid = stringToSid (int2string i) in
                match mapLookup sid fields with Some ty2 then
                  recur ty1 ty2
                else
                  infoErrorExit info "Incompatible tuple types")
             tys
        in
        any (lam f. f ()) fs
      else false
    else match tt with (_, TyVar _) | (TyVar _, _) then
      false
    else match tt with
      (TySeq {ty = ty1}, TySeq {ty = ty2}) |
      (OTyList {ty = ty1}, OTyList {ty = ty2}) |
      (OTyArray {ty = ty1}, OTyArray {ty = ty2})
    then
      recur ty1 ty2
    else match tt with
      (TyArrow {from = ty11, to = ty12}, TyArrow {from = ty21, to = ty22})
    then
      or (recur ty21 ty11) (recur ty12 ty22)
    else
      true
  in
  recur ty1 ty2

let _approxsize = 10
let _listToSeqCost = 5
let _arrayToSeqCost = 2
let _tensorToGenarrayCost = 1

let _convert : GenerateEnv -> Info -> Expr -> Type -> Type -> (Int, Expr) =
  use OCamlDataConversion in
  lam env : GenerateEnv. lam info. lam t. lam ty1. lam ty2.

  recursive let recur = lam t. lam ty1. lam ty2.

    let covertEls =
    lam approxsize. lam mapop. lam t. lam ty1. lam ty2.
      let ident = nameSym "x" in
      let var =
        TmVar {
          ident = ident,
          ty = TyUnknown { info = info },
          info = info
        }
      in
      match recur var ty1 ty2 with (cost, body) then
        let t =
          TmApp {
            lhs = TmApp {
                    lhs = mapop,
                    rhs =
                      TmLam {
                        ident = ident,
                        tyIdent = TyUnknown { info = info },
                        body = body,
                        ty = TyUnknown { info = info },
                        info = info
                      },
                    ty = TyUnknown { info = info },
                    info = info
                  },
            rhs = t,
            ty = TyUnknown { info = info },
            info = info
          }
        in
        (muli approxsize cost, t)
      else never
    in

    let convertContainer =
    lam opcost. lam approxsize. lam op. lam mapop.
    lam t. lam ty1. lam ty2.
      let x =
        if _requiresConversion env info ty1 ty2 then
          match covertEls approxsize mapop t ty1 ty2 with (cost, t) then
            (addi opcost cost, t)
          else never
        else
          (opcost, t)
      in
      match x with (cost, t) then
        let t =
          TmApp {
            lhs = op,
            rhs = t,
            ty = TyUnknown { info = info },
            info = info
          }
        in
        (cost, t)
      else never
    in

    if not (_requiresConversion env info ty1 ty2) then
      (0, t)
    else
      let tt = (ty1, ty2) in
      match tt with (TySeq {ty = ty1}, OTyList {ty = ty2}) then
        let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.to_list" } in
        let mapop = OTmVarExt { ident = intrinsicOpSeq "Helpers.map" } in
        convertContainer _listToSeqCost _approxsize op mapop t ty1 ty2
      else match tt with (OTyList {ty = ty1}, TySeq {ty = ty2}) then
        let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.of_list" } in
        let mapop = OTmVarExt { ident = "List.map" } in
        convertContainer _listToSeqCost _approxsize op mapop t ty1 ty2
      else match tt with (TySeq {ty = ty1}, OTyArray {ty = ty2}) then
        let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.to_array" } in
        let mapop = OTmVarExt { ident = intrinsicOpSeq "Helpers.map" } in
        convertContainer _arrayToSeqCost _approxsize op mapop t ty1 ty2
      else match tt with (OTyArray {ty = ty1}, TySeq {ty = ty2}) then
        let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.of_array" } in
        let mapop = OTmVarExt { ident = "Array.map" } in
        convertContainer _arrayToSeqCost _approxsize op mapop t ty1 ty2
      else match tt with (TyRecord {fields = fields}, OTyTuple {tys = []}) then
        if eqi (mapSize fields) 0  then
          (0, semi_ t (OTmTuple { values = [] }))
        else
          infoErrorExit info "Cannot convert non-empty record to empty tuple"
      else match tt with (OTyTuple {tys = []}, TyRecord {fields = fields}) then
        if eqi (mapSize fields) 0  then
          (0, semi_ t (tmTuple [] ty2 info))
        else
          infoErrorExit info "Cannot convert empty tuple to non-empty record"
      else match tt with (OTyTuple {tys = tys}, TyVar {ident = ident}) then
        match mapLookup ident env.constrs
        with Some (TyRecord {fields = fields}) then
          let ns = create (length tys) (lam. nameSym "t") in
          let pvars =
            map (lam n. PatNamed { ident = PName n, info = info }) ns
          in
          let tpat = OPatTuple { pats = pvars } in
          let costsTs =
            mapi
              (lam i. lam x : (Name, Type).
                match x with (ident, ty1) then
                  let sid = stringToSid (int2string i) in
                  match mapLookup sid fields with Some ty2 then
                    let var =
                      TmVar {
                        ident = ident,
                        ty = TyUnknown { info = info },
                        info = info
                      }
                    in
                    recur var ty1 ty2
                  else
                    infoErrorExit info "Cannot convert tuple"
                else never)
              (zip ns tys)
          in
          match unzip costsTs with (costs, ts) then
            let t =
              OTmMatch {
                target = t,
                arms = [(OPatTuple { pats = pvars }, OTmTuple { values = ts })]
              }
            in
            (foldl1 addi costs, t)
          else never
        else infoErrorExit info "Cannot convert tuple"
      else match tt with (TyVar {ident = ident}, OTyTuple {tys = tys}) then
        match mapLookup ident env.constrs
        with Some (TyRecord {fields = fields}) then
          let ns = create (length tys) (lam. nameSym "t") in
          let pvars =
            map (lam n. PatNamed { ident = PName n, info = info }) ns
          in
          let tpat = patTuple pvars info in
          let costsTs =
            mapi
              (lam i. lam x : (Name, Type).
                match x with (ident, ty2) then
                  let sid = stringToSid (int2string i) in
                  match mapLookup sid fields with Some ty1 then
                    let var =
                      TmVar {
                        ident = ident,
                        ty = TyUnknown { info = info },
                        info = info
                      }
                    in
                    recur var ty1 ty2
                  else
                    infoErrorExit info "Cannot convert tuple"
                else never)
              (zip ns tys)
          in
          match unzip costsTs with (costs, ts) then
            let t =
              TmMatch {
                target = t,
                pat = tpat,
                thn = tmTuple ts ty1 info,
                els = TmNever { ty = TyUnknown { info = info }, info = info },
                ty = ty1,
                info = info
              }
            in
            (foldl1 addi costs, t)
          else never
        else infoErrorExit info "Cannot convert tuple"
      else match tt with
        (OTyBigArrayGenArray
          {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]}
        ,OTyBigArrayGenArray
          {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]})
      then
        (0, t)
      else match tt with
        (OTyBigArrayGenArray
          {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]}
        ,OTyBigArrayGenArray
          {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]})
      then
        (0, t)
      else match tt with
        (TyTensor {ty = TyInt _}
        ,OTyBigArrayGenArray
          {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]})
      then
        let lhs =
          OTmVarExt { ident = intrinsicOpTensor "Helpers.to_genarray_clayout" }
        in
        let t =
          TmApp {
            lhs = lhs,
            rhs = t,
            ty = ty1,
            info = info
          }
        in
        (_tensorToGenarrayCost, t)
      else match tt with
        (OTyBigArrayGenArray
          {tys = [TyInt _, OTyBigArrayIntElt _, OTyBigArrayClayout _]}
        ,TyTensor {ty = TyInt _})
      then
        let lhs = OTmVarExt { ident = intrinsicOpTensor "carray_int" } in
        let t =
          TmApp {
            lhs = lhs,
            rhs = t,
            ty = ty2,
            info = info
          }
        in
        (_tensorToGenarrayCost, t)
      else match tt with
        (TyTensor {ty = TyFloat _}
        ,OTyBigArrayGenArray
          {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]})
      then
        let lhs =
          OTmVarExt { ident = intrinsicOpTensor "Helpers.to_genarray_clayout" }
        in
        let t =
          TmApp {
            lhs = lhs,
            rhs = t,
            ty = ty1,
            info = info
          }
        in
        (_tensorToGenarrayCost, t)
      else match tt with
        (OTyBigArrayGenArray
          {tys = [TyFloat _, OTyBigArrayFloat64Elt _, OTyBigArrayClayout _]}
        ,TyTensor {ty = TyFloat _})
      then
        let lhs = OTmVarExt { ident = intrinsicOpTensor "carray_float" } in
        let t =
          TmApp {
            lhs = lhs,
            rhs = t,
            ty = ty2,
            info = info
          }
        in
        (_tensorToGenarrayCost, t)
      else match tt
      with (TyArrow {from = ty11, to = ty12}, TyArrow {from = ty21, to = ty22})
      then
        let ident = nameSym "x" in
        let arg = TmVar { ident = ident, ty = ty21, info = info } in
        match recur arg ty21 ty11 with (cost1, arg) then
          let body =
            TmApp {
              lhs = t,
              rhs = arg,
              ty = ty22,
              info = info
            }
          in
          match recur body ty12 ty22 with (cost2, body) then
            let t =
              TmLam {
                ident = ident,
                tyIdent = ty21,
                body = body,
                ty = ty2,
                info = info
              }
            in
            (addi cost1 cost2, t)
          else never
        else never
      else infoErrorExit info "Cannot convert data"
  in

  let ty1 = typeUnwrapAlias env.aliases ty1 in
  let ty2 = typeUnwrapAlias env.aliases ty2 in
  recur t ty1 ty2

-- Converts expression `Exp` of type `Type` to expression `Expr` of type
-- `Type`.
let externalConvertData : GenerateEnv -> Info -> Expr -> Type -> Type -> Expr =
  lam env. lam info. lam t. lam ty1. lam ty2.
  match _convert env info t ty1 ty2 with (_, t) then t
  else never

-- Computes the cost of converting the expression `Exp` of type `Type` to
-- expression `Expr` of type `Type`.
let externalConvertDataCost : GenerateEnv -> Type -> Type -> Int =
  lam env. lam ty1. lam ty2.
  match _convert env (NoInfo ()) never_ ty1 ty2 with (cost, _) then cost
  else never

lang OCamlGenerateExternal
  -- Popluates `env` by chosing external implementations.
  sem chooseExternalImpls
        (implsMap : Map String [ExternalImpl])
        (env : GenerateEnv)
         /- : Expr -> GenerateEnv -/
        =
  -- Intentionally left blank
end

-- A naive implementation of external generation where we just pick the
-- implementation with the lowest cost with respect to the type given at the
-- external term definition.
lang OCamlGenerateExternalNaive = OCamlGenerateExternal + ExtAst
  sem chooseExternalImpls
        (implsMap : Map String [ExternalImpl])
        (env : GenerateEnv) =

  | TmExt {ident = ident, ty = ty, inexpr = inexpr} ->
    let identStr = nameGetStr ident in
    let impls = mapLookup identStr implsMap in
    match impls with Some (![] & impls) then
      let impl =
        minOrElse
          (lam. error "impossible")
          (lam r1 : ExternalImpl. lam r2 : ExternalImpl.
             let cost1 = externalConvertDataCost env r1.ty ty in
             let cost2 = externalConvertDataCost env r2.ty ty in
             subi cost1 cost2)
        impls
      in
      let env = { env with exts = mapInsert ident [impl] env.exts } in
      chooseExternalImpls implsMap env inexpr
    else
      error (join ["No implementation for external ", identStr])
  | t -> sfold_Expr_Expr (chooseExternalImpls implsMap) env t
end
