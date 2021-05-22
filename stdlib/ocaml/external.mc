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
    match tt with (_, OTyLabel _) then
      true
    else match tt with
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
    else match tt with (TyVar {ident = ident}, OTyRecord {fields = fields})
    then
      true
    else match tt with (OTyRecord {fields = fields}, TyVar {ident = ident})
    then
      true
    else match tt with (_, TyVar _) | (TyVar _, _) then
      false
    else match tt with
      (TySeq {ty = ty1}, TySeq {ty = ty2}) |
      (OTyList {ty = ty1}, OTyList {ty = ty2}) |
      (OTyArray {ty = ty1}, OTyArray {ty = ty2})
    then
      recur ty1 ty2
    else match tt with
      (OTyBigarrayGenarray
        {tys = [TyInt _, OTyBigarrayIntElt _, OTyBigarrayClayout _]}
      ,OTyBigarrayGenarray
        {tys = [TyInt _, OTyBigarrayIntElt _, OTyBigarrayClayout _]})
        |
      (OTyBigarrayGenarray
        {tys = [TyFloat _, OTyBigarrayFloat64Elt _, OTyBigarrayClayout _]}
      ,OTyBigarrayGenarray
        {tys = [TyFloat _, OTyBigarrayFloat64Elt _, OTyBigarrayClayout _]})
    then
      false
    else match tt with
      (OTyBigarrayArray {
          rank = rank1,
          tys = [TyInt _, OTyBigarrayIntElt _, OTyBigarrayClayout _]
        }
      ,OTyBigarrayArray {
          rank = rank2,
          tys = [TyInt _, OTyBigarrayIntElt _, OTyBigarrayClayout _]
        })
        |
      (OTyBigarrayArray {
          rank = rank1,
          tys = [TyFloat _, OTyBigarrayFloat64Elt _, OTyBigarrayClayout _]
        }
      ,OTyBigarrayArray {
          rank = rank2,
          tys = [TyFloat _, OTyBigarrayFloat64Elt _, OTyBigarrayClayout _]
        })
    then
      eqi rank1 rank2
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
let _tupleConversionCost = 1
let _recordConversionCost = 1

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

    let convertTuple = lam t. lam tys. lam fields. lam recur.
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
        (addi _tupleConversionCost (foldl1 addi costs), t)
      else never
    in

    if not (_requiresConversion env info ty1 ty2) then
      (0, t)
    else
      let tt = (ty1, ty2) in
      match tt with (_, OTyLabel {label = label, ty = ty2}) then
        recur (OTmLabel { label = label, arg = t }) ty1 ty2
      else match tt with (TySeq {ty = ty1}, OTyList {ty = ty2}) then
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
          convertTuple t tys fields recur
        else infoErrorExit info "Cannot convert tuple"
      else match tt with (TyVar {ident = ident}, OTyTuple {tys = tys}) then
        match mapLookup ident env.constrs
        with Some (TyRecord {fields = fields}) then
          convertTuple t tys fields (lam t. lam ty1. lam ty2. recur t ty2 ty1)
        else infoErrorExit info "Cannot convert tuple"
      else match tt with (OTyRecord {fields = fields1}, TyVar {ident = ident})
      then
        match mapLookup ident env.constrs
        with Some (TyRecord {fields = fields2, labels = labels}) then
          let costsTms =
            mapi
              (lam i. lam field : (String, Type).
                match field with (l1, ty1) then
                  let l2 = get labels i in
                  match mapLookup (stringToSid l2) fields2 with Some ty2 then
                    recur (OTmProject { field = l1, tm = t }) ty1 ty2
                  else never
                else never)
              fields1
          in
          match unzip costsTms with (costs, tms) then
            let t = tmRecord (zip labels tms) ty2 info in
            let cost = addi _recordConversionCost (foldl1 addi costs) in
            (cost, t)
          else never
        else infoErrorExit info "Cannot convert record"
      else match tt with
        (TyVar {ident = ident}, OTyRecord {tyident = tyident, fields = fields2})
      then
        match mapLookup ident env.constrs
        with Some (TyRecord {fields = fields1, labels = labels1}) then
          let ns = create (length labels1) (lam. nameSym "r") in
          let pvars =
            map (lam n. PatNamed { ident = PName n, info = info }) ns
          in
          let rpat = patRecord (zip labels1 pvars) info in
          match unzip fields2 with (labels2, tys2) then
            let costsTms =
              mapi
                (lam i. lam x : (Name, Type).
                  match x with (ident, ty2) then
                    let sid = stringToSid (get labels1 i) in
                    match mapLookup sid fields1 with Some ty1 then
                      let var =
                        TmVar {
                          ident = ident,
                          ty = TyUnknown { info = info },
                          info = info
                        }
                      in
                      recur var ty1 ty2
                    else
                      infoErrorExit info "Cannot convert record"
                  else never)
                (zip ns tys2)
            in
            match unzip costsTms with (costs, tms) then
              let t =
                TmMatch {
                  target = t,
                  pat = rpat,
                  thn =
                    OTmRecord {
                      bindings = zip labels2 tms, tyident = tyident
                    },
                  els = TmNever { ty = TyUnknown { info = info }, info = info },
                  ty = TyUnknown { info = info },
                  info = info
                }
              in
              (foldl1 addi costs, t)
            else never
          else never
        else infoErrorExit info "Cannot convert record"
      else match tt with
        (OTyBigarrayGenarray
          {tys = [TyInt _, OTyBigarrayIntElt _, OTyBigarrayClayout _]}
        ,OTyBigarrayGenarray
          {tys = [TyInt _, OTyBigarrayIntElt _, OTyBigarrayClayout _]})
          |
        (OTyBigarrayGenarray
          {tys = [TyFloat _, OTyBigarrayFloat64Elt _, OTyBigarrayClayout _]}
        ,OTyBigarrayGenarray
          {tys = [TyFloat _, OTyBigarrayFloat64Elt _, OTyBigarrayClayout _]})
      then
        (0, t)
      else match tt with
        (OTyBigarrayArray {
            rank = rank1,
            tys = [TyInt _, OTyBigarrayIntElt _, OTyBigarrayClayout _]
          }
        ,OTyBigarrayArray {
            rank = rank2,
            tys = [TyInt _, OTyBigarrayIntElt _, OTyBigarrayClayout _]
          })
          |
        (OTyBigarrayArray {
            rank = rank1,
            tys = [TyFloat _, OTyBigarrayFloat64Elt _, OTyBigarrayClayout _]
          }
        ,OTyBigarrayArray {
            rank = rank2,
            tys = [TyFloat _, OTyBigarrayFloat64Elt _, OTyBigarrayClayout _]
          })
      then
        if eqi rank1 rank2 then (0, t)
        else infoErrorExit info "Bigarray rank mismatch"
      else match tt with
        (TyTensor {ty = elty1}
        ,OTyBigarrayGenarray
          {tys = [elty2, elty3, OTyBigarrayClayout _]})
      then
        match (elty1, elty2, elty3) with
          (TyInt _, TyInt _, OTyBigarrayIntElt _) |
          (TyFloat _, TyFloat _, OTyBigarrayFloat64Elt _)
        then
          let lhs =
            OTmVarExt
              { ident = intrinsicOpTensor "Helpers.to_genarray_clayout" }
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
        else
          infoErrorExit info "Cannot convert to bigarray"
      else match tt with
        (TyTensor {ty = elty1}
        ,OTyBigarrayArray {
            rank = rank,
            tys = [elty2, elty3, OTyBigarrayClayout _]
          })
      then
        match (elty1, elty2, elty3) with
          (TyInt _, TyInt _, OTyBigarrayIntElt _) |
          (TyFloat _, TyFloat _, OTyBigarrayFloat64Elt _)
        then
          let lhs =
            let op =
              if eqi rank 1 then
                "Helpers.to_array1_clayout"
              else if eqi rank 2 then
                "Helpers.to_array2_clayout"
              else
                infoErrorExit info "Cannot convert bigarray"
            in
            OTmVarExt { ident = intrinsicOpTensor op }
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
        else
          infoErrorExit info "Cannot convert to bigarray"
      else match tt with
        (OTyBigarrayGenarray
          {tys = [elty1, elty3, OTyBigarrayClayout _]}
        ,TyTensor {ty = elty2})
      then
        let op =
          let elt = (elty1, elty2, elty3) in
          match elt with (TyInt _, TyInt _, OTyBigarrayIntElt _) then
            "carray_int"
          else match elt with (TyFloat _, TyFloat _, OTyBigarrayFloat64Elt _)
          then
            "carray_float"
          else infoErrorExit info "Cannot convert bigarray"
        in
        let lhs = OTmVarExt { ident = intrinsicOpTensor op } in
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
        (OTyBigarrayArray {
          rank = rank,
          tys = [elty1, elty3, OTyBigarrayClayout _]
         }
        ,TyTensor {ty = elty2})
      then
        let op =
          let eltr = (elty1, elty2, elty3, rank) in
          match eltr
          with (TyInt _, TyInt _, OTyBigarrayIntElt _, 1) then
            "Helpers.of_array1_clayout_int"
          else match eltr
          with (TyFloat _, TyFloat _, OTyBigarrayFloat64Elt _, 1) then
            "Helpers.of_array1_clayout_float"
          else match eltr
          with (TyInt _, TyInt _, OTyBigarrayIntElt _, 2) then
            "Helpers.of_array2_clayout_int"
          else match eltr
          with (TyFloat _, TyFloat _, OTyBigarrayFloat64Elt _, 2) then
            "Helpers.of_array2_clayout_float"
          else infoErrorExit info "Cannot convert bigarray"
        in
        let lhs = OTmVarExt { ident = intrinsicOpTensor op } in
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
      else dprint ty1; infoErrorExit info "Cannot convert data"
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

  | TmExt {ident = ident, ty = ty, inexpr = inexpr, info = info} ->
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
      infoErrorExit info (join ["No implementation for external ", identStr])
  | t -> sfold_Expr_Expr (chooseExternalImpls implsMap) env t
end
