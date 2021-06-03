include "mexpr/type.mc"
include "stringid.mc"
include "ocaml/external-includes.mc"
include "ocaml/ast.mc"
include "ocaml/intrinsics-ops.mc"
include "ocaml/generate-env.mc"

lang OCamlDataConversion = OCamlAst + MExprAst

let _approxsize = 10
let _listToSeqCost = 5
let _arrayToSeqCost = 2
let _tensorToGenarrayCost = 1
let _tupleConversionCost = 1
let _recordConversionCost = 1

lang OCamlGenerateExternal = OCamlAst + MExprAst
  -- Popluates `env` by chosing external implementations.
  sem chooseExternalImpls
        (implsMap : Map String [ExternalImpl])
        (env : GenerateEnv) = /- : Expr -> GenerateEnv -/

  sem _convertEls
    (approxsize : Int)
    (mapop : String)
    (info : Info)
    (env : GenerateEnv)
    (t : Expr)
    (ty1 : Type) =
  | ty2 ->
    let ident = nameSym "x" in
    let var =
      TmVar {
        ident = ident,
        ty = TyUnknown { info = info },
        info = info
      }
    in
    match convertData info env var ty1 ty2 with (cost, body) then
      let t =
        if gti cost 0 then
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
        else t
      in
      (muli approxsize cost, t)
    else never

  sem _convertContainer
    (op : String)
    (opcost : Int)
    (approxsize : Int)
    (mapop : String)
    (info : Info)
    (env : GenerateEnv)
    (t : Expr)
    (ty1 : Type) =
  | ty2 ->
    match _convertEls _approxsize mapop info env t ty1 ty2 with (cost, t) then
      let t =
         TmApp {
            lhs = op,
            rhs = t,
            ty = TyUnknown { info = info },
            info = info
          }
       in
       (addi cost opcost, t)
    else never

  sem _convertTuple
    (info : Info)
    (env : GenerateEnv)
    (getTy1 : Type -> Type -> Type)
    (getTy2 : Type -> Type -> Type)
    (t : Expr)
    (fields : [(String, Type)]) =
  | tys ->
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
              convertData info env var (getTy1 ty1 ty2) (getTy2 ty1 ty2)
            else
              infoErrorExit info "Cannot convert tuple"
          else never)
        (zip ns tys)
    in
    match unzip costsTs with (costs, ts) then
      let cost = foldl1 addi costs in
      if eqi cost 0 then
        (0, t)
      else
        let t =
          OTmMatch {
            target = t,
            arms = [(OPatTuple { pats = pvars }, OTmTuple { values = ts })]
          }
        in
        (addi _tupleConversionCost cost , t)
    else never

  -- Converts the term `t` from `ty1` to `ty2`, returning a tuple `(Int, Expr)`
  -- which is the cost and result of the conversion, respectively. If, and only
  -- if, no conversion is necessary, the cost should be 0.
  sem convertData (info : Info) (env : GenerateEnv) (t : Expr) (ty1 : Type) =
  | ty2 ->
    let ty1 = typeUnwrapAlias env.aliases ty1 in
    let ty2 = typeUnwrapAlias env.aliases ty2 in
    let tt : (Type, Type) = (ty1, ty2) in
    match tt with
      (TyArrow {from = ty11, to = ty12}, TyArrow {from = ty21, to = ty22})
    then
      let ident = nameSym "x" in
      let arg = TmVar { ident = ident, ty = ty21, info = info } in
      match (
        match ty11 with OTyLabel {label = label, ty = ty11} then
          match convertData info env arg ty21 ty11 with (cost1, arg) then
             (cost1, OTmLabel { label = label, arg = arg })
          else never
        else
          match convertData info env arg ty21 ty11 with (cost1, arg) then
            (cost1, arg)
          else never
       ) with (cost1, arg)
      then
        let body =
          TmApp {
            lhs = t,
            rhs = arg,
            ty = TyUnknown { info = info },
            info = info
           }
        in
        match convertData info env body ty12 ty22 with (cost2, body) then
          let t =
            TmLam {
              ident = ident,
              tyIdent = ty21,
              body = body,
              ty = TyUnknown { info = info },
              info = info
            }
          in
          (addi cost1 cost2, t)
        else never
      else never
    else match tt with
      (OTyList {ty = ty1}, TySeq {ty = ty2})
    then
      let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.of_list" } in
      let mapop = OTmVarExt { ident = "List.map" } in
      _convertContainer op _listToSeqCost _approxsize mapop info env t ty1 ty2
    else match tt with
      (TySeq {ty = ty1}, OTyList {ty = ty2})
    then
      let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.to_list" } in
      let mapop = OTmVarExt { ident = intrinsicOpSeq "Helpers.map" } in
      _convertContainer op _listToSeqCost _approxsize mapop info env t ty1 ty2
    else match tt with
      (TySeq {ty = ty1}, OTyArray {ty = ty2})
    then
      let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.to_array" } in
      let mapop = OTmVarExt { ident = intrinsicOpSeq "Helpers.map" } in
      _convertContainer op _arrayToSeqCost _approxsize mapop info env t ty1 ty2
    else match tt with
      (OTyArray {ty = ty1}, TySeq {ty = ty2})
    then
      let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.of_array" } in
      let mapop = OTmVarExt { ident = "Array.map" } in
      _convertContainer op _arrayToSeqCost _approxsize mapop info env t ty1 ty2
    else match tt with
      (OTyTuple {tys = []}, TyRecord {fields = fields}) |
      (TyRecord {fields = fields}, OTyTuple {tys = []})
    then
      if eqi (mapSize fields) 0 then
        (0, semi_ t (OTmTuple { values = [] }))
      else infoErrorExit info "Cannot convert unit"
    else match tt with
      (OTyTuple {tys = tys}, TyVar {ident = ident})
    then
      match mapLookup ident env.constrs
      with Some (TyRecord {fields = fields}) then
        _convertTuple info env (lam x. lam. x) (lam. lam x. x) t fields tys
      else infoErrorExit info "Cannot convert from OCaml tuple"
    else match tt with
      (TyVar {ident = ident}, OTyTuple {tys = tys})
    then
      match mapLookup ident env.constrs
      with Some (TyRecord {fields = fields}) then
        _convertTuple info env (lam. lam x. x) (lam x. lam. x) t fields tys
      else infoErrorExit info "Cannot convert to OCaml tuple"
    else match tt with
      (OTyRecord {fields = fields1}, TyVar {ident = ident})
    then
      match mapLookup ident env.constrs
      with Some (TyRecord {fields = fields2, labels = labels2}) then
        let costsTms =
          zipWith
            (lam l2. lam field : (String, Type).
              match field with (l1, ty1) then
                match mapLookup l2 fields2 with Some ty2 then
                  convertData
                    info env (OTmProject { field = l1, tm = t }) ty1 ty2
                else never
              else never)
            labels2 fields1
        in
        match unzip costsTms with (costs, tms) then
          let ns = create (length labels2) (lam. nameSym "t") in
          match mapLookup (ocamlTypedFields fields2) env.records
          with Some id then
            let bindings =
              zipWith (lam label. lam t. (label, objRepr t)) labels2 tms
            in
            let record =
              TmRecord {
                bindings = mapFromSeq cmpSID bindings,
                ty = ty2,
                info = info
               }
            in
            let t = OTmConApp { ident = id, args = [record] } in
            let cost = addi _recordConversionCost (foldl1 addi costs) in
            (cost, t)
          else never
        else never
      else infoErrorExit info "Cannot convert record"
    else match tt with
      (TyVar {ident = ident}, OTyRecord {tyident = tyident, fields = fields2})
    then
      match mapLookup ident env.constrs
      with Some (TyRecord {fields = fields1, labels = labels1}) then
        match mapLookup (ocamlTypedFields fields1) env.records
        with Some id then
          let ns = create (length labels1) (lam. nameSym "r") in
          let pvars =
            map
              (lam n.
                PatNamed {
                  ident = PName n,
                  info = info
                })
              ns
          in
          let rpat =
            OPatRecord { bindings = mapFromSeq cmpSID (zip labels1 pvars) }
          in
          match unzip fields2 with (labels2, tys2) then
            let costsTms =
              mapi
                (lam i. lam x : (Name, Type).
                  match x with (ident, ty2) then
                    let l1 = get labels1 i in
                    match mapLookup l1 fields1 with Some ty1 then
                      let var =
                        TmVar {
                          ident = ident,
                          ty = TyUnknown { info = info },
                          info = info
                        }
                      in
                      convertData info env (objMagic var) ty1 ty2
                    else
                      infoErrorExit info "impossible"
                  else never)
                (zip ns tys2)
            in
            match unzip costsTms with (costs, tms) then
              let rec =
                OTmRecord { bindings = zip labels2 tms, tyident = tyident }
              in
              let cpat = OPatCon { ident = id, args = [rpat] } in
              let t = OTmMatch { target = t, arms = [(cpat, rec)] } in
              (foldl1 addi costs, t)
            else never
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
    else match tt with
      (TyUnknown _, _) | (_, TyUnknown _) |
      (TyInt _, TyInt _) | (TyFloat _, TyFloat _) | (TyBool _, TyBool _)
    then
      (0, t)
    else match tt with
      (TyVar {ident = ident}, _) | (_, TyVar {ident = ident}) |
      (TyApp {lhs = TyVar _}, _) | (_, TyApp {lhs = TyVar _})
    then
      (0, t)
    else
      dprint ty1;
      print "\n";
      dprint ty2;
      infoErrorExit info "Cannot convert data"
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

    let cost = lam ty1. lam ty2.
      match convertData info env uunit_ ty1 ty2 with (cost, _) then cost
      else never
    in

    match impls with Some (![] & impls) then
      let impl =
        minOrElse
          (lam. error "impossible")
          (lam r1 : ExternalImpl. lam r2 : ExternalImpl.
             let cost1 = cost r1.ty ty in
             let cost2 = cost r2.ty ty in
             subi cost1 cost2)
        impls
      in
      let env = { env with exts = mapInsert ident [impl] env.exts } in
      chooseExternalImpls implsMap env inexpr
    else
      infoErrorExit info (join ["No implementation for external ", identStr])
  | t -> sfold_Expr_Expr (chooseExternalImpls implsMap) env t
end
