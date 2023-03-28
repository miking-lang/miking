include "mexpr/type.mc"
include "mexpr/record.mc"
include "stringid.mc"
include "ocaml/external-includes.mc"
include "ocaml/ast.mc"
include "ocaml/intrinsics-ops.mc"
include "ocaml/generate-env.mc"

let _approxsize = 10
let _listToSeqCost = 5
let _arrayToSeqCost = 2
let _tensorToGenarrayCost = 1
let _tupleConversionCost = 1
let _recordConversionCost = 1
let _seqtostringcost = 2

lang OCamlChooseExternalImpl = Ast
  -- `chooseExternalImpls impls env t` chooses external definitions from
  -- `impls` for each external in `t` and adds these to `env`.
  sem chooseExternalImpls
    : Map String [ExternalImpl] -> GenerateEnv -> Expr -> GenerateEnv
end

lang OCamlDataConversion = Ast
  -- `convertDataInner info env tm2 (ty1, ty2)` converts the term `t` from
  -- `ty1` to `ty2`, returning a tuple `(cost, t2)`, where `tm2` is the
  -- converted term and `cost` which is the cost of the conversion. The cost is
  -- 0 If, and only if, no conversion is necessary.
  sem convertDataInner
    : Info -> GenerateEnv -> Expr -> (Type, Type) -> (Int, Expr)

  -- `convertData` wraps `convertDataInner`, performing common operations
  -- on types before conversions such as unwrapping type aliases. I.e. recursive
  -- calls to `convertDataInner` should in most cases go via this function.
  sem convertData
    : Info -> GenerateEnv -> Expr -> (Type, Type) -> (Int, Expr)
  sem convertData info env t =
  | (ty1, ty2) ->
    let ty1 = unwrapType ty1 in
    let ty2 = unwrapType ty2 in
    convertDataInner info env t (ty1, ty2)
end

lang OCamlDataConversionBase = OCamlDataConversion + OCamlAst
  + IntTypeAst + FloatTypeAst + BoolTypeAst

  sem convertDataInner info env t =
  | (TyInt _, TyInt _) | (TyFloat _, TyFloat _) | (TyBool _, TyBool _) -> (0, t)
end

lang OCamlDataConversionOpaque = OCamlDataConversion + OCamlAst
  + ConTypeAst + AppTypeAst + UnknownTypeAst + AllTypeAst + VarTypeAst

  sem convertDataInner info env t =
  | (TyUnknown _ | TyVar _, !(TyAll _)) | (!(TyAll _), TyUnknown _ | TyVar _)
  | (TyCon {ident = _}, !(TyAll _)) | (!(TyAll _), TyCon {ident = _})
  | (TyApp {lhs = TyCon _}, !(TyAll _)) | (!(TyAll _), TyApp {lhs = TyCon _})
  -> (0, t)
  | (TyAll {ty = ty1}, TyAll {ty = ty2})
  | (TyAll {ty = ty1}, ty2)
  | (ty1, TyAll {ty = ty2})
  -> convertData info env t (ty1, ty2)
end

lang OCamlDataConversionFun =
  OCamlDataConversion + OCamlAst + FunTypeAst + UnknownTypeAst
  sem convertDataInner info env t =
  | (TyArrow {from = ty11, to = ty12}, TyArrow {from = ty21, to = ty22}) ->
     let ident = nameSym "x" in
      let arg =
        TmVar { ident = ident, ty = ty21, info = info, frozen = false }
      in
      match (
        match ty11 with OTyLabel {label = label, ty = ty11} then
          match convertData info env arg (ty21, ty11) with (cost1, arg) in
          (cost1, OTmLabel { label = label, arg = arg })
        else
        match ty21 with OTyLabel {ty = ty21} then
          convertData info env arg (ty21, ty11)
        else
          match convertData info env arg (ty21, ty11) with (cost1, arg) in
          (cost1, arg)
      ) with (cost1, arg) in
      let body =
        TmApp {
          lhs = t,
          rhs = arg,
          ty = TyUnknown { info = info },
          info = info
         }
      in
      let label =
        match ty21 with OTyLabel {label = label} then Some label else None ()
      in
      match convertData info env body (ty12, ty22) with (cost2, body) in
      let t = OTmLam { label = label, ident = ident, body = body } in
      (addi cost1 cost2, t)
end

lang OCamlDataConversionString =
  OCamlDataConversion + OCamlAst
  + SeqTypeAst + CharTypeAst + UnknownTypeAst + LamAst + AppAst

  sem convertDataInner info env t =
  | (OTyString _, TySeq {ty = TyChar _} & ty2) ->
    let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.of_utf8" } in
    let t =
      TmApp {
        lhs = op,
        rhs = t,
        ty = ty2,
        info = info
      }
    in
    (_seqtostringcost, t)
  | (TySeq {ty = TyChar _}, OTyString _) ->
    let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.to_utf8" } in
    let t =
      TmApp {
        lhs = op,
        rhs = t,
        ty = TyUnknown { info = info },
        info = info
      }
    in
    (_seqtostringcost, t)
end

lang OCamlDataConversionHelpers =
  OCamlDataConversion + OCamlAst + UnknownTypeAst + LamAst + AppAst + VarAst

  sem _convertElements
    : Int -> Expr -> Info -> GenerateEnv -> Expr -> (Type, Type) -> (Int, Expr)
  sem _convertElements approxsize mapop info env t =
  | (ty1, ty2) ->
    let ident = nameSym "x" in
    let var =
      TmVar {
        ident = ident,
        ty = TyUnknown { info = info },
        info = info,
        frozen = false
      }
    in
    match convertData info env var (ty1, ty2) with (cost, body) in
    let t =
      if gti cost 0 then
        TmApp {
          lhs = TmApp {
                  lhs = mapop,
                  rhs =
                    TmLam {
                      ident = ident,
                      tyAnnot = TyUnknown { info = info },
                      tyParam = TyUnknown { info = info },
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

  -- Helper function to convert a container.
  sem convertContainer
    : Expr                      -- Operation that converts the container.
    -> Int                      -- Cost of container operation.
    -> Int                      -- Approximate size of container (influences
                                -- overall conversion cost).
    -> Expr                     -- Operation that coverts the elements in the
                                -- container.
    -> Info                     -- File info.
    -> GenerateEnv              -- The environment.
    -> Expr                     -- The container term to convert.
    -> (Type, Type)             -- (ty1, ty2), the container element type ty1 to
                                -- be converted to an element type ty2.
    -> (Int, Expr)              -- The conversion cost and converted term.
  sem convertContainer op opcost approxsize mapop info env t =
  | (ty1, ty2) ->
    match _convertElements _approxsize mapop info env t (ty1, ty2)
    with (cost, t) in
    let t =
       TmApp {
          lhs = op,
          rhs = t,
          ty = TyUnknown { info = info },
          info = info
        }
     in
     (addi cost opcost, t)

  -- Helper function to convert OCaml tuples to/from MExpr records.
  sem convertTuple
  : Info                        -- File info.
  -> GenerateEnv                -- The environment.
  -> Bool                       -- If converting from ty1 to ty2 (otherwise ty2
                                -- to ty1).
  -> Expr                       -- The term to convert.
  -> Map SID Type               -- The Record fields of MExpr record type.
  -> [Type]                     -- The syntactic order of fields of MExpr record
                                -- type.
  -> (Int, Expr)                -- The conversion cost and converted term.
  sem convertTuple info env ty1ToTy2 t fields =
  | tys ->
    let ns = create (length tys) (lam. nameSym "t") in
    let pvars =
      map (lam n. PatNamed { ident = PName n, info = info, ty = tyunknown_ }) ns
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
                  info = info,
                  frozen = false
                }
              in
              if ty1ToTy2 then convertData info env var (ty1, ty2)
              else convertData info env var (ty2, ty1)
            else
              errorSingle [info] "Cannot convert tuple"
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

end

lang OCamlDataConversionList = OCamlDataConversionHelpers + OCamlAst
  + SeqTypeAst + UnknownTypeAst + ExtAst + LamAst

  sem convertDataInner info env t =
  | (OTyList {ty = ty1}, TySeq {ty = ty2}) ->
    let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.of_list" } in
    let mapop = OTmVarExt { ident = "List.map" } in
    convertContainer op _listToSeqCost _approxsize mapop info env t (ty1, ty2)
  | (TySeq {ty = ty1}, OTyList {ty = ty2}) ->
    let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.to_list" } in
    let mapop = OTmVarExt { ident = intrinsicOpSeq "map" } in
    convertContainer op _listToSeqCost _approxsize mapop info env t (ty1, ty2)
end

lang OCamlDataConversionArray = OCamlDataConversionHelpers + OCamlAst
  + SeqTypeAst + UnknownTypeAst + ExtAst + LamAst

  sem convertDataInner info env t =
  | (TySeq {ty = ty1}, OTyArray {ty = ty2}) ->
    let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.to_array_copy" } in
    let mapop = OTmVarExt { ident = intrinsicOpSeq "map" } in
    convertContainer op _arrayToSeqCost _approxsize mapop info env t (ty1, ty2)
  | (OTyArray {ty = ty1}, TySeq {ty = ty2}) ->
    let op = OTmVarExt { ident = intrinsicOpSeq "Helpers.of_array_copy" } in
    let mapop = OTmVarExt { ident = "Array.map" } in
    convertContainer op _arrayToSeqCost _approxsize mapop info env t (ty1, ty2)
end

lang OCamlDataConversionTuple = OCamlDataConversionHelpers + OCamlAst
  + RecordTypeAst + ConTypeAst + UnknownTypeAst

  sem convertDataInner info env t =
  | (OTyTuple {tys = []}, TyRecord {fields = fields}) |
    (TyRecord {fields = fields}, OTyTuple {tys = []}) ->
    if eqi (mapSize fields) 0 then
      (0, semi_ t (OTmTuple { values = [] }))
    else errorSingle [info] "Cannot convert unit"
  | (OTyTuple {tys = tys}, TyCon {ident = ident}) ->
    match mapLookup ident env.constrs
    with Some (TyRecord {fields = fields}) then
      convertTuple info env true t fields tys
    else errorSingle [info] "Cannot convert from OCaml tuple"
  | (TyCon {ident = ident}, OTyTuple {tys = tys}) ->
    match mapLookup ident env.constrs
    with Some (TyRecord {fields = fields}) then
      convertTuple info env false t fields tys
    else errorSingle [info] "Cannot convert to OCaml tuple"
end

lang OCamlDataConversionRecords = OCamlDataConversion + OCamlAst
  + RecordTypeAst + ConTypeAst + UnknownTypeAst

  sem convertDataInner info env t =
  | (OTyRecordExt {fields = fields1} & ty1,
    TyCon {ident = ident} & ty2) ->
    match mapLookup ident env.constrs
    with Some (TyRecord {fields = fields2} & ty) then
      let fields1Labels2 =
        map
          (lam f : { label : String, asLabel : String, ty : Type}.
            match f with {label = label, asLabel = asLabel, ty = ty} in
            ((label, ty), stringToSid asLabel))
          fields1
      in
      match unzip fields1Labels2 with (fields1, labels2) in
      let costsTms =
        zipWith
          (lam l2. lam field : (String, Type).
            match field with (l1, ty1) in
            match mapLookup l2 fields2 with Some ty2 then
              convertData
                info env (OTmProject { field = l1, tm = t }) (ty1, ty2)
            else
              errorSingle [info] (join
                  ["Field \"", sidToString l2, "\" not found in record type"]))
          labels2 fields1
      in
      match unzip costsTms with (costs, tms) in
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
      else errorSingle [info] "impossible"
    else errorSingle [info] "Cannot convert record"
  | (TyCon {ident = ident} & ty1,
    OTyRecordExt {tyident = tyident, fields = fields2} & ty2) ->
    match mapLookup ident env.constrs
    with Some (TyRecord {fields = fields1} & ty) then
      let fields2Labels1 =
        map
          (lam f : {label : String, asLabel : String, ty : Type}.
            match f with {label = label, asLabel = asLabel, ty = ty} in
            ((label, ty), stringToSid asLabel))
          fields2
      in
      match unzip fields2Labels1 with (fields2, labels1) in
      match mapLookup (ocamlTypedFields fields1) env.records
      with Some id then
        let ns = create (length labels1) (lam. nameSym "r") in
        let pvars =
          map
            (lam n.
              PatNamed {
                ident = PName n,
                info = info,
                ty = tyunknown_
              })
            ns
        in
        let rpat =
          OPatRecord { bindings = mapFromSeq cmpSID (zip labels1 pvars) }
        in
        match unzip fields2 with (labels2, tys2) in
        let costsTms =
          zipWith
            (lam ident : Name. lam x : (SID, Type).
              match x with (l1, ty2) in
              match mapLookup l1 fields1 with Some ty1 then
                let var =
                  TmVar {
                    ident = ident,
                    ty = TyUnknown { info = info },
                    info = info,
                    frozen = false
                  }
                in
                convertData info env (objMagic var) (ty1, ty2)
              else
                errorSingle [info] (join
                    ["Field \"", sidToString l1, "\" not found in record type"]))
            ns (zip labels1 tys2)
        in
        match unzip costsTms with (costs, tms) in
        let rec =
          OTmRecord { bindings = zip labels2 tms, tyident = tyident }
        in
        let cpat = OPatCon { ident = id, args = [rpat] } in
        let t = OTmMatch { target = t, arms = [(cpat, rec)] } in
        (foldl1 addi costs, t)
      else errorSingle [info] "impossible"
    else errorSingle [info] "Cannot convert record"
end

lang OCamlDataConversionBigArray = OCamlDataConversionHelpers + OCamlAst
  + TensorTypeAst + UnknownTypeAst + ExtAst + LamAst

  sem convertDataInner info env t =
  | (OTyBigarrayGenarray
      {ty = TyInt _, elty = OTyBigarrayIntElt _, layout = OTyBigarrayClayout _}
    ,OTyBigarrayGenarray
      {ty = TyInt _, elty = OTyBigarrayIntElt _, layout = OTyBigarrayClayout _})
  | (OTyBigarrayGenarray {
      ty = TyFloat _,
      elty = OTyBigarrayFloat64Elt _,
      layout = OTyBigarrayClayout _
    }
    ,OTyBigarrayGenarray {
      ty = TyFloat _,
      elty = OTyBigarrayFloat64Elt _,
      layout = OTyBigarrayClayout _
    })
  ->
    (0, t)
  | (OTyBigarrayArray {
        rank = rank1,
        ty = TyInt _, elty = OTyBigarrayIntElt _, layout = OTyBigarrayClayout _
      }
    ,OTyBigarrayArray {
        rank = rank2,
        ty = TyInt _, elty = OTyBigarrayIntElt _, layout = OTyBigarrayClayout _
      })
  | (OTyBigarrayArray {
        rank = rank1,
        ty = TyFloat _,
        elty = OTyBigarrayFloat64Elt _,
        layout = OTyBigarrayClayout _
      }
    ,OTyBigarrayArray {
        rank = rank2,
        ty = TyFloat _,
        elty = OTyBigarrayFloat64Elt _,
        layout = OTyBigarrayClayout _
      })
  ->
    if eqi rank1 rank2 then (0, t)
    else errorSingle [info] "Bigarray rank mismatch"
  | (TyTensor {ty = elty1} & ty1
    ,OTyBigarrayGenarray
      {ty = elty2, elty = elty3, layout = OTyBigarrayClayout _})
  ->
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
      errorSingle [info] "Cannot convert to bigarray"
  | (TyTensor {ty = elty1} & ty1
    ,OTyBigarrayArray {
        rank = rank,
        ty = elty2, elty = elty3, layout = OTyBigarrayClayout _
      })
   ->
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
            errorSingle [info] "Cannot convert bigarray"
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
      errorSingle [info] "Cannot convert to bigarray"
  | (OTyBigarrayGenarray
      {ty = elty1, elty = elty3, layout = OTyBigarrayClayout _}
    ,TyTensor {ty = elty2} & ty2)
  ->
    let op =
      switch (elty1, elty2, elty3)
      case (TyInt _, TyInt _, OTyBigarrayIntElt _) then
        "Helpers.of_genarray_clayout"
      case (TyFloat _, TyFloat _, OTyBigarrayFloat64Elt _) then
        "Helpers.of_genarray_clayout"
      case (_, _, _) then errorSingle [info] "Cannot convert bigarray"
      end
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
  | (OTyBigarrayArray {
      rank = rank,
      ty = elty1, elty = elty3, layout = OTyBigarrayClayout _
     }
    ,TyTensor {ty = elty2} & ty2)
  ->
    let op =
      switch (elty1, elty2, elty3, rank)
      case (TyInt _, TyInt _, OTyBigarrayIntElt _, 1) then
        "Helpers.of_array1_clayout"
      case (TyFloat _, TyFloat _, OTyBigarrayFloat64Elt _, 1) then
        "Helpers.of_array1_clayout"
      case (TyInt _, TyInt _, OTyBigarrayIntElt _, 2) then
        "Helpers.of_array2_clayout"
      case (TyFloat _, TyFloat _, OTyBigarrayFloat64Elt _, 2) then
        "Helpers.of_array2_clayout"
      case (_, _, _, _) then errorSingle [info] "Cannot convert bigarray"
      end
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
end

lang OCamlDataConversionMExpr = OCamlDataConversion + OCamlAst + MExprAst
  + OCamlDataConversionBase
  + OCamlDataConversionOpaque
  + OCamlDataConversionFun
  + OCamlDataConversionString
  + OCamlDataConversionList
  + OCamlDataConversionArray
  + OCamlDataConversionTuple
  + OCamlDataConversionRecords
  + OCamlDataConversionBigArray
end

-- A naive implementation of external generation where we just pick the
-- implementation with the lowest cost with respect to the type given at the
-- external term definition.
lang OCamlGenerateExternalNaive =
  OCamlDataConversionMExpr + OCamlChooseExternalImpl + ExtAst

  sem chooseExternalImpls implsMap env =
  | TmExt {ident = ident, tyIdent = tyIdent, inexpr = inexpr, info = info} ->
    let identStr = nameGetStr ident in
    let impls = mapLookup identStr implsMap in

    let cost = lam ty1. lam ty2.
      match convertData info env uunit_ (ty1, ty2) with (cost, _) in cost
    in

    match impls with Some (![] & impls) then
      let impl =
        minOrElse
          (lam. error "impossible")
          (lam r1 : ExternalImpl. lam r2 : ExternalImpl.
             let cost1 = cost r1.ty tyIdent in
             let cost2 = cost r2.ty tyIdent in
             subi cost1 cost2)
        impls
      in
      let env = { env with exts = mapInsert ident [impl] env.exts } in
      chooseExternalImpls implsMap env inexpr
    else
      let errMsg = join ["No implementation for external ", identStr, "."] in
      let errMsg =
        match mapLookup identStr globalExternalImplsMap with Some impls then
          join [
            errMsg,
            " Try to install one of the following set of OCaml packages: ",
            strJoin " "
              (map
                (lam x: ExternalImpl. join ["[", strJoin "," x.libraries, "]"])
                impls)
          ]
        else errMsg
      in
      errorSingle [info] errMsg
  | t -> sfold_Expr_Expr (chooseExternalImpls implsMap) env t
end
