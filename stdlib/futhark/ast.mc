-- Defines an incomplete AST for the Futhark programming language.

include "assoc-seq.mc"
include "mexpr/ast.mc" -- to reuse PatNamed definition
include "mexpr/info.mc"

lang FutharkTypeParamAst
  syn FutTypeParam =
  | FPSize {val : Name}
  | FPType {val : Name}
end

lang FutharkConstAst
  syn FutConst =
  | FCInt { val : Int }
  | FCFloat { val : Float }
  | FCBool { val : Bool }
  | FCAdd ()
  | FCSub ()
  | FCMul ()
  | FCDiv ()
  | FCRem ()
  | FCFloatFloor ()
  | FCFloat2Int ()
  | FCEq ()
  | FCNeq ()
  | FCGt ()
  | FCLt ()
  | FCGeq ()
  | FCLeq ()
  | FCOr ()
  | FCAnd ()
  | FCXor ()
  | FCMap ()
  | FCMap2 ()
  | FCReduce ()
  | FCScan ()
  | FCFilter ()
  | FCPartition ()
  | FCAll ()
  | FCAny ()
  | FCFlatten ()
  | FCIndices ()
  | FCIota ()
  | FCLength ()
  | FCReverse ()
  | FCConcat ()
  | FCHead ()
  | FCTail ()
  | FCNull ()
  | FCFoldl ()
  | FCTake ()
  | FCReplicate ()
  | FCTabulate ()
end

lang FutharkPatAst
  syn FutPat =
  | FPNamed { ident : PatName, info : Info }
  | FPInt { val : Int, info : Info }
  | FPBool { val : Bool, info : Info }
  | FPRecord { bindings : Map SID FutPat, info : Info }

  sem infoFutPat =
  | FPNamed t -> t.info
  | FPInt t -> t.info
  | FPBool t -> t.info
  | FPRecord t -> t.info

  sem withInfoFutPat (info : Info) =
  | FPNamed t -> FPNamed {t with info = info}
  | FPInt t -> FPInt {t with info = info}
  | FPBool t -> FPBool {t with info = info}
  | FPRecord t -> FPRecord {t with info = info}
end

lang FutharkTypeAst = FutharkTypeParamAst
  syn FutType =
  | FTyUnknown { info : Info }
  | FTyInt { info : Info }
  | FTyFloat { info : Info }
  | FTyBool { info : Info }
  | FTyIdent { ident : Name, info : Info }
  | FTyArray { elem : FutType, dim : Option Name, info : Info }
  | FTyRecord { fields : Map SID FutType, info : Info }
  | FTyArrow { from : FutType, to : FutType, info : Info }
  | FTyParamsApp { ty : FutType, params : [FutTypeParam], info : Info }

  sem infoFutTy =
  | FTyUnknown t -> t.info
  | FTyInt t -> t.info
  | FTyFloat t -> t.info
  | FTyBool t -> t.info
  | FTyIdent t -> t.info
  | FTyArray t -> t.info
  | FTyRecord t -> t.info
  | FTyArrow t -> t.info
  | FTyParamsApp t -> t.info

  sem withInfoFutTy (info : Info) =
  | FTyUnknown t -> FTyUnknown {t with info = info}
  | FTyInt t -> FTyInt {t with info = info}
  | FTyFloat t -> FTyFloat {t with info = info}
  | FTyBool t -> FTyBool {t with info = info}
  | FTyIdent t -> FTyIdent {t with info = info}
  | FTyArray t -> FTyArray {t with info = info}
  | FTyRecord t -> FTyRecord {t with info = info}
  | FTyArrow t -> FTyArrow {t with info = info}
  | FTyParamsApp t -> FTyParamsApp {t with info = info}
end

lang FutharkExprAst = FutharkConstAst + FutharkPatAst + FutharkTypeAst
  syn FutExpr =
  | FEVar { ident : Name, info : Info }
  | FERecord { fields : Map SID FutExpr, info : Info }
  | FERecordProj { rec : FutExpr, key : SID, info : Info }
  | FEArray { tms : [FutExpr], info : Info }
  | FEArrayAccess { array : FutExpr, index : FutExpr, info : Info }
  | FEArrayUpdate { array : FutExpr, index : FutExpr, value : FutExpr,
                    info : Info }
  | FEArraySlice { array : FutExpr, startIdx : FutExpr, endIdx : FutExpr,
                   info : Info }
  | FEConst { val : FutConst, info : Info }
  | FELam { ident : Name, body : FutExpr, info : Info }
  | FEApp { lhs : FutExpr, rhs : FutExpr, info : Info }
  | FELet { ident : Name, tyBody : FutType, body : FutExpr, inexpr : FutExpr,
            info : Info }
  | FEIf { cond : FutExpr, thn : FutExpr, els : FutExpr, info : Info }
  | FEForEach { param : FutExpr, loopVar : Name, seq : FutExpr, body : FutExpr,
                info : Info }
  | FEMatch { target : FutExpr, cases : [(FutPat, FutExpr)], info : Info }

  sem infoFutTm =
  | FEVar t -> t.info
  | FERecord t -> t.info
  | FERecordProj t -> t.info
  | FEArray t -> t.info
  | FEArrayAccess t -> t.info
  | FEArrayUpdate t -> t.info
  | FEArraySlice t -> t.info
  | FEConst t -> t.info
  | FELam t -> t.info
  | FEApp t -> t.info
  | FELet t -> t.info
  | FEIf t -> t.info
  | FEForEach t -> t.info
  | FEMatch t -> t.info

  sem withInfoFutTm (info : Info) =
  | FEVar t -> FEVar {t with info = info}
  | FERecord t -> FERecord {t with info = info}
  | FERecordProj t -> FERecordProj {t with info = info}
  | FEArray t -> FEArray {t with info = info}
  | FEArrayAccess t -> FEArrayAccess {t with info = info}
  | FEArrayUpdate t -> FEArrayUpdate {t with info = info}
  | FEArraySlice t -> FEArraySlice {t with info = info}
  | FEConst t -> FEConst {t with info = info}
  | FELam t -> FELam {t with info = info}
  | FEApp t -> FEApp {t with info = info}
  | FELet t -> FELet {t with info = info}
  | FEIf t -> FEIf {t with info = info}
  | FEForEach t -> FEForEach {t with info = info}
  | FEMatch t -> FEMatch {t with info = info}

  sem smapAccumL_FExpr_FExpr (f : acc -> a -> (acc, b)) (acc : acc) =
  | FERecord t ->
    match mapMapAccum (lam acc. lam. lam v. f acc v) acc t.fields with (acc, fields) then
      (acc, FERecord {t with fields = fields})
    else never
  | FERecordProj t ->
    match f acc t.rec with (acc, rec) then
      (acc, FERecordProj {t with rec = rec})
    else never
  | FEArray t ->
    match mapAccumL f acc t.tms with (acc, tms) then
      (acc, FEArray {t with tms = tms})
    else never
  | FEArrayAccess t ->
    match f acc t.array with (acc, array) then
      match f acc t.index with (acc, index) then
        (acc, FEArrayAccess {{t with array = array} with index = index})
      else never
    else never
  | FEArrayUpdate t ->
    match f acc t.array with (acc, array) then
      match f acc t.index with (acc, index) then
        match f acc t.value with (acc, value) then
          (acc, FEArrayUpdate {{{t with array = array}
                                   with index = index}
                                   with value = value})
        else never
      else never
    else never
  | FEArraySlice t ->
    match f acc t.array with (acc, array) then
      match f acc t.startIdx with (acc, startIdx) then
        match f acc t.endIdx with (acc, endIdx) then
          (acc, FEArraySlice {{{t with array = array}
                                  with startIdx = startIdx}
                                  with endIdx = endIdx})
        else never
      else never
    else never
  | FELam t ->
    match f acc t.body with (acc, body) then
      (acc, FELam {t with body = body})
    else never
  | FEApp t ->
    match f acc t.lhs with (acc, lhs) then
      match f acc t.rhs with (acc, rhs) then
        (acc, FEApp {{t with lhs = lhs} with rhs = rhs})
      else never
    else never
  | FELet t ->
    match f acc t.body with (acc, body) then
      match f acc t.inexpr with (acc, inexpr) then
        (acc, FELet {{t with body = body} with inexpr = inexpr})
      else never
    else never
  | FEIf t ->
    match f acc t.cond with (acc, cond) then
      match f acc t.thn with (acc, thn) then
        match f acc t.els with (acc, els) then
          (acc, FEIf {{{t with cond = cond} with thn = thn} with els = els})
        else never
      else never
    else never
  | FEForEach t ->
    match f acc t.param with (acc, param) then
      match f acc t.seq with (acc, seq) then
        match f acc t.body with (acc, body) then
          (acc, FEForEach {{{t with param = param}
                               with seq = seq}
                               with body = body})
        else never
      else never
    else never
  | FEMatch t ->
    let caseFunc = lam acc. lam patExpr : (FutPat, FutExpr).
      match f acc patExpr.1 with (acc, expr) then
        (acc, (patExpr.0, expr))
      else never
    in
    match f acc t.target with (acc, target) then
      match mapAccumL caseFunc acc t.cases with (acc, cases) then
        (acc, FEMatch {{t with target = target} with cases = cases})
      else never
    else never
  | t -> (acc, t)

  sem smap_FExpr_FExpr (f : a -> b) =
  | t ->
    let res : ((), FutExpr) =
      smapAccumL_FExpr_FExpr (lam. lam a. ((), f a)) () t in
    res.1

  sem sfold_FExpr_FExpr (f : acc -> a -> acc) (acc : acc) =
  | t ->
    let res : (acc, FutExpr) =
      smapAccumL_FExpr_FExpr (lam acc. lam a. (f acc a, a)) acc t in
    res.0
end

lang FutharkAst = FutharkTypeParamAst + FutharkTypeAst + FutharkExprAst
  syn FutDecl =
  | FDeclFun { ident : Name, entry : Bool, typeParams : [FutTypeParam],
               params : [(Name, FutType)], ret : FutType, body : FutExpr,
               info : Info }
  | FDeclConst { ident : Name, ty : FutType, val : FutExpr, info : Info }
  | FDeclType { ident : Name, typeParams : [FutTypeParam], ty : FutType,
                info : Info }

  syn FutProg =
  | FProg { decls : [FutDecl] }
end
