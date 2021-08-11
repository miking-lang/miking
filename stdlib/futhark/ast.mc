-- Defines an incomplete AST for the Futhark programming language.

include "assoc-seq.mc"
include "mexpr/ast.mc" -- to reuse PatNamed definition

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
  | FPNamed { ident : PatName }
  | FPInt { val : Int }
  | FPBool { val : Bool }
  | FPRecord { bindings : Map SID FutPat }
end

lang FutharkTypeAst = FutharkTypeParamAst
  syn FutType =
  | FTyUnknown ()
  | FTyInt ()
  | FTyFloat ()
  | FTyBool ()
  | FTyIdent { ident : Name }
  | FTyArray { elem : FutType, dim : Option Name }
  | FTyRecord { fields : Map SID FutType }
  | FTyArrow { from : FutType, to : FutType }
  | FTyParamsApp { ty : FutType, params : [FutTypeParam] }
end

lang FutharkExprAst = FutharkConstAst + FutharkPatAst + FutharkTypeAst
  syn FutExpr =
  | FEVar { ident : Name }
  | FEBuiltIn { str : String }
  | FERecord { fields : Map SID FutExpr }
  | FERecordProj { rec : FutExpr, key : SID }
  | FEArray { tms : [FutExpr] }
  | FEArrayAccess { array : FutExpr, index : FutExpr }
  | FEArrayUpdate { array : FutExpr, index : FutExpr, value : FutExpr }
  | FEArraySlice { array : FutExpr, startIdx : FutExpr, endIdx : FutExpr }
  | FEConst { val : FutConst }
  | FELam { ident : Name, body : FutExpr }
  | FEApp { lhs : FutExpr, rhs : FutExpr }
  | FELet { ident : Name, tyBody : FutType, body : FutExpr, inexpr : FutExpr }
  | FEIf { cond : FutExpr, thn : FutExpr, els : FutExpr }
  | FEForEach { param : FutExpr, loopVar : Name, seq : FutExpr, body : FutExpr }
  | FEMatch { target : FutExpr, cases : [(FutPat, FutExpr)] }

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
               params : [(Name, FutType)], ret : FutType, body : FutExpr }
  | FDeclConst { ident : Name, ty : FutType, val : FutExpr }
  | FDeclType { ident : Name, typeParams : [FutTypeParam], ty : FutType }

  syn FutProg =
  | FProg { decls : [FutDecl] }
end
