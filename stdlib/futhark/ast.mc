-- Defines an incomplete AST for the Futhark programming language.

include "assoc-seq.mc"
include "mexpr/ast.mc" -- to reuse PatNamed definition
include "mexpr/info.mc"

lang FutharkLiteralSizeAst
  syn FutIntSize =
  | I8
  | I16
  | I32
  | I64
  | U8
  | U16
  | U32
  | U64

  syn FutFloatSize =
  | F32
  | F64
end

lang FutharkTypeParamAst
  syn FutTypeParam =
  | FPSize {val : Name}
  | FPType {val : Name}

  sem futTypeParamIdent =
  | FPSize t -> t.val
  | FPType t -> t.val
end

lang FutharkConstAst = FutharkLiteralSizeAst
  syn FutConst =
  | FCInt { val : Int, sz : Option FutIntSize }
  | FCFloat { val : Float, sz : Option FutFloatSize }
  | FCBool { val : Bool }
  | FCAdd ()
  | FCSub ()
  | FCMul ()
  | FCDiv ()
  | FCNegi ()
  | FCNegf ()
  | FCRem ()
  | FCFloatFloor ()
  | FCFloat2Int ()
  | FCInt2Float ()
  | FCEq ()
  | FCNeq ()
  | FCGt ()
  | FCLt ()
  | FCGeq ()
  | FCLeq ()
  | FCAnd ()
  | FCOr ()
  | FCBitAnd ()
  | FCBitOr ()
  | FCBitXor ()
  | FCSrl ()
  | FCSll ()
  | FCMap ()
  | FCMap2 ()
  | FCReduce ()
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
  | FCReplicate ()
  | FCTabulate ()
  | FCCopy ()
end

lang FutharkTypeAst = FutharkTypeParamAst + FutharkLiteralSizeAst
  syn FutArrayDim =
  | NamedDim Name
  | AbsDim Int

  syn FutType =
  | FTyUnknown { info : Info }
  | FTyInt { info : Info, sz : FutIntSize }
  | FTyFloat { info : Info, sz : FutFloatSize }
  | FTyBool { info : Info }
  | FTyIdent { ident : Name, info : Info }
  | FTyArray { elem : FutType, dim : Option FutArrayDim, info : Info }
  | FTyRecord { fields : Map SID FutType, info : Info }
  | FTyProj { target : FutType, label : SID, info : Info }
  | FTyArrow { from : FutType, to : FutType, info : Info }
  | FTyAll { ident : Name, ty : FutType, info : Info }

  sem infoFutTy =
  | FTyUnknown t -> t.info
  | FTyInt t -> t.info
  | FTyFloat t -> t.info
  | FTyBool t -> t.info
  | FTyIdent t -> t.info
  | FTyArray t -> t.info
  | FTyRecord t -> t.info
  | FTyProj t -> t.info
  | FTyArrow t -> t.info
  | FTyAll t -> t.info

  sem withInfoFutTy (info : Info) =
  | FTyUnknown t -> FTyUnknown {t with info = info}
  | FTyInt t -> FTyInt {t with info = info}
  | FTyFloat t -> FTyFloat {t with info = info}
  | FTyBool t -> FTyBool {t with info = info}
  | FTyIdent t -> FTyIdent {t with info = info}
  | FTyArray t -> FTyArray {t with info = info}
  | FTyRecord t -> FTyRecord {t with info = info}
  | FTyProj t -> FTyProj {t with info = info}
  | FTyArrow t -> FTyArrow {t with info = info}
  | FTyAll t -> FTyAll {t with info = info}

  sem smapAccumL_FType_FType : all a. (a -> FutType -> (a, FutType)) -> a
                                    -> FutType -> (a, FutType)
  sem smapAccumL_FType_FType f acc =
  | FTyArray t ->
    match f acc t.elem with (acc, elem) in
    (acc, FTyArray {t with elem = elem})
  | FTyRecord t ->
    match mapMapAccum (lam acc. lam. lam e. f acc e) acc t.fields with (acc, fields) in
    (acc, FTyRecord {t with fields = fields})
  | FTyProj t ->
    match f acc t.target with (acc, target) in
    (acc, FTyProj {t with target = target})
  | FTyArrow t ->
    match f acc t.from with (acc, from) in
    match f acc t.to with (acc, to) in
    (acc, FTyArrow {{t with from = from} with to = to})
  | FTyAll t ->
    match f acc t.ty with (acc, ty) in
    (acc, FTyAll {t with ty = ty})
  | t -> (acc, t)

  sem smap_FType_FType : (FutType -> FutType) -> FutType -> FutType
  sem smap_FType_FType f =
  | t ->
    let res : ((), FutType) = smapAccumL_FType_FType (lam. lam a. ((), f a)) () t in
    res.1

  sem sfold_FType_FType : all a. (a -> FutType -> a) -> a -> FutType -> a
  sem sfold_FType_FType f acc =
  | t ->
    let res : (a, FutType) = smapAccumL_FType_FType (lam acc. lam a. (f acc a, a)) acc t in
    res.0
end

lang FutharkPatAst = FutharkTypeAst
  syn FutPat =
  | FPNamed { ident : PatName, ty : FutType, info : Info }
  | FPInt { val : Int, ty : FutType, info : Info }
  | FPBool { val : Bool, ty : FutType, info : Info }
  | FPRecord { bindings : Map SID FutPat, ty : FutType, info : Info }

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

  sem tyFutPat =
  | FPNamed t -> t.ty
  | FPInt t -> t.ty
  | FPBool t -> t.ty
  | FPRecord t -> t.ty

  sem withTypeFutPat (ty : FutType) =
  | FPNamed t -> FPNamed {t with ty = ty}
  | FPInt t -> FPInt {t with ty = ty}
  | FPBool t -> FPBool {t with ty = ty}
  | FPRecord t -> FPRecord {t with ty = ty}
end

lang FutharkExprAst = FutharkConstAst + FutharkPatAst + FutharkTypeAst
  syn FutExpr =
  | FEVar { ident : Name, ty : FutType, info : Info }
  | FEVarExt { ident : String, ty : FutType, info : Info }
  | FESizeCoercion { e : FutExpr, ty : FutType, info : Info }
  | FESizeEquality { x1 : Name, d1 : Int, x2 : Name, d2 : Int, ty : FutType,
                     info : Info }
  | FEProj { target : FutExpr, label : SID, ty : FutType, info : Info }
  | FERecord { fields : Map SID FutExpr, ty : FutType, info : Info }
  | FERecordUpdate { rec : FutExpr, key : SID, value : FutExpr, ty : FutType,
                     info : Info }
  | FEArray { tms : [FutExpr], ty : FutType, info : Info }
  | FEArrayAccess { array : FutExpr, index : FutExpr, ty : FutType,
                    info : Info }
  | FEArrayUpdate { array : FutExpr, index : FutExpr, value : FutExpr,
                    ty : FutType, info : Info }
  | FEArraySlice { array : FutExpr, startIdx : FutExpr, endIdx : FutExpr,
                   ty : FutType, info : Info }
  | FEConst { val : FutConst, ty : FutType, info : Info }
  | FELam { ident : Name, body : FutExpr, ty : FutType, info : Info }
  | FEApp { lhs : FutExpr, rhs : FutExpr, ty : FutType, info : Info }
  | FELet { ident : Name, tyBody : FutType, body : FutExpr, inexpr : FutExpr,
            ty : FutType, info : Info }
  | FEIf { cond : FutExpr, thn : FutExpr, els : FutExpr, ty : FutType,
           info : Info }
  | FEForEach { param : (FutPat, FutExpr), loopVar : Name, seq : FutExpr,
                body : FutExpr, ty : FutType, info : Info }
  | FEMatch { target : FutExpr, cases : [(FutPat, FutExpr)], ty : FutType,
              info : Info }

  sem infoFutTm : FutExpr -> Info
  sem infoFutTm =
  | FEVar t -> t.info
  | FEVarExt t -> t.info
  | FESizeCoercion t -> t.info
  | FESizeEquality t -> t.info
  | FEProj t -> t.info
  | FERecord t -> t.info
  | FERecordUpdate t -> t.info
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

  sem withInfoFutTm : Info -> FutExpr -> FutExpr
  sem withInfoFutTm info =
  | FEVar t -> FEVar {t with info = info}
  | FEVarExt t -> FEVarExt {t with info = info}
  | FESizeCoercion t -> FESizeCoercion {t with info = info}
  | FESizeEquality t -> FESizeEquality {t with info = info}
  | FEProj t -> FEProj {t with info = info}
  | FERecord t -> FERecord {t with info = info}
  | FERecordUpdate t -> FERecordUpdate {t with info = info}
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

  sem tyFutTm : FutExpr -> FutType
  sem tyFutTm =
  | FEVar t -> t.ty
  | FEVarExt t -> t.ty
  | FESizeCoercion t -> t.ty
  | FESizeEquality t -> t.ty
  | FEProj t -> t.ty
  | FERecord t -> t.ty
  | FERecordUpdate t -> t.ty
  | FEArray t -> t.ty
  | FEArrayAccess t -> t.ty
  | FEArrayUpdate t -> t.ty
  | FEArraySlice t -> t.ty
  | FEConst t -> t.ty
  | FELam t -> t.ty
  | FEApp t -> t.ty
  | FELet t -> t.ty
  | FEIf t -> t.ty
  | FEForEach t -> t.ty
  | FEMatch t -> t.ty

  sem withTypeFutTm : FutType -> FutExpr -> FutExpr
  sem withTypeFutTm ty =
  | FEVar t -> FEVar {t with ty = ty}
  | FEVarExt t -> FEVarExt {t with ty = ty}
  | FESizeCoercion t -> FESizeCoercion {t with ty = ty}
  | FESizeEquality t -> FESizeEquality {t with ty = ty}
  | FEProj t -> FEProj {t with ty = ty}
  | FERecord t -> FERecord {t with ty = ty}
  | FERecordUpdate t -> FERecordUpdate {t with ty = ty}
  | FEArray t -> FEArray {t with ty = ty}
  | FEArrayAccess t -> FEArrayAccess {t with ty = ty}
  | FEArrayUpdate t -> FEArrayUpdate {t with ty = ty}
  | FEArraySlice t -> FEArraySlice {t with ty = ty}
  | FEConst t -> FEConst {t with ty = ty}
  | FELam t -> FELam {t with ty = ty}
  | FEApp t -> FEApp {t with ty = ty}
  | FELet t -> FELet {t with ty = ty}
  | FEIf t -> FEIf {t with ty = ty}
  | FEForEach t -> FEForEach {t with ty = ty}
  | FEMatch t -> FEMatch {t with ty = ty}

  sem smapAccumL_FExpr_FExpr : all a. (a -> FutExpr -> (a, FutExpr)) -> a
                                    -> FutExpr -> (a, FutExpr)
  sem smapAccumL_FExpr_FExpr f acc =
  | FESizeCoercion t ->
    match f acc t.e with (acc, e) in
    (acc, FESizeCoercion {t with e = e})
  | FEProj t ->
    match f acc t.target with (acc, target) in
    (acc, FEProj {t with target = target})
  | FERecord t ->
    match mapMapAccum (lam acc. lam. lam v. f acc v) acc t.fields with (acc, fields) in
    (acc, FERecord {t with fields = fields})
  | FERecordUpdate t ->
    match f acc t.rec with (acc, rec) in
    match f acc t.value with (acc, value) in
    (acc, FERecordUpdate {{t with rec = rec} with value = value})
  | FEArray t ->
    match mapAccumL f acc t.tms with (acc, tms) in
    (acc, FEArray {t with tms = tms})
  | FEArrayAccess t ->
    match f acc t.array with (acc, array) in
    match f acc t.index with (acc, index) in
    (acc, FEArrayAccess {{t with array = array} with index = index})
  | FEArrayUpdate t ->
    match f acc t.array with (acc, array) in
    match f acc t.index with (acc, index) in
    match f acc t.value with (acc, value) in
    (acc, FEArrayUpdate {{{t with array = array}
                             with index = index}
                             with value = value})
  | FEArraySlice t ->
    match f acc t.array with (acc, array) in
    match f acc t.startIdx with (acc, startIdx) in
    match f acc t.endIdx with (acc, endIdx) in
    (acc, FEArraySlice {{{t with array = array}
                            with startIdx = startIdx}
                            with endIdx = endIdx})
  | FELam t ->
    match f acc t.body with (acc, body) in
    (acc, FELam {t with body = body})
  | FEApp t ->
    match f acc t.lhs with (acc, lhs) in
    match f acc t.rhs with (acc, rhs) in
    (acc, FEApp {{t with lhs = lhs} with rhs = rhs})
  | FELet t ->
    match f acc t.body with (acc, body) in
    match f acc t.inexpr with (acc, inexpr) in
    (acc, FELet {{t with body = body} with inexpr = inexpr})
  | FEIf t ->
    match f acc t.cond with (acc, cond) in
    match f acc t.thn with (acc, thn) in
    match f acc t.els with (acc, els) in
    (acc, FEIf {{{t with cond = cond} with thn = thn} with els = els})
  | FEForEach t ->
    match f acc t.param.1 with (acc, paramExpr) in
    match f acc t.seq with (acc, seq) in
    match f acc t.body with (acc, body) in
    (acc, FEForEach {{{t with param = (t.param.0, paramExpr)}
                         with seq = seq}
                         with body = body})
  | FEMatch t ->
    let caseFunc = lam acc. lam patExpr : (FutPat, FutExpr).
      match f acc patExpr.1 with (acc, expr) in
      (acc, (patExpr.0, expr))
    in
    match f acc t.target with (acc, target) in
    match mapAccumL caseFunc acc t.cases with (acc, cases) in
    (acc, FEMatch {{t with target = target} with cases = cases})
  | t -> (acc, t)

  sem smap_FExpr_FExpr : (FutExpr -> FutExpr) -> FutExpr -> FutExpr
  sem smap_FExpr_FExpr f =
  | t ->
    match smapAccumL_FExpr_FExpr (lam. lam a. ((), f a)) () t with (_, e) in
    e

  sem sfold_FExpr_FExpr : all a. (a -> FutExpr -> a) -> a -> FutExpr -> a
  sem sfold_FExpr_FExpr f acc =
  | t ->
    match smapAccumL_FExpr_FExpr (lam acc. lam a. (f acc a, a)) acc t with (acc, _) in
    acc
end

lang FutharkAst = FutharkTypeParamAst + FutharkTypeAst + FutharkExprAst
  syn FutDecl =
  | FDeclFun { ident : Name, entry : Bool, typeParams : [FutTypeParam],
               params : [(Name, FutType)], ret : FutType, body : FutExpr,
               info : Info }
  | FDeclConst { ident : Name, ty : FutType, val : FutExpr, info : Info }
  | FDeclType { ident : Name, typeParams : [FutTypeParam], ty : FutType,
                info : Info }
  | FDeclModuleAlias { ident : Name, moduleId : String, info : Info }

  syn FutProg =
  | FProg { decls : [FutDecl] }
end
