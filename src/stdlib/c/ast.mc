-- AST fragment for a subset of the C language, suitable for code generation.

-- NOTE(dlunde,2020-10-29): Missing functionality (most things are probably not
-- needed for code generation or can be expressed through other language
-- constructs):
--
-- * Labeled statements and goto
-- * Storage class specifiers (typedef, auto, register, static, extern)
-- * Type qualifiers (const, volatile)
-- * Increment/decrement operators
-- * Combined assignment operators (e.g. +=, *=)
-- * Ternary operator (cond ? expr : expr)
-- * DoWhile, For
--
-- The above list is of course not exhaustive.

-- NOTE(dlunde,2020-10-30):
--
-- * Definitions have optional identifiers and initializers to allow for
--   declaring struct/union/enum types without instantiating them
--
--   struct ty { ... members ... };
--
--   and to initialize variables directly
--
--   int arr[] = {1, 2, 3};
--
--   To keep the AST clean, however, this currently also allows for incorrect
--   definitions such as
--
--   int *;
--
--   int = 1;
--
--   which are not valid in C.
--
-- * Furthermore, to support anonymous structs and unions, the tag is also
--   optional, thus allowing
--
--   struct;
--
--   union;
--
--   which are also not valid in C.

include "name.mc"
include "option.mc"
include "externals.mc"

-----------------------------
-- C TYPES AND EXPRESSIONS --
-----------------------------
lang CExprTypeAst

  syn CType =
  | CTyVar    { id: Name }
  | CTyChar   {}
  | CTyInt    {}
  | CTyInt32  {}
  | CTyInt64  {}
  | CTyFloat  {}
  | CTyDouble {}
  | CTyVoid   {}
  | CTyPtr    { ty: CType }
  | CTyFun    { ret: CType, params: [CType] }
  | CTyArray  { ty: CType, size: Option CExpr }
  | CTyStruct { id: Option Name, mem: Option [(CType,Option Name)] }
  | CTyUnion  { id: Option Name, mem: Option [(CType,Option Name)] }
  | CTyEnum   { id: Option Name, mem: Option [Name] }

  sem _mapAccumLMem
    : all acc. (acc -> CType -> (acc, CType)) -> acc
      -> Option [(CType,Option Name)] -> (acc, Option [(CType,Option Name)])
  sem _mapAccumLMem f acc =
  | mem ->
    let fMem = lam acc. lam memEntry : (CType, Option Name).
      match memEntry with (ty, optId) in
      match f acc ty with (acc, ty) in
      (acc, (ty, optId)) in
    match mem with Some mem then
      match mapAccumL fMem acc mem with (acc, mem) in
      (acc, Some mem)
    else (acc, mem)

  sem smapAccumLCTypeCType
    : all acc. (acc -> CType -> (acc, CType)) -> acc -> CType -> (acc, CType)
  sem smapAccumLCTypeCType f acc =
  | CTyPtr t ->
    match f acc t.ty with (acc, ty) in
    (acc, CTyPtr {t with ty = ty})
  | CTyFun t ->
    match f acc t.ret with (acc, ret) in
    match mapAccumL f acc t.params with (acc, params) in
    (acc, CTyFun {{t with ret = ret} with params = params})
  | CTyArray t ->
    match f acc t.ty with (acc, ty) in
    (acc, CTyArray {t with ty = ty})
  | CTyStruct t ->
    match _mapAccumLMem f acc t.mem with (acc, mem) in
    (acc, CTyStruct {t with mem = mem})
  | CTyUnion t ->
    match _mapAccumLMem f acc t.mem with (acc, mem) in
    (acc, CTyStruct {t with mem = mem})
  | ty -> (acc, ty)

  sem smapCTypeCType : (CType -> CType) -> CType -> CType
  sem smapCTypeCType f =
  | p ->
    match smapAccumLCTypeCType (lam. lam a. ((), f a)) () p with (_, p) in p

  sem sfoldCTypeCType : all acc. (acc -> CType -> acc) -> acc -> CType -> acc
  sem sfoldCTypeCType f acc =
  | p ->
    match smapAccumLCTypeCType (lam acc. lam a. (f acc a, a)) acc p
    with (acc, _) in
    acc

  syn CExpr =
  | CEVar        /- Variables -/            { id: Name }
  | CEApp        /- Function application -/ { fun: Name, args: [CExpr] }
  | CEInt        /- Integer literals -/     { i: Int }
  | CEFloat      /- Float literals -/       { f: Float }
  | CEChar       /- Character literals -/   { c: Char }
  | CEString     /- String literals -/      { s: String }
  | CEBinOp      /- Binary operators -/     { op: CBinOp,
                                              lhs: CExpr,
                                              rhs: CExpr }
  | CEUnOp       /- Unary operators -/      { op: CUnOp, arg: CExpr }
  | CEMember     /- lhs.id -/               { lhs: CExpr, id: Name }
  | CEArrow      /- lhs->id -/              { lhs: CExpr, id: Name }
  | CECast       /- (ty) rhs -/             { ty: CType, rhs: CExpr }
  | CESizeOfType /- sizeof(ty) -/           { ty: CType }

  sem smapAccumLCExprCExpr
    : all acc. (acc -> CExpr -> (acc, CExpr)) -> acc -> CExpr -> (acc, CExpr)
  sem smapAccumLCExprCExpr f acc =
  | CEApp t ->
    match mapAccumL f acc t.args with (acc, args) in
    (acc, CEApp {t with args = args})
  | CEBinOp t ->
    match f acc t.lhs with (acc, lhs) in
    match f acc t.rhs with (acc, rhs) in
    (acc, CEBinOp {{t with lhs = lhs} with rhs = rhs})
  | CEUnOp t ->
    match f acc t.arg with (acc, arg) in
    (acc, CEUnOp {t with arg = arg})
  | CEMember t ->
    match f acc t.lhs with (acc, lhs) in
    (acc, CEMember {t with lhs = lhs})
  | CEArrow t ->
    match f acc t.lhs with (acc, lhs) in
    (acc, CEArrow {t with lhs = lhs})
  | CECast t ->
    match f acc t.rhs with (acc, rhs) in
    (acc, CECast {t with rhs = rhs})
  | (CEVar _ | CEInt _ | CEFloat _ | CEChar _ | CEString _ | CESizeOfType _) & ty ->
    (acc, ty)

  sem smap_CExpr_CExpr (f: CExpr -> CExpr) =
  | p ->
    match smapAccumLCExprCExpr (lam. lam a. ((), f a)) () p with (_, p) in p

  sem sfold_CExpr_CExpr : all acc. (acc -> CExpr -> acc) -> acc -> CExpr -> acc
  sem sfold_CExpr_CExpr f acc =
  | p ->
    match smapAccumLCExprCExpr (lam acc. lam a. (f acc a, a)) acc p
    with (acc, _) in
    acc

  syn CBinOp =
  | COAssign    /- lhs = rhs -/  {}
  | COSubScript /- lhs[rhs] -/   {}
  | COOr        /- lhs || rhs -/ {}
  | COAnd       /- lhs && rhs -/ {}
  | COEq        /- lhs == rhs -/ {}
  | CONeq       /- lhs != rhs -/ {}
  | COLt        /- lhs < rhs -/  {}
  | COGt        /- lhs > rhs -/  {}
  | COLe        /- lhs <= rhs -/ {}
  | COGe        /- lhs >= rhs -/ {}
  | COShiftL    /- lhs << rhs -/ {}
  | COShiftR    /- lhs >> rhs -/ {}
  | COAdd       /- lhs + rhs -/  {}
  | COSub       /- lhs - rhs -/  {}
  | COMul       /- lhs * rhs -/  {}
  | CODiv       /- lhs / rhs -/  {}
  | COMod       /- lhs % rhs -/  {}
  | COBOr       /- lhs | rhs -/  {}
  | COBAnd      /- lhs & rhs -/  {}
  | COXor       /- lhs ^ rhs -/  {}

  syn CUnOp =
  | COSizeOf /- sizeof(arg) -/ {}
  | CODeref  /- *arg -/        {}
  | COAddrOf /- &arg -/        {}
  | CONeg    /- -arg -/        {}
  | CONot    /- ~arg -/        {}

end


--------------------
-- C INITIALIZERS --
--------------------
lang CInitAst = CExprTypeAst

  syn CInit =
  | CIExpr { expr: CExpr }
  | CIList { inits: [CInit] }

  sem sfold_CInit_CExpr : all acc. (acc -> CExpr -> acc) -> acc -> CInit -> acc
  sem sfold_CInit_CExpr f acc =
  | CIExpr t -> f acc t.expr
  | CIList t -> foldl (sfold_CInit_CExpr f) acc t.inits

  sem smap_CInit_CExpr (f: CExpr -> CExpr) =
  | CIExpr t -> CIExpr { t with expr = f t.expr }
  | CIList t -> CIList { t with inits = map (smap_CInit_CExpr f) t.inits }

end

------------------
-- C STATEMENTS --
------------------
lang CStmtAst = CInitAst + CExprTypeAst
  -- We force if, switch, and while to introduce new scopes (by setting the
  -- body type to [CStmt] rather than CStmt). It is allowed in C to have a
  -- single (i.e., not compound) statement as the body, but this statement is
  -- NOT allowed to be a definition. To do this properly, we would need to have
  -- separate data types for statements and definitions.

  syn CStmt =
  | CSDef     { ty: CType, id: Option Name, init: Option CInit }
  | CSIf      { cond: CExpr, thn: [CStmt], els: [CStmt] }
  | CSSwitch  { cond: CExpr, body: [(Int, [CStmt])], default: Option [CStmt] }
  | CSWhile   { cond: CExpr, body: [CStmt] }
  | CSExpr    { expr: CExpr }
  | CSComp    { stmts: [CStmt] }
  | CSRet     { val: Option CExpr }
  | CSCont    {}
  | CSBreak   {}
  | CSNop     {}

  sem smapAccumLCStmtCStmt : all acc. (acc -> CStmt -> (acc, CStmt)) -> acc
                                      -> CStmt -> (acc, CStmt)
  sem smapAccumLCStmtCStmt f acc =
  | CSIf t ->
    match mapAccumL f acc t.thn with (acc, thn) in
    match mapAccumL f acc t.els with (acc, els) in
    (acc, CSIf {{t with thn = thn} with els = els})
  | CSSwitch t ->
    let bodyFn = lam acc. lam caseArg : (Int, [CStmt]).
      match caseArg with (i, stmts) in
      match mapAccumL f acc stmts with (acc, stmts) in
      (acc, (i, stmts))
    in
    match mapAccumL bodyFn acc t.body with (acc, body) in
    match optionMapAccum (mapAccumL f) acc t.default with (acc, default) in
    (acc, CSSwitch {{t with body = body} with default = default})
  | CSWhile t ->
    match mapAccumL f acc t.body with (acc, body) in
    (acc, CSWhile {t with body = body})
  | CSComp t ->
    match mapAccumL f acc t.stmts with (acc, stmts) in
    (acc, CSComp {t with stmts = stmts})
  | stmt -> (acc, stmt)

  sem smap_CStmt_CStmt : (CStmt -> CStmt) -> CStmt -> CStmt
  sem smap_CStmt_CStmt f =
  | stmt ->
    match smapAccumLCStmtCStmt (lam. lam a. ((), f a)) () stmt with (_, stmt) in
    stmt

  sem sfold_CStmt_CStmt : all acc. (acc -> CStmt -> acc) -> acc -> CStmt -> acc
  sem sfold_CStmt_CStmt f acc =
  | stmt ->
    match smapAccumLCStmtCStmt (lam acc. lam a. (f acc a, a)) acc stmt
    with (acc, _) in
    acc

  sem sfold_CStmt_CExpr : all acc. (acc -> CExpr -> acc) -> acc -> CStmt -> acc
  sem sfold_CStmt_CExpr f acc =
  | CSDef t -> optionMapOrElse (lam. acc) (sfold_CInit_CExpr f acc) t.init
  | CSIf t ->
    let sf = sfold_CStmt_CExpr f in
    foldl sf (foldl sf (f acc t.cond) t.thn) t.els
  | CSSwitch t -> error "TODO"
  | CSWhile t -> error "TODO"
  | CSExpr t -> f acc t.expr
  | CSComp t -> error "TODO"
  | CSRet t -> optionMapOrElse (lam. acc) (f acc) t.val
  | CSCont _ -> acc
  | CSBreak _ -> acc
  | CSNop _ -> acc

  sem smap_CStmt_CExpr (f: CExpr -> CExpr) =
  | CSDef t ->
    let init = optionMap (smap_CInit_CExpr f) t.init in
    CSDef { t with init = init }
  | CSIf t ->
    let sf = smap_CStmt_CExpr f in
    CSIf {{{ t with cond = f t.cond}
               with thn = map (smap_CStmt_CExpr f) t.thn }
               with els = map (smap_CStmt_CExpr f) t.els }
  | CSSwitch t -> error "TODO"
  | CSWhile t -> error "TODO"
  | CSExpr t -> CSExpr { t with expr = f t.expr }
  | CSComp t -> error "TODO"
  | CSRet t -> CSRet { t with val = optionMap f t.val }
  | CSCont _ & t -> t
  | CSBreak _ & t -> t
  | CSNop _ & t -> t

  sem sreplace_CStmt_CStmt (f: CStmt -> [CStmt]) =
  | CSDef t -> CSDef t
  | CSIf t ->
    let thn = join (map f t.thn) in
    let els = join (map f t.els) in
    CSIf {{ t with thn = thn } with els = els }
  | CSSwitch t -> error "TODO"
  | CSWhile t -> error "TODO"
  | CSExpr t -> CSExpr t
  | CSComp t -> error "TODO"
  | CSRet t -> CSRet t
  | CSCont t -> CSCont t
  | CSBreak t -> CSBreak t
  | CSNop t -> CSNop t

end


-----------------
-- C TOP-LEVEL --
-----------------
lang CTopAst = CExprTypeAst + CInitAst + CStmtAst

  syn CTop =
  -- Type definitions are supported at this level.
  | CTTyDef { ty: CType, id: Name }
  | CTDef { ty: CType, id: Option Name, init: Option CInit }
  | CTFun { ret: CType, id: Name, params: [(CType,Name)], body: [CStmt] }

  sem smap_CTop_CExpr (f: CExpr -> CExpr) =
  | CTTyDef _ & t -> t
  | CTDef t -> CTDef { t with init = optionMap (smap_CInit_CExpr f) t.init }
  | CTFun t -> CTFun { t with body = map (smap_CStmt_CExpr f) t.body }

  sem sreplace_CTop_CStmt (f: CStmt -> [CStmt]) =
  | CTTyDef _ & t -> t
  | CTDef _ & t -> t
  | CTFun t -> CTFun { t with body = join (map f t.body) }

  sem sfold_CTop_CStmt : all acc. (acc -> CStmt -> acc) -> acc -> CTop -> acc
  sem sfold_CTop_CStmt f acc =
  | CTTyDef _ -> acc
  | CTDef _ -> acc
  | CTFun t -> foldl f acc t.body

end

-----------------------
-- COMBINED FRAGMENT --
-----------------------
lang CAst = CExprTypeAst + CInitAst + CStmtAst + CTopAst
end

---------------
-- C PROGRAM --
---------------
lang CProgAst = CTopAst
  -- We support including a set of header files at the top of the program.

  syn CProg =
  | CPProg { includes: [String], tops: [CTop] }

end
