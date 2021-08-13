-- Identifies all positions where the given Futhark AST violates any of the
-- following restrictions imposed on higher-order functions:
-- 1. Arrays of functions
-- 2. Function returned from if-expression
-- 3. Loop parameter cannot be a function
--
-- If the type of an involved term is unknown, it is assumed to not violate any
-- of the above constraints.

include "futhark/ast.mc"
include "futhark/ast-builder.mc"

lang FutharkFunctionRestrictions = FutharkAst
  -- NOTE(larshum, 2021-08-13): We use this type to represent an error in the
  -- program. By using this instead of exiting on the first error, we can both
  -- report multiple errors at once, and we can also unit test the behaviour.
  syn FutharkFunctionError =
  | FunctionInArray Info
  | FunctionFromIf Info
  | FunctionLoopParameter Info

  sem pprintFutharkFunctionError =
  | FunctionInArray info ->
    infoErrorString info "Futhark does not permit functions in arrays"
  | FunctionFromIf info ->
    infoErrorString info (join ["Futhark does not allow the result of a ",
                                "conditional expression to be a function"])
  | FunctionLoopParameter info ->
    infoErrorString info (join ["Cannot translate expression operating on ",
                                "functions to Futhark"])

  sem findFutharkFunctionViolationsExpr (errors : [FutharkFunctionError]) =
  | (FEArray _) & t ->
    match tyFutTm t with FTyArray {elem = elemTy} then
      match elemTy with FTyArrow _ then
        cons (FunctionInArray (infoFutTm t)) errors
      else errors
    else errors
  | (FEIf _) & t ->
    match tyFutTm t with FTyArrow _ then
      cons (FunctionFromIf (infoFutTm t)) errors
    else errors
  | (FEForEach {param = param}) & t ->
    match tyFutTm param with FTyArrow _ then
      cons (FunctionLoopParameter (infoFutTm t)) errors
    else errors
  | t -> sfold_FExpr_FExpr findFutharkFunctionViolationsExpr errors t

  sem findFutharkFunctionViolationsDecl (errors : [FutharkFunctionError]) =
  | FDeclFun t -> findFutharkFunctionViolationsExpr errors t.body
  | FDeclConst t -> findFutharkFunctionViolationsExpr errors t.val
  | FDeclType t -> errors

  sem findFutharkFunctionViolations =
  | FProg t ->
    reverse (foldl findFutharkFunctionViolationsDecl [] t.decls)

  sem reportFutharkFunctionViolations =
  | FProg t ->
    let errors = findFutharkFunctionViolations (FProg t) in
    if null errors then ()
    else
      let msg = strJoin "\n" (map pprintFutharkFunctionError errors) in
      error msg
end

mexpr

use FutharkFunctionRestrictions in

let futProgram = lam decls. FProg {decls = decls} in
let futFun = lam body.
  FDeclFun {ident = nameSym "f", entry = true, typeParams = [], params = [],
            ret = futUnknownTy_, body = body, info = NoInfo ()} in
let futConst = lam val.
  FDeclConst {ident = nameSym "f", ty = futUnknownTy_, val = val,
              info = NoInfo ()} in

let x = nameSym "x" in
let t = futProgram [futFun (FEArray {
  tms = [nFutLam_ x (nFutVar_ x)],
  ty = futUnsizedArrayTy_ (futArrowTy_ futIntTy_ futIntTy_),
  info = NoInfo ()})] in
utest findFutharkFunctionViolations t with [FunctionInArray (NoInfo ())] in

let t = futProgram [futFun (FEIf {
  cond = futAppSeq_ (futConst_ (FCLt ())) [futInt_ 0, futInt_ 1],
  thn = nFutLam_ x (nFutVar_ x),
  els = nFutLam_ x (futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ x, futInt_ 1]),
  ty = futArrowTy_ futIntTy_ futIntTy_,
  info = NoInfo ()})] in
utest findFutharkFunctionViolations t with [FunctionFromIf (NoInfo ())] in

let t = futProgram [futFun (
  futForEach_
    (FELam {ident = x, body = nFutVar_ x,
            ty = FTyArrow {from = futIntTy_, to = futIntTy_, info = NoInfo ()},
            info = NoInfo ()})
    x
    (futUnsizedArrayTy_ [])
    (futUnit_ ()))] in
utest findFutharkFunctionViolations t with [FunctionLoopParameter (NoInfo ())] in

let t = futProgram [futConst (nuFutLet_ x (futInt_ 3))] in
utest findFutharkFunctionViolations t with [] in
utest reportFutharkFunctionViolations t with () in

let y = nameSym "y" in
let z = nameSym "z" in
let combined = futProgram [
  futConst (FEArray {
    tms = [nFutLam_ x (nFutVar_ x)],
    ty = futUnsizedArrayTy_ (futArrowTy_ futIntTy_ futIntTy_),
    info = NoInfo ()}),
  futFun (futBindall_ [
    nuFutLet_ x
      (FEIf {
        cond = futAppSeq_ (futConst_ (FCLt ())) [futInt_ 0, futInt_ 1],
        thn = nFutLam_ y (nFutVar_ y),
        els = nFutLam_ y (futAppSeq_ (futConst_ (FCAdd ())) [nFutVar_ y, futInt_ 1]),
        ty = futArrowTy_ futIntTy_ futIntTy_,
        info = NoInfo ()}),
    futForEach_
      (FELam {ident = y, body = nFutVar_ x,
              ty = FTyArrow {from = futIntTy_, to = futIntTy_, info = NoInfo ()},
              info = NoInfo ()})
      z
      (futArray_ [])
      (futUnit_ ())])
] in
utest findFutharkFunctionViolations combined
with [FunctionInArray (NoInfo ()), FunctionFromIf (NoInfo ()),
      FunctionLoopParameter (NoInfo ())] in

-- reportFutharkFunctionViolations combined ;

()
