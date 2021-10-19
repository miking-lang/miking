include "ocaml/ast.mc"

let tyZ3Context_ = otyvarext_ "Z3.context"
let tyZ3Solver_ = otyvarext_ "Z3.Solver.solver"
let tyZ3Model_ = otyvarext_ "Z3.Model.model"
let tyZ3FuncDecl_ = otyvarext_ "Z3.FuncDecl.func_decl"
let tyZ3Symbol_ = otyvarext_ "Z3.Symbol.symbol"
let tyZ3Expr_ = otyvarext_ "Z3.Expr.expr"

let z3ExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString [
    ("externalZ3MkContext", [
      { expr = "Z3.mk_context",
        ty = tyarrow_ (otylist_ (otytuple_ [otystring_, otystring_])) tyZ3Context_,
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3MkSolver", [
      { expr = "fun ctx -> Z3.Solver.mk_solver ctx None",
        ty = tyarrow_ tyZ3Context_ tyZ3Solver_,
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3SolverAdd", [
      { expr = "fun s expr -> Z3.Solver.add s [expr]",
        ty = tyarrows_ [tyZ3Solver_, tyZ3Expr_, otyunit_],
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3SolverReset", [
      { expr = "Z3.Solver.reset",
       ty = tyarrow_ tyZ3Solver_ otyunit_,
       libraries = ["z3"],
       cLibraries = [] }
    ]),
    ("externalZ3SolverCheck", [
      { expr = "fun s -> Z3.Solver.check s []",
        ty = tyarrow_ tyZ3Solver_ otyopaque_,
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3SolverStatusInt", [
      { expr =
"function
  | Z3.Solver.UNSATISFIABLE -> 0
  | Z3.Solver.UNKNOWN -> 1
  | Z3.Solver.SATISFIABLE -> 2",
        ty = tyarrow_ otyopaque_ tyint_,
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3SolverGetModel", [
      { expr = "fun s -> Option.get (Z3.Solver.get_model s)",
        ty = tyarrow_ tyZ3Solver_ tyZ3Model_,
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3ModelGetConstInterpExpr", [
      { expr = "Z3.Model.get_const_interp_e",
        ty = tyarrows_ [tyZ3Model_, tyZ3Expr_, otyopaque_],
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3SymbolMkString", [
      { expr = "Z3.Symbol.mk_string",
        ty = tyarrows_ [tyZ3Context_, otystring_, tyZ3Symbol_],
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3ExprToString", [
      { expr = "Z3.Expr.to_string",
        ty = tyarrow_ tyZ3Expr_ otystring_,
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3MkInteger", [
      { expr = "Z3.Arithmetic.Integer.mk_const",
        ty = tyarrows_ [tyZ3Context_, tyZ3Symbol_, tyZ3Expr_],
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3MkIntegerLiteral", [
      { expr = "Z3.Arithmetic.Integer.mk_numeral_i",
        ty = tyarrows_ [tyZ3Context_, tyint_, tyZ3Expr_],
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3ArithmeticMkGt", [
      { expr = "Z3.Arithmetic.mk_gt",
        ty = tyarrows_ [tyZ3Context_, tyZ3Expr_, tyZ3Expr_, tyZ3Expr_],
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3ArithmeticMkAdd", [
      { expr = "fun ctx a b -> Z3.Arithmetic.mk_add ctx [a; b]",
        ty = tyarrows_ [tyZ3Context_, tyZ3Expr_, tyZ3Expr_, tyZ3Expr_],
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3ArithmeticMkSub", [
      { expr = "fun ctx a b -> Z3.Arithmetic.mk_sub ctx [a; b]",
        ty = tyarrows_ [tyZ3Context_, tyZ3Expr_, tyZ3Expr_, tyZ3Expr_],
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3ArithmeticMkMul", [
      { expr = "fun ctx a b -> Z3.Arithmetic.mk_mul ctx [a; b]",
        ty = tyarrows_ [tyZ3Context_, tyZ3Expr_, tyZ3Expr_, tyZ3Expr_],
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3BooleanMkEq", [
      { expr = "Z3.Boolean.mk_eq",
        ty = tyarrows_ [tyZ3Context_, tyZ3Expr_, tyZ3Expr_, tyZ3Expr_],
        libraries = ["z3"],
        cLibraries = [] }
    ]),
    ("externalZ3BooleanMkNot", [
      { expr = "Z3.Boolean.mk_not",
        ty = tyarrows_ [tyZ3Context_, tyZ3Expr_, tyZ3Expr_],
        libraries = ["z3"],
        cLibraries = [] }
    ])
  ]

