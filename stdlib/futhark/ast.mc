-- Defines an incomplete AST for the Futhark programming language.

include "mexpr/ast.mc" -- to reuse PatNamed definition

lang FutharkAst
  syn FutTypeParam =
  | FPSize {val : Name}
  | FPType {val : Name}

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

  syn FutPat =
  | FPNamed { ident : PatName }
  | FPInt { val : Int }
  | FPBool { val : Bool }
  | FPRecord { bindings : Map SID FutPat }

  syn FutExpr =
  | FEVar { ident : Name }
  | FEBuiltIn { str : String }
  | FERecord { fields : Map SID FutExpr }
  | FERecordProj { rec : FutExpr, key : SID }
  | FEArray { tms : [FutExpr] }
  | FEArrayAccess { array : FutExpr, index : FutExpr }
  | FEArrayUpdate { array : FutExpr, index : FutExpr, value : FutExpr }
  | FEConst { val : FutConst }
  | FELam { idents : [Name], body : FutExpr }
  | FEApp { lhs : FutExpr, rhs : FutExpr }
  | FELet { ident : Name, tyBody : Option FutType, body : FutExpr, inexpr : FutExpr }
  | FEIf { cond : FutExpr, thn : FutExpr, els : FutExpr }
  | FEFor { param : FutExpr, loopVar : Name, boundVar : Name, thn : FutExpr }
  | FEMatch { target : FutExpr, cases : [(FutPat, FutExpr)] }

  syn FutType =
  | FTyInt ()
  | FTyFloat ()
  | FTyBool ()
  | FTyIdent { ident : Name }
  | FTyArray { elem : FutType, dim : Option FutExpr }
  | FTyRecord { fields : Map SID FutType }
  | FTyArrow { from : FutType, to : FutType }

  syn FutDecl =
  | FDeclFun { ident : Name, entry : Bool, typeParams : [FutTypeParam],
               params : [(Name, FutType)], ret : FutType, body : FutExpr }
  | FDeclConst { ident : Name, ty : FutType, val : FutExpr }
  | FDeclType { ident : Name, typeParams : [FutTypeParam], ty : FutType }

  syn FutProg =
  | FProg { decls : [FutDecl] }
end
