-- Defines an incomplete AST for the Futhark programming language.

lang FutharkAst
  syn FutConst =
  | FCAdd ()
  | FCSub ()
  | FCMul ()
  | FCDiv ()
  | FCRem ()
  | FCEq ()
  | FCNeq ()
  | FCGt ()
  | FCLt ()
  | FCOr ()
  | FCAnd ()
  | FCXor ()

  syn FutExpr =
  | FEVar { ident : Name }
  | FEInt64 { val : Int }
  | FEFloat64 { val : Float }
  | FERecord { fields : Map SID FutExpr }
  | FEArray { tms : [FutExpr] }
  | FEConst { val : FutConst }
  | FELam { ident : Name, body : FutExpr }
  | FEApp { lhs : FutExpr, rhs : FutExpr }
  | FELet { ident : Name, body : FutExpr, inexpr : FutExpr }
  | FERecordProj { rec : FutExpr, key : SID }

  syn FutType =
  | FTyIdent { ident : Name }
  | FTyArray { elem : FutType, dim : Option Int }
  | FTyRecord { fields : Map SID FutType }

  syn FutDecl =
  | FDeclFun { ident : Name, entry : Bool, params : [(Name, FutType)],
               ret : FutType, body : FutExpr }
  | FDeclConst { ident : Name, ty : FutType, val : FutExpr }

  syn FutProg =
  | FProg { decls : [FutDecl] }
end
