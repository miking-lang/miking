-- Defines an incomplete AST for the Futhark programming language.

lang FutharkAst
  syn FutConst =
  | FCInt { val : Int }
  | FCFloat { val : Float }
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
  | FCMap ()
  | FCMap2 ()

  syn FutExpr =
  | FEVar { ident : Name }
  | FERecord { fields : Map SID FutExpr }
  | FERecordProj { rec : FutExpr, key : SID }
  | FEArray { tms : [FutExpr] }
  | FEConst { val : FutConst }
  | FELam { idents : [Name], body : FutExpr }
  | FEApp { lhs : FutExpr, rhs : FutExpr }
  | FELet { ident : Name, ty : FutType, body : FutExpr, inexpr : FutExpr }

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
