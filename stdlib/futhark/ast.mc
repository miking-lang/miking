-- Defines an incomplete AST for the Futhark programming language.

lang FutharkAst
  syn FutTypeParam =
  | FPSize {val : Name}
  | FPType {val : Name}

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
  | FEArrayAccess { array : FutExpr, index : FutExpr }
  | FEConst { val : FutConst }
  | FELam { idents : [Name], body : FutExpr }
  | FEApp { lhs : FutExpr, rhs : FutExpr }
  | FELet { ident : Name, ty : FutType, body : FutExpr, inexpr : FutExpr }

  syn FutType =
  | FTyInt ()
  | FTyFloat ()
  | FTyIdent { ident : Name }
  | FTyArray { elem : FutType, dim : Option FutExpr }
  | FTyRecord { fields : Map SID FutType }

  syn FutDecl =
  | FDeclFun { ident : Name, entry : Bool, typeParams : [FutTypeParam],
               params : [(Name, FutType)], ret : FutType, body : FutExpr }
  | FDeclConst { ident : Name, ty : FutType, val : FutExpr }

  syn FutProg =
  | FProg { decls : [FutDecl] }
end
