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
  | FELam { idents : [Name], body : FutExpr }
  | FEApp { lhs : FutExpr, rhs : FutExpr }
  | FELet { ident : Name, tyBody : FutType, body : FutExpr, inexpr : FutExpr }
  | FEIf { cond : FutExpr, thn : FutExpr, els : FutExpr }
  | FEFor { param : FutExpr, loopVar : Name, boundVar : Name, thn : FutExpr }
  | FEMatch { target : FutExpr, cases : [(FutPat, FutExpr)] }
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
