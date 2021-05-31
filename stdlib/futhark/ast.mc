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
end

lang FutharkPatAst
  syn FutPat =
  | FPNamed { ident : PatName }
  | FPInt { val : Int }
  | FPBool { val : Bool }
  | FPRecord { bindings : Map SID FutPat }
end

lang FutharkTypeAst
  syn FutType =
  | FTyInt ()
  | FTyFloat ()
  | FTyBool ()
  | FTyIdent { ident : Name }
  | FTyArray { elem : FutType, dim : Option Name }
  | FTyRecord { fields : Map SID FutType }
  | FTyArrow { from : FutType, to : FutType }
  | FTyParamsApp { ty : FutType, params : [Name] }
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
  | FEConst { val : FutConst }
  | FELam { idents : [Name], body : FutExpr }
  | FEApp { lhs : FutExpr, rhs : FutExpr }
  | FELet { ident : Name, tyBody : Option FutType, body : FutExpr, inexpr : FutExpr }
  | FEIf { cond : FutExpr, thn : FutExpr, els : FutExpr }
  | FEFor { param : FutExpr, loopVar : Name, boundVar : Name, thn : FutExpr }
  | FEMatch { target : FutExpr, cases : [(FutPat, FutExpr)] }

  sem smap_Expr_Expr (f : FutExpr -> a) =
  | FEVar t -> FEVar t
  | FEBuiltIn t -> FEBuiltIn t
  | FERecord t -> FERecord {t with fields = mapMap f t.fields}
  | FERecordProj t -> FERecordProj {t with rec = f t.rec}
  | FEArray t -> FEArray {t with tms = map f t.tms}
  | FEArrayAccess t -> FEArrayAccess {{t with array = f t.array}
                                         with index = f t.index}
  | FEArrayUpdate t -> FEArrayUpdate {{{t with array = f t.array}
                                          with index = f t.index}
                                          with value = f t.value}
  | FEConst t -> FEConst t
  | FELam t -> FELam {t with body = f t.body}
  | FEApp t -> FEApp {{t with lhs = f t.lhs} with rhs = f t.rhs}
  | FELet t -> FELet {{t with body = f t.body} with inexpr = f t.inexpr}
  | FEIf t -> FEIf {{{t with cond = f t.cond}
                        with thn = f t.thn}
                        with els = f t.els}
  | FEFor t -> FEFor {{t with param = f t.param} with thn = f t.thn}
  | FEMatch t -> FEMatch {{t with target = f t.target}
                             with cases = assocSeqMap f t.cases}
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
