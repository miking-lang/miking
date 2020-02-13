include "string.mc"

lang VarAst
  syn Expr =
  | TmVar {ident : String}
end

lang VarPat
  syn Pat =
  | PVar {ident : String}
end


lang AppAst
  syn Expr =
  | TmApp {lhs : Expr,
           rhs : Expr}
end


lang FunAst = VarAst + AppAst
  syn Type =
  | TyArrow {from : Type,
             to   : Type}
  syn Expr =
  | TmLam {ident : String,
           tpe   : Option,
           body  : Expr}
end


lang LetAst = VarAst
  syn Expr =
  | TmLet {ident  : String,
           tpe    : Option,
           body   : Expr,
           inexpr : Expr}
end


lang RecLetsAst = VarAst
  syn Type =
  syn Expr =
  | TmRecLets {bindings : [{ident : String,
                            tpe   : Option,
                            body  : Expr}],
               inexpr   : Expr}
end


lang ConstAst
  syn Const =

  syn Expr =
  | TmConst {val : Const}
end


lang UnitAst = ConstAst
  syn Const =
  | CUnit {}
end

lang UnitPat = UnitAst
  syn Pat =
  | PUnit {}
end


lang IntAst = ConstAst
  syn Const =
  | CInt {val : Int}
end

lang IntPat = IntAst
  syn Pat =
  | PInt {val : Int}
end


lang ArithIntAst = ConstAst + IntAst
  syn Const =
  | CAddi {}
  | CSubi {}
  | CMuli {}
end


lang FloatAst = ConstAst
  syn Const =
  | CFloat {val : Float}
end


lang ArithFloatAst = ConstAst + FloatAst
  syn Const =
  | CAddf {}
  | CSubf {}
  | CMulf {}
  | CDivf {}
  | CNegf {}
end

lang BoolAst
  syn Const =
  | CBool {val : Bool}
  | CNot {}
  | CAnd {}
  | COr {}

  syn Expr =
  | TmIf {cond : Expr,
          thn  : Expr,
          els  : Expr}
end

lang BoolPat = BoolAst
  syn Pat =
  | PBool {val : Bool}
end


lang CmpAst = IntAst + BoolAst
  syn Const =
  | CEqi {}
  | CLti {}
end


lang CharAst = ConstAst
  syn Const =
  | CChar {val : Char}
end


lang SeqAst = IntAst
  syn Const =
  | CSeq {tms : [Expr]}
  | CNth {}

  syn Expr =
  | TmSeq {tms : [Expr]}
end


lang TupleAst
  syn Expr =
  | TmTuple {tms : [Expr]}
  | TmProj {tup : Expr,
            idx : Int}
end

lang TuplePat = TupleAst
  syn Pat =
  | PTuple {pats : [Pat]}
end


lang RecordAst
  syn Expr =
  | TmRecord {bindings : [{key   : String,
                           value : Expr}]}
  | TmRecordProj {rec : Expr,
                  key : String}
  | TmRecordUpdate {rec   : Expr,
                    key   : String,
                    value : Expr}
end


lang DataAst
  -- TODO: Constructors have no generated symbols
  syn Expr =
  | TmConDef {ident  : String,
              tpe    : Option,
              inexpr : Expr}
  | TmConFun {ident : String}
end

lang DataPat = DataAst
  syn Pat =
  | PCon {ident  : String,
          subpat : Pat}
end


lang MatchAst
  syn Expr =
  | TmMatch {target : Expr,
             pat    : Pat,
             thn    : Expr,
             els    : Expr}

  syn Pat =
end

lang UtestAst
  syn Expr =
  | TmUtest {test     : Expr,
             expected : Expr,
             next     : Expr}
end


lang DynTypeAst
  syn Type =
  | TyDyn {}
end

lang UnitTypeAst
  syn Type =
  | TyUnit {}
end

lang CharTypeAst
  syn Type =
  | TyChar {}
  | TyString {}
end

lang SeqTypeAst
  syn Type =
  | TySeq {tpe : Type}
end

lang TupleTypeAst
  syn Type =
  | TyProd {tpes : [Type]}
end

lang RecordTypeAst
  syn Type =
  | TyRecord {tpes : [{ident : String,
                       tpe   : Type}]}
end

lang DataTypeAst
  syn Type =
  | TyCon {ident : String}
end

lang ArithTypeAst
  syn Type =
  | TyInt {}
end

lang BoolTypeAst
  syn Type =
  | TyBool {}
end

lang AppTypeAst
  syn Type =
  | TyApp {lhs : Type, rhs : Type}
end


lang MExprAst =
  VarAst + AppAst + FunAst + LetAst + RecLetsAst + ConstAst +
  UnitAst + UnitPat + IntAst + IntPat + ArithIntAst +
  FloatAst + ArithFloatAst + BoolAst + BoolPat + CmpAst + CharAst +
  SeqAst + TupleAst + TuplePat + DataAst + DataPat + MatchAst + VarPat +
  UtestAst
