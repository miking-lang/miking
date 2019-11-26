/*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   parser.mly includes the grammar for parsing the two languages 'mcore' and
   'Ragnar'. The latter is used for implementing the Miking compiler.
*/

%{

  open Ustring.Op
  open Msg
  open Ast

  (** Create a new info, taking left and right part *)
  let mkinfo fi1 fi2 =
    match (fi1,fi2) with
      | (Info(fn,r1,c1,_,_), Info(_,_,_,r2,c2)) -> Info(fn,r1,c1,r2,c2)
      | (Info(fn,r1,c1,r2,c2), NoInfo) -> Info(fn,r1,c1,r2,c2)
      | (NoInfo, Info(fn,r1,c1,r2,c2)) -> Info(fn,r1,c1,r2,c2)
      | (_,_) -> NoInfo

  let is_upper c =
    let a = Ustring.get (us"A") 0 in
    let z = Ustring.get (us"Z") 0 in
    a <= c && c <= z
%}

/* Misc tokens */
%token EOF
%token <Ustring.ustring Ast.tokendata> IDENT
%token <Ustring.ustring Ast.tokendata> STRING
%token <Ustring.ustring Ast.tokendata> CHAR
%token <int Ast.tokendata> UINT
%token <float Ast.tokendata> UFLOAT

/* Keywords */
%token <unit Ast.tokendata> IF
%token <unit Ast.tokendata> THEN
%token <unit Ast.tokendata> ELSE
%token <unit Ast.tokendata> TRUE
%token <unit Ast.tokendata> FALSE
%token <unit Ast.tokendata> MATCH
%token <unit Ast.tokendata> WITH
%token <unit Ast.tokendata> UTEST
%token <unit Ast.tokendata> TYPE
%token <unit Ast.tokendata> CON
%token <unit Ast.tokendata> LANG
%token <unit Ast.tokendata> LET
%token <unit Ast.tokendata> REC
%token <unit Ast.tokendata> LAM
%token <unit Ast.tokendata> IN
%token <unit Ast.tokendata> END
%token <unit Ast.tokendata> SYN
%token <unit Ast.tokendata> SEM
%token <unit Ast.tokendata> USE
%token <unit Ast.tokendata> MEXPR
%token <unit Ast.tokendata> INCLUDE

%token <unit Ast.tokendata> EQ            /* "="   */
%token <unit Ast.tokendata> ARROW         /* "->"  */
%token <unit Ast.tokendata> ADD           /* "+"   */

/* Symbolic Tokens */
%token <unit Ast.tokendata> LPAREN        /* "("   */
%token <unit Ast.tokendata> RPAREN        /* ")"   */
%token <unit Ast.tokendata> LSQUARE       /* "["   */
%token <unit Ast.tokendata> RSQUARE       /* "]"   */
%token <unit Ast.tokendata> COLON         /* ":"   */
%token <unit Ast.tokendata> COMMA         /* ","   */
%token <unit Ast.tokendata> DOT           /* "."   */
%token <unit Ast.tokendata> BAR           /* "|"   */

%start main

%type <Ast.program> main

%%

main:
  | includes tops mexpr_opt EOF
    { Program ($1, $2, $3) }

includes:
  | include_ includes
    { $1 :: $2 }
  |
    { [] }

include_:
  | INCLUDE STRING
    { let fi = mkinfo $1.i $2.i in
      Include(fi, $2.v) }

mexpr_opt:
  | MEXPR mexpr
    { $2 }
  |
    { TmConst(NoInfo, Cunit) }

tops:
  | top tops
    { $1 :: $2 }
  |
    { [] }
  // TODO: These should matter with a type system
  | TYPE IDENT tops
    { $3 }
  | TYPE IDENT EQ ty tops
    { $5 }

top:
  | mlang
    { TopLang($1) }
  | toplet
    { TopLet($1) }
  | topRecLet
    { TopRecLet($1) }
  | topcon
    { TopCon($1) }

toplet:
  | LET IDENT ty_op EQ mexpr
    { let fi = mkinfo $1.i $4.i in
      Let (fi, $2.v, $5) }

topRecLet:
  | REC lets END
    { let fi = mkinfo $1.i $3.i in
      RecLet (fi, $2) }

topcon:
  | CON IDENT ty_op
    { let fi = mkinfo $1.i $2.i in
      Con (fi, $2.v, $3) }

mlang:
  | LANG IDENT lang_includes lang_body
    { let fi = if List.length $3 > 0 then
                 mkinfo $1.i (List.nth $3 (List.length $3 - 1)).i
               else
                 mkinfo $1.i $2.i
      in
      Lang (fi, $2.v, List.map (fun l -> l.v) $3, $4) }

lang_includes:
  | EQ lang_list
    { $2 }
  |
    { [] }
lang_list:
  | IDENT ADD lang_list
    { $1 :: $3 }
  | IDENT
    { [$1] }

lang_body:
  | decls END
    { $1 }
  |
    { [] }
decls:
  | decl decls
    { $1 :: $2 }
  |
    { [] }
decl:
  | SYN IDENT EQ constrs
    { let fi = mkinfo $1.i $3.i in
      Data (fi, $2.v, $4) }
  | SEM IDENT params EQ cases
    { let fi = mkinfo $1.i $4.i in
      Inter (fi, $2.v, $3, $5) }

constrs:
  | constr constrs
    { $1 :: $2 }
  |
    { [] }
constr:
  | BAR IDENT constr_params
    { let fi = mkinfo $1.i $2.i in
      CDecl(fi, $2.v, $3) }

constr_params:
  | ty
    { $1 }
  |
    { TyUnit }

params:
  | LPAREN IDENT COLON ty RPAREN params
    { let fi = mkinfo $1.i $5.i in
      Param (fi, $2.v, $4) :: $6 }
  |
    { [] }

cases:
  | case cases
    { $1 :: $2 }
  |
    { [] }
case:
  | BAR IDENT ARROW mexpr
    { let fi = mkinfo $1.i $3.i in
      let c = Ustring.get $2.v 0 in
      if is_upper c
      then (ConPattern (fi, $2.v, None), $4)
      else (VarPattern (fi, $2.v), $4)}
  | BAR IDENT binder ARROW mexpr
    { let fi = mkinfo $1.i $4.i in
      (ConPattern (fi, $2.v, Some $3), $5)}
binder:
  | LPAREN IDENT RPAREN
    { $2.v }
  | IDENT
    { $1.v }

/// Expression language ///////////////////////////////



mexpr:
  | left
      { $1 }
  | TYPE IDENT IN mexpr
      { $4 }
  | TYPE IDENT EQ ty IN mexpr
      { $6 }
  | REC lets IN mexpr
      { let fi = mkinfo $1.i $3.i in
         TmRecLets(fi,$2,$4) }
  | LET IDENT ty_op EQ mexpr IN mexpr
      { let fi = mkinfo $1.i $6.i in
        TmLet(fi,$2.v,$5,$7) }
  | LAM IDENT ty_op DOT mexpr
      { let fi = mkinfo $1.i (tm_info $5) in
        TmLam(fi,$2.v,$3,$5) }
  | IF mexpr THEN mexpr ELSE mexpr
      { let fi = mkinfo $1.i (tm_info $6) in
        TmIf(fi,$2,$4,$6) }
  | CON IDENT ty_op IN mexpr
      { let fi = mkinfo $1.i $4.i in
        TmCondef(fi,$2.v,$3,$5)}
  | MATCH mexpr WITH IDENT ident_op THEN mexpr ELSE mexpr
      { let fi = mkinfo $1.i $8.i in
         TmMatch(fi,$2,$4.v,noidx,$5,$7,$9) }
  | USE IDENT IN mexpr
      { let fi = mkinfo $1.i $3.i in
        TmUse(fi,$2.v,$4) }
  | UTEST mexpr WITH mexpr IN mexpr
      { let fi = mkinfo $1.i (tm_info $4) in
        TmUtest(fi,$2,$4,$6) }

lets:
  | LET IDENT ty_op EQ mexpr
      { let fi = mkinfo $1.i (tm_info $5) in
        [(fi, $2.v, $5)] }
  | LET IDENT ty_op EQ mexpr lets
      { let fi = mkinfo $1.i (tm_info $5) in
         (fi, $2.v, $5)::$6 }



left:
  | atom
      { $1 }
  | left atom
      { let fi = mkinfo (tm_info $1) (tm_info $2) in
        TmApp(fi,$1,$2) }


atom:
  | atom DOT UINT        { TmProj(mkinfo (tm_info $1) $3.i, $1, $3.v) }
  | LPAREN seq RPAREN    { if List.length $2 = 1 then List.hd $2
                           else TmTuple(mkinfo $1.i $3.i,$2) }
  | LPAREN RPAREN        { TmConst($1.i, Cunit) }
  | IDENT                { TmVar($1.i,$1.v,noidx) }
  | CHAR                 { TmConst($1.i, CChar(List.hd (ustring2list $1.v))) }
  | UINT                 { TmConst($1.i,CInt($1.v)) }
  | UFLOAT               { TmConst($1.i,CFloat($1.v)) }
  | TRUE                 { TmConst($1.i,CBool(true)) }
  | FALSE                { TmConst($1.i,CBool(false)) }
  | STRING               { TmConst($1.i, CSeq(List.map (fun x -> TmConst($1.i,CChar(x)))
                                                       (ustring2list $1.v))) }
  | LSQUARE seq RSQUARE  { TmSeq(mkinfo $1.i $3.i, $2) }
  | LSQUARE RSQUARE      { TmSeq(mkinfo $1.i $2.i, []) }


ident_op:
  | IDENT
      { Some($1.v) }
  |
      { None }


seq:
  | mexpr
      { [$1] }
  | mexpr COMMA seq
      { $1::$3 }



ty_op:
  | COLON ty
      { $2 }
  |
      { TyDyn }


ty:
  | ty_atom
      { $1 }
  | ty_atom ARROW ty
      { TyArrow($1,$3) }


ty_atom:
  | LPAREN RPAREN
      { TyUnit }
  | LPAREN ty RPAREN
      { $2 }
  | LSQUARE ty RSQUARE
      { TySeq($2) }
  | LPAREN ty COMMA ty_list RPAREN
      { TyTuple ($2::$4) }
  | IDENT
      {match Ustring.to_utf8 $1.v with
       | "Dyn"    -> TyDyn
       | "Bool"   -> TyBool
       | "Int"    -> TyInt
       | "Float"  -> TyFloat
       | "Char"   -> TyChar
       | "String" -> TySeq(TyChar)
       | s        -> TyCon(us s)
      }
ty_list:
  | ty COMMA ty_list
    { $1 :: $3 }
  | ty
    { [$1] }
