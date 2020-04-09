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
%token <unit Ast.tokendata> LBRACKET      /* "{"   */
%token <unit Ast.tokendata> RBRACKET      /* "}"   */
%token <unit Ast.tokendata> COLON         /* ":"   */
%token <unit Ast.tokendata> COMMA         /* ","   */
%token <unit Ast.tokendata> DOT           /* "."   */
%token <unit Ast.tokendata> BAR           /* "|"   */
%token <unit Ast.tokendata> CONCAT        /* "++"  */

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
      (VarPattern (fi, $2.v), $4) }
  | BAR IDENT binder ARROW mexpr
    { let fi = mkinfo $1.i $4.i in
      (ConPattern (fi, $2.v, $3), $5)}
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
        TmMatch(fi,$2,PatBool(NoInfo,true),$4,$6) }
  | CON IDENT ty_op IN mexpr
      { let fi = mkinfo $1.i $4.i in
        TmCondef(fi,$2.v,$3,$5)}
  | MATCH mexpr WITH pat THEN mexpr ELSE mexpr
      { let fi = mkinfo $1.i (tm_info $8) in
         TmMatch(fi,$2,$4,$6,$8) }
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
  | atom DOT label       { TmProj(mkinfo (tm_info $1) $2.i, $1, $3) }
  | LPAREN seq RPAREN    { if List.length $2 = 1 then List.hd $2
                           else TmTuple(mkinfo $1.i $3.i,$2) }
  | LPAREN RPAREN        { TmConst($1.i, Cunit) }
  | IDENT                { TmVar($1.i,$1.v,noidx) }
  | CHAR                 { TmConst($1.i, CChar(List.hd (ustring2list $1.v))) }
  | UINT                 { TmConst($1.i,CInt($1.v)) }
  | UFLOAT               { TmConst($1.i,CFloat($1.v)) }
  | TRUE                 { TmConst($1.i,CBool(true)) }
  | FALSE                { TmConst($1.i,CBool(false)) }
  | STRING               { TmSeq($1.i, Mseq.map (fun x -> TmConst($1.i,CChar(x)))
                                                  (Mseq.of_ustring $1.v)) }
  | LSQUARE seq RSQUARE  { TmSeq(mkinfo $1.i $3.i, Mseq.of_list $2) }
  | LSQUARE RSQUARE      { TmSeq(mkinfo $1.i $2.i, Mseq.empty) }
  | LBRACKET labels RBRACKET    { TmRecord(mkinfo $1.i $3.i, $2)}
  | LBRACKET RBRACKET    { TmRecord(mkinfo $1.i $2.i, [])}
  | LBRACKET mexpr WITH IDENT EQ mexpr RBRACKET
      { TmRecordUpdate(mkinfo $1.i $7.i, $2, $4.v, $6) }

label:
  | UINT
    { LabIdx($1.v) }
  | IDENT
    { LabStr($1.v) }

seq:
  | mexpr
      { [$1] }
  | mexpr COMMA seq
      { $1::$3 }

labels:
  | IDENT EQ mexpr
    {[($1.v, $3)]}
  | IDENT EQ mexpr COMMA labels
    {($1.v, $3)::$5}

pats:
  | pat
      { [$1] }
  | pat COMMA pats
      { $1::$3 }

patseq:
  | LSQUARE RSQUARE
      { (mkinfo $1.i $2.i, []) }
  | LSQUARE pats RSQUARE
      { (mkinfo $1.i $3.i, $2) }
  | STRING
      { ($1.i, List.map (fun x -> PatChar($1.i,x)) (ustring2list $1.v)) }


name:
  | IDENT
      { if $1.v =. us"_"
        then PatNamed($1.i, NameWildcard)
        else PatNamed($1.i, NameStr($1.v)) }

pat:
  | name
      { $1 }
  | IDENT pat
      { PatCon(mkinfo $1.i (pat_info $2), $1.v, noidx, $2) }
  | patseq
      { PatSeq($1 |> fst, $1 |> snd |> Mseq.of_list, SeqMatchTotal) }
  | patseq CONCAT IDENT
      { PatSeq($1 |> fst, $1 |> snd |> Mseq.of_list, SeqMatchPrefix(NameStr($3.v))) }
  | IDENT CONCAT patseq
      { PatSeq($3 |> fst, $3 |> snd |> Mseq.of_list, SeqMatchPostfix(NameStr($1.v))) }
  | LPAREN pat RPAREN
      { $2 }
  | LPAREN pat COMMA pat_list RPAREN
      { let fi = mkinfo $1.i $5.i
        in PatTuple(fi, $2 :: $4) }
  | UINT /* TODO: enable matching against negative ints */
      { PatInt($1.i, $1.v) }
  | CHAR
      { PatChar($1.i, List.hd (ustring2list $1.v)) }
  | TRUE
      { PatBool($1.i, true) }
  | FALSE
      { PatBool($1.i, false) }
  | LPAREN RPAREN
      { PatUnit(mkinfo $1.i $2.i) }

pat_list:
  | pat
      { [$1] }
  | pat COMMA pat_list
      { $1 :: $3 }


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
  | LBRACKET RBRACKET
      { TyRecord [] }
  | LBRACKET label_tys RBRACKET
      { TyRecord($2) }
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

label_tys:
  | IDENT COLON ty
    {[($1.v, $3)]}
  | IDENT COLON ty COMMA label_tys
    {($1.v, $3)::$5}
