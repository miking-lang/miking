/*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

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

   (** Add fix-point, if recursive function *)
  let addrec x t =
    let rec hasx t = match t with
      | TmVar(_,y,_,_) ->  x =. y
      | TmLam(_,y,_,t1) -> if x =. y then false else hasx t1
      | TmClos(_,_,_,_,_,_) -> failwith "Cannot happen"
      | TmApp(_,t1,t2) -> hasx t1 || hasx t2
      | TmConst(_,_) -> false
      | TmFix(_) -> false
      | TmTyLam(fi,x,k,t1) -> hasx t1
      | TmTyApp(fi,t1,ty1) -> hasx t1
      | TmPEval(_) -> false
      | TmIfexp(_,_,None) -> false
      | TmIfexp(_,_,Some(t1)) -> hasx t1
      | TmChar(_,_) -> false
      | TmExprSeq(_,t1,t2) -> hasx t1 || hasx t2
      | TmUC(fi,uct,ordered,uniqueness) ->
          let rec work uc = match uc with
          | UCNode(uc1,uc2) -> work uc1 || work uc2
          | UCLeaf(tms) -> List.exists hasx tms
          in work uct
      | TmUtest(fi,t1,t2,tnext) -> hasx t1 || hasx t2 || hasx tnext
      | TmMatch(fi,t1,cases) ->
          List.exists (fun (Case(_,_,t)) -> hasx t) cases
      | TmNop -> false
    in
    if hasx t then TmApp(NoInfo,TmFix(NoInfo), (TmLam(NoInfo,x,TyUndef,t))) else t


%}

/* Misc tokens */
%token EOF
%token <Ustring.ustring Ast.tokendata> IDENT
%token <Ustring.ustring Ast.tokendata> FUNIDENT
%token <Ustring.ustring Ast.tokendata> STRING
%token <Ustring.ustring Ast.tokendata> CHAR
%token <int Ast.tokendata> UINT
%token <float Ast.tokendata> UFLOAT
%token <Ustring.Op.sid Ast.tokendata> ATOM

/* Keywords */
%token <unit Ast.tokendata> FUNC
%token <unit Ast.tokendata> FUNC2
%token <unit Ast.tokendata> DEF
%token <unit Ast.tokendata> IN
%token <unit Ast.tokendata> IF
%token <unit Ast.tokendata> IF2           /* Special handling if( */
%token <unit Ast.tokendata> THEN
%token <unit Ast.tokendata> ELSE
%token <unit Ast.tokendata> TRUE
%token <unit Ast.tokendata> FALSE
%token <unit Ast.tokendata> MATCH
%token <unit Ast.tokendata> UTEST
%token <unit Ast.tokendata> TYPE
%token <unit Ast.tokendata> DATA
%token <unit Ast.tokendata> LANG
%token <unit Ast.tokendata> MCORE
%token <unit Ast.tokendata> RAGNAR
%token <unit Ast.tokendata> LET
%token <unit Ast.tokendata> LAM
%token <unit Ast.tokendata> IN
%token <unit Ast.tokendata> NOP
%token <unit Ast.tokendata> FIX
%token <unit Ast.tokendata> PEVAL
%token <unit Ast.tokendata> IFEXP




%token <unit Ast.tokendata> EQ            /* "="  */
%token <unit Ast.tokendata> ARROW         /* "->"  */
%token <unit Ast.tokendata> ADD           /* "+"  */
%token <unit Ast.tokendata> SUB           /* "-"  */
%token <unit Ast.tokendata> MUL           /* "*"  */
%token <unit Ast.tokendata> DIV           /* "/"  */
%token <unit Ast.tokendata> MOD           /* "%"  */
%token <unit Ast.tokendata> LESS          /* "<"  */
%token <unit Ast.tokendata> LESSEQUAL     /* "<=" */
%token <unit Ast.tokendata> GREAT         /* ">"  */
%token <unit Ast.tokendata> GREATEQUAL    /* ">=" */
%token <unit Ast.tokendata> SHIFTLL       /* "<<" */
%token <unit Ast.tokendata> SHIFTRL       /* ">>" */
%token <unit Ast.tokendata> SHIFTRA       /* ">>>" */
%token <unit Ast.tokendata> EQUAL         /* "==" */
%token <unit Ast.tokendata> NOTEQUAL      /* "!=" */
%token <unit Ast.tokendata> NOT           /* "!"   */
%token <unit Ast.tokendata> OR            /* "||" */
%token <unit Ast.tokendata> AND           /* "&&" */
%token <unit Ast.tokendata> CONCAT        /* "++" */



/* Symbolic Tokens */
%token <unit Ast.tokendata> LPAREN        /* "("  */
%token <unit Ast.tokendata> RPAREN        /* ")"  */
%token <unit Ast.tokendata> LSQUARE       /* "["  */
%token <unit Ast.tokendata> RSQUARE       /* "]"  */
%token <unit Ast.tokendata> LCURLY        /* "{"  */
%token <unit Ast.tokendata> RCURLY        /* "}"  */
%token <unit Ast.tokendata> CONS          /* "::" */
%token <unit Ast.tokendata> COLON         /* ":"  */
%token <unit Ast.tokendata> COMMA         /* ","  */
%token <unit Ast.tokendata> DOT           /* "."  */
%token <unit Ast.tokendata> BAR           /* "|"  */
%token <unit Ast.tokendata> ARROW         /* "->" */
%token <unit Ast.tokendata> DARROW        /* "=>" */

%start main

%left OR  /*prec 2*/
%left AND  /*prec 3*/
%left LESS LESSEQUAL GREAT GREATEQUAL EQUAL NOTEQUAL /*prec 6*/
%left CONCAT
%left SHIFTLL SHIFTRL SHIFTRA
%nonassoc NOT /*prec8 */
%left ADD SUB /*prec 8*/
%left MUL DIV MOD /*prec 9*/




%type <Ast.tm> main

%%

main:
  | mcore_scope EOF
      { $1 }


/* ********************************* MCORE **************************************** */

mcore_scope:
  | { TmNop }
  | UTEST mc_atom mc_atom mcore_scope
      { let fi = mkinfo $1.i (tm_info $3) in
        TmUtest(fi,$2,$3,$4) }
  | LET IDENT EQ mc_term mcore_scope
      { let fi = mkinfo $1.i (tm_info $4) in
        TmApp(fi,TmLam(fi,$2.v,TyUndef,$5),$4) }

mc_term:
  | mc_left
      { $1 }
  | LAM IDENT COLON ty DOT mc_term
      { let fi = mkinfo $1.i (tm_info $6) in
        TmLam(fi,$2.v,TyUndef,$6) }
  | LET IDENT EQ mc_term IN mc_term
      { let fi = mkinfo $1.i (tm_info $4) in
        TmApp(fi,TmLam(fi,$2.v,TyUndef,$6),$4) }


mc_left:
  | mc_atom
      { $1 }
  | mc_left mc_atom
      { TmApp(NoInfo,$1,$2) }

mc_atom:
  | LPAREN mc_term RPAREN   { $2 }
  | IDENT                { TmVar($1.i,$1.v,noidx,false) }
  | CHAR                 { TmChar($1.i, List.hd (ustring2list $1.v)) }
  | STRING               { ustring2uctm $1.i $1.v }
  | UINT                 { TmConst($1.i,CInt($1.v)) }
  | UFLOAT               { TmConst($1.i,CFloat($1.v)) }
  | TRUE                 { TmConst($1.i,CBool(true)) }
  | FALSE                { TmConst($1.i,CBool(false)) }
  | NOP                  { TmNop }
  | FIX                  { TmFix($1.i) }
  | PEVAL                { TmPEval($1.i) }
  | IFEXP                { TmIfexp($1.i,None,None) }
  | ATOM                 { TmConst($1.i,CAtom($1.v,[])) }




ty:
  | tyatom
      {}
  | tyatom ARROW ty
      {}

tyatom:
  | IDENT
      {}
  | LPAREN RPAREN
      {}
  | LPAREN revtypetupleseq RPAREN
      {}
  | LSQUARE ty RSQUARE
      {}
  | FUNIDENT revtyargs RPAREN
      {}


revtypetupleseq:
  | ty
      {}
  | revtypetupleseq COMMA ty
      {}

tyarg:
  | ty
      {}
  | IDENT COLON ty
      {}

revtyargs:
  |   {}
  | tyarg
      {}
  | revtyargs COMMA tyarg
      {}
