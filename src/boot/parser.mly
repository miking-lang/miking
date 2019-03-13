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


(* Create kind when optionally available *)
let mkop_kind fi op =
  match op with
  | None -> KindStar(fi)
  | Some(k) -> k

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
%token <unit Ast.tokendata> CASE
%token <unit Ast.tokendata> UTEST
%token <unit Ast.tokendata> TYPE
%token <unit Ast.tokendata> DATA
%token <unit Ast.tokendata> LANG
%token <unit Ast.tokendata> MCORE
%token <unit Ast.tokendata> PMCORE
%token <unit Ast.tokendata> LET
%token <unit Ast.tokendata> LAM
%token <unit Ast.tokendata> BIGLAM
%token <unit Ast.tokendata> ALL
%token <unit Ast.tokendata> NOP
%token <unit Ast.tokendata> FIX
%token <unit Ast.tokendata> DIVE
%token <unit Ast.tokendata> IFEXP
%token <unit Ast.tokendata> COMPOSE




%token <unit Ast.tokendata> EQ            /* "="   */
%token <unit Ast.tokendata> ARROW         /* "->"  */
%token <unit Ast.tokendata> ADD           /* "+"   */
%token <unit Ast.tokendata> SUB           /* "-"   */
%token <unit Ast.tokendata> MUL           /* "*"   */
%token <unit Ast.tokendata> DIV           /* "/"   */
%token <unit Ast.tokendata> MOD           /* "%"   */
%token <unit Ast.tokendata> LESS          /* "<"   */
%token <unit Ast.tokendata> LESSEQUAL     /* "<="  */
%token <unit Ast.tokendata> GREAT         /* ">"   */
%token <unit Ast.tokendata> GREATEQUAL    /* ">="  */
%token <unit Ast.tokendata> SHIFTLL       /* "<<"  */
%token <unit Ast.tokendata> SHIFTRL       /* ">>"  */
%token <unit Ast.tokendata> SHIFTRA       /* ">>>" */
%token <unit Ast.tokendata> EQUAL         /* "=="  */
%token <unit Ast.tokendata> NOTEQUAL      /* "!="  */
%token <unit Ast.tokendata> NOT           /* "!"   */
%token <unit Ast.tokendata> OR            /* "||"  */
%token <unit Ast.tokendata> AND           /* "&&"  */
%token <unit Ast.tokendata> CONCAT        /* "++"  */
%token <unit Ast.tokendata> DOLLAR        /* "$"   */



/* Symbolic Tokens */
%token <unit Ast.tokendata> LPAREN        /* "("   */
%token <unit Ast.tokendata> RPAREN        /* ")"   */
%token <unit Ast.tokendata> LSQUARE       /* "["   */
%token <unit Ast.tokendata> RSQUARE       /* "]"   */
%token <unit Ast.tokendata> LCURLY        /* "{"   */
%token <unit Ast.tokendata> RCURLY        /* "}"   */
%token <unit Ast.tokendata> CONS          /* "::"  */
%token <unit Ast.tokendata> COLON         /* ":"   */
%token <unit Ast.tokendata> COMMA         /* ","   */
%token <unit Ast.tokendata> DOT           /* "."   */
%token <unit Ast.tokendata> BAR           /* "|"   */
%token <unit Ast.tokendata> ARROW         /* "->"  */
%token <unit Ast.tokendata> DARROW        /* "=>"  */

%start main

%left OR   /*prec 2*/
%left AND  /*prec 3*/
%left LESS LESSEQUAL GREAT GREATEQUAL EQUAL NOTEQUAL /*prec 6*/
%left CONCAT
%left SHIFTLL SHIFTRL SHIFTRA
%nonassoc NOT /*prec 8 */
%left ADD SUB /*prec 8*/
%left MUL DIV MOD /*prec 9*/




%type <Ast.tm> main

%%

main:
  | LANG MCORE module_body EOF
      { $3 }
  | LANG MCORE module_term EOF
      { $3 }
  | LANG PMCORE module_term EOF
      { $3 }


module_term:
  | LCURLY op_self_var module_body RCURLY
      { $3 }

op_self_var:
  |
      { None }
  | IDENT DOT
      { Some $1.v }

module_body:
  | { TmNop }
  | UTEST atom atom module_body
      { let fi = mkinfo $1.i (tm_info $3) in
        TmUtest(fi,$2,$3,$4) }
  | LET IDENT EQ term module_body
      { let fi = mkinfo $1.i (tm_info $4) in
        TmApp(fi,TmLam(fi,$2.v,TyDyn,$5),$4) }
  | TYPE IDENT CONS kind module_body
      { $5 }
/*      { let fi = mkinfo $1.i (tm_info $3) in
        TmDefType(fi,$2.v,$3) }
*/
  | DATA IDENT COLON ty module_body
      { $5 }
/*      { let fi = mkinfo $1.i (tm_info $3) in
        TmDefCon(fi,$2,$3)}
*/


term:
  | cases
      { $1 }
  | LAM IDENT ty_op DOT term
      { let fi = mkinfo $1.i (tm_info $5) in
        TmLam(fi,$2.v,$3,$5) }
  | BIGLAM IDENT op_kind DOT term
      { let fi = mkinfo $1.i (tm_info $5) in
        TmTyLam(fi,$2.v,mkop_kind $2.i $3,$5) }
  | MATCH term WITH term
      { $4 }
  | module_term
      { TmNop }
  | COMPOSE atom atom
      { TmNop }



/*      { let fi = mkinfo $1.i (tm_info $4) in
        TmMatch(fi,$2,$4) }
*/


cases:
  | case
      { $1 }
  | case BAR cases
      { TmNop }
/*
    { let fi = mkinfo (tm_info $1) (tm_info $3) in
      TmCaseComp(fi,$1,$3) }
*/

case:
  | left
      { $1 }
  | CASE IDENT name_lst ARROW left
      { TmNop }
/*
      { let fi = mkinfo $1.i $6.i in
        TmCase(fi,$2.v,List.rev $4,$7) }
*/



left:
  | atom
      { $1 }
  | left atom
      { let fi = mkinfo (tm_info $1) (tm_info $2) in
        TmApp(fi,$1,$2) }
  | left LSQUARE ty RSQUARE
      { let fi = mkinfo (tm_info $1) $4.i in
        TmTyApp(fi,$1,$3) }



atom:
  | LPAREN term RPAREN   { $2 }
  | IDENT                { TmVar($1.i,$1.v,noidx,false) }
  | CHAR                 { TmChar($1.i, List.hd (ustring2list $1.v)) }
  | STRING               { ustring2uctm $1.i $1.v }
  | UINT                 { TmConst($1.i,CInt($1.v)) }
  | UFLOAT               { TmConst($1.i,CFloat($1.v)) }
  | TRUE                 { TmConst($1.i,CBool(true)) }
  | FALSE                { TmConst($1.i,CBool(false)) }
  | NOP                  { TmNop }
  | FIX                  { TmFix($1.i) }
  | DIVE                 { TmDive($1.i) }
  | IFEXP                { TmIfexp($1.i,None,None) }
  | atom DOT IDENT       { TmNop }


name_lst:
  |
    { [] }
  | IDENT name_lst
    { $1::$2 }




ty_op:
  | COLON ty
      { $2 }
  |
      { TyDyn }



ty:
  | ty_left
    { $1 }
  | ty_left ARROW ty
      { let fi = mkinfo (ty_info $1) (ty_info $3) in
        TyArrow(fi,$1,$3) }
  | ALL IDENT op_kind DOT ty
      { let fi = mkinfo $1.i (ty_info $5) in
        TyAll(fi,$2.v,mkop_kind $2.i $3,$5) }
  | LAM IDENT op_kind DOT ty
      { let fi = mkinfo $1.i (ty_info $5) in
        TyLam(fi,$2.v,mkop_kind $2.i $3,$5) }


ty_left:
  | ty_atom
      { $1 }
  | ty_left ty_atom
      { let fi = mkinfo (ty_info $1) (ty_info $2) in
        TyApp(fi,$1,$2) }



ty_atom:
  | LPAREN ty RPAREN
      { $2 }
  | IDENT
      {match Ustring.to_utf8 $1.v with
       | "Bool" -> TyGround($1.i,GBool)
       | "Int" -> TyGround($1.i,GInt)
       | "Float" -> TyGround($1.i,GFloat)
       | "String" -> TyGround($1.i,GVoid)  (* TODO *)
       | "Void" -> TyGround($1.i,GVoid)
       | _ -> TyVar($1.i,$1.v,-1)
      }




op_kind:
  |
      { None }
  | CONS kind
      { Some($2) }


kind:
  | kind_atom
      { $1 }
  | kind_atom ARROW kind
      { let fi = mkinfo (kind_info $1) (kind_info $3) in
        KindArrow(fi,$1,$3) }

kind_atom:
  | MUL
      { KindStar($1.i) }
  | LPAREN kind RPAREN
      { $2 }
