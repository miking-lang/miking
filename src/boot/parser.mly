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
%token <unit Ast.tokendata> CASE
%token <unit Ast.tokendata> UTEST
%token <unit Ast.tokendata> TYPE
%token <unit Ast.tokendata> DATA
%token <unit Ast.tokendata> LANG
%token <unit Ast.tokendata> MCORE
%token <unit Ast.tokendata> PMCORE
%token <unit Ast.tokendata> LET
%token <unit Ast.tokendata> TLET
%token <unit Ast.tokendata> LAM
%token <unit Ast.tokendata> BIGLAM
%token <unit Ast.tokendata> ALL
%token <unit Ast.tokendata> NOP
%token <unit Ast.tokendata> FIX
%token <unit Ast.tokendata> IFEXP
%token <unit Ast.tokendata> COMPOSE
%token <unit Ast.tokendata> PUB
%token <unit Ast.tokendata> IN




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


%type <Ast.program> main

%%


main:
  | mexpr EOF
    { Program(tm_info $1, [], $1) }


mexpr:
  | left
      { $1 }
  | LAM IDENT ty_op DOT mexpr
      { let fi = mkinfo $1.i (tm_info $5) in
        TmLam(fi,$2.v,$3,$5) }
  | UTEST mexpr WITH mexpr IN mexpr
      { let fi = mkinfo $1.i (tm_info $4) in
        TmUtest(fi,$2,$4,$6) }


left:
  | atom
      { $1 }
  | left atom
      { let fi = mkinfo (tm_info $1) (tm_info $2) in
        TmApp(fi,$1,$2) }


atom:
  | LPAREN mexpr RPAREN   { $2 }
  | IDENT                { TmVar($1.i,$1.v,noidx) }
  | CHAR                 { TmConst($1.i, CChar(List.hd (ustring2list $1.v))) }
  | NOP                  { TmConst($1.i, Cnop) }
  | FIX                  { TmFix($1.i) }
  | UINT                 { TmConst($1.i,CInt($1.v)) }
  | UFLOAT               { TmConst($1.i,CFloat($1.v)) }
  | TRUE                 { TmConst($1.i,CBool(true)) }
  | FALSE                { TmConst($1.i,CBool(false)) }
  | LSQUARE seq RSQUARE  { TmConst(mkinfo $1.i $3.i, CSeq($2)) }
  | LSQUARE RSQUARE      { TmConst(mkinfo $1.i $2.i, CSeq([])) }


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


ty_atom:
  | LPAREN ty RPAREN
      { $2 }
  | IDENT
      {match Ustring.to_utf8 $1.v with
       | "Dyn" -> TyDyn
       | _ -> failwith "Unknown type"
      }
