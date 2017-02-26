/* 
   Modelyze II is licensed under the MIT license. 
   Copyright (C) David Broman. See file LICENSE.txt
   
   parser.mly includes the grammar for parsing the mcore--, the subset
   that is used in the bootstrapping interpreter.
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
      | TmVar(_,y,_) ->  x =. y 
      | TmLam(_,y,t1) -> if x =. y then false else hasx t1
      | TmClos(_,_,_) -> failwith "Cannot happen"
      | TmFix(_,t1) -> hasx t1
      | TmApp(_,t1,t2) -> hasx t1 || hasx t2
      | TmInt(_,_) -> false
      | TmBool(_,_) -> false
      | TmChar(_,_) -> false
      | TmOp(_,_,t1,t2) -> hasx t1 || hasx t2
      | TmIf(_,t1,t2,t3) -> hasx t1 || hasx t2|| hasx t3
      | TmExprSeq(_,t1,t2) -> hasx t1 || hasx t2
      | TmUC(fi,uct,ordered,uniqueness) ->
          let rec work uc = match uc with
          | UCNode(uc1,uc2) -> work uc1 || work uc2
          | UCLeaf(tms) -> List.exists hasx tms
          in work uct
      | TmUtest(fi,t1,t2,tnext) -> hasx t1 || hasx t2 || hasx tnext
      | TmNop -> false
    in
    if hasx t then TmFix(NoInfo,TmLam(NoInfo,x,t)) else t
 
        
%}

/* Misc tokens */
%token EOF
%token <Ustring.ustring Ast.tokendata> IDENT
%token <Ustring.ustring Ast.tokendata> FUNIDENT
%token <Ustring.ustring Ast.tokendata> STRING
%token <Ustring.ustring Ast.tokendata> CHAR
%token <int Ast.tokendata> UINT

/* Keywords */
%token <unit Ast.tokendata> FUNC
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


%token <unit Ast.tokendata> EQ            /* "="  */
%token <unit Ast.tokendata> ADD           /* "+"  */
%token <unit Ast.tokendata> SUB           /* "-"  */
%token <unit Ast.tokendata> MUL           /* "*"  */
%token <unit Ast.tokendata> DIV           /* "/"  */
%token <unit Ast.tokendata> MOD           /* "%"  */
%token <unit Ast.tokendata> LESS          /* "<"  */
%token <unit Ast.tokendata> LESSEQUAL     /* "<=" */
%token <unit Ast.tokendata> GREAT         /* ">"  */
%token <unit Ast.tokendata> GREATEQUAL    /* ">=" */
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
%nonassoc NOT /*prec8 */
%left ADD SUB /*prec 8*/
%left MUL DIV MOD /*prec 9*/




%type <Ast.tm> main

%%

main:
  | scope EOF
      { $1 }

      

scope:
  | { TmNop }
  | term scope  {
      match $2 with
      | TmNop -> $1 
      | _ -> TmExprSeq(tm_info $1,$1,$2) }      
  | DEF FUNIDENT revidentseq RPAREN body scope
      { let fi = mkinfo $1.i (tm_info $5) in
        let rec mkfun lst = (match lst with
          | x::xs -> TmLam(fi,x,mkfun xs)
          | [] -> $5 ) in
        let f = if List.length $3 = 0 then [us"@no"] else $3 in
        TmApp(fi,TmLam(fi,$2.v,$6),addrec $2.v (mkfun (List.rev f))) } 
  | DEF IDENT body scope
      { let fi = mkinfo $1.i (tm_info $3) in 
        TmApp(fi,TmLam(fi,$2.v,$4),$3) }
  | UTEST term term scope
      { let fi = mkinfo $1.i (tm_info $3) in 
        TmUtest(fi,$2,$3,$4) }

      
body:
  | EQ op { $2 }
  | LCURLY scope RCURLY { $2 }
      
      
term:
  | op                   { $1 }      
  | FUNC IDENT LCURLY term RCURLY
      { let fi = mkinfo $1.i (tm_info $4) in
        TmLam(fi,$2.v,$4) }
  | IF term THEN term ELSE term
      { let fi = mkinfo $1.i (tm_info $6) in
        TmIf(fi,$2,$4,$6) }
  | IF2 term RPAREN term ELSE term
      { let fi = mkinfo $1.i (tm_info $6) in
        TmIf(fi,$2,$4,$6) }
  | IF term term ELSE term
      { let fi = mkinfo $1.i (tm_info $5) in
        TmIf(fi,$2,$3,$5) }
  | IDENT DARROW term
      { let fi = mkinfo $1.i (tm_info $3) in
        TmLam(fi,$1.v,$3)}

      
      
      
op:
  | atom                 { $1 }     
  | op ADD op            { TmOp($2.i,OpAdd,$1,$3) }
  | op SUB op            { TmOp($2.i,OpSub,$1,$3) }
  | op MUL op            { TmOp($2.i,OpMul,$1,$3) }
  | op DIV op            { TmOp($2.i,OpDiv,$1,$3) }
  | op MOD op            { TmOp($2.i,OpMod,$1,$3) }
  | op LESS op           { TmOp($2.i,OpLess,$1,$3) }      
  | op LESSEQUAL op      { TmOp($2.i,OpLessEqual,$1,$3) }      
  | op GREAT op          { TmOp($2.i,OpGreat,$1,$3) }      
  | op GREATEQUAL op     { TmOp($2.i,OpGreatEqual,$1,$3) }      
  | op EQUAL op          { TmOp($2.i,OpEqual,$1,$3) }      
  | op NOTEQUAL op       { TmOp($2.i,OpNotEqual,$1,$3) }
  | NOT op               { TmOp($1.i,OpBoolNot,$2,TmNop) }
  | op AND op            { TmOp($2.i,OpBoolAnd,$1,$3) }
  | op OR op             { TmOp($2.i,OpBoolOr,$1,$3) }
  | op CONCAT op         { TmOp($2.i,OpConcat,$1,$3) }

    
      
atom:
    /* Function application */  
  | FUNIDENT revtmseq RPAREN  
      { let fi = mkinfo $1.i $3.i in
        let rec mkapps lst =
          match lst with
          | t::ts -> TmApp(fi,mkapps ts,t)
          | [] -> TmVar($1.i,$1.v,noidx)
        in
        (match Ustring.to_utf8 $1.v with
         | "dprint"  -> TmOp($1.i,OpDprint,List.hd $2,TmNop)
         | "dbprint" -> TmOp($1.i,OpDBprint,List.hd $2,TmNop)
         | _ -> mkapps (if List.length $2 = 0 then [TmNop] else $2))}
  | LPAREN term RPAREN   { $2 }
  | LPAREN SUB op RPAREN { TmOp($2.i,OpMul,TmInt($2.i,-1),$3) }
  | LSQUARE revtmseq RSQUARE  
       { TmUC($1.i,UCLeaf(List.rev $2),UCOrdered,UCMultivalued) }
  | LCURLY scope RCURLY  { $2 }
  | IDENT                { TmVar($1.i,$1.v,noidx) }
  | CHAR                 { TmChar($1.i, List.hd (ustring2list $1.v)) }
  | STRING
      { let lst = List.map (fun x -> TmChar(NoInfo,x)) (ustring2list $1.v) in
        TmUC($1.i,UCLeaf(lst),UCOrdered,UCMultivalued) } 
  | UINT                 { TmInt($1.i,$1.v) }
  | TRUE                 { TmBool($1.i,true) }
  | FALSE                { TmBool($1.i,false) }
  
      
revtmseq:
    |   {[]}
    |   term
        {[$1]}               
    |   revtmseq COMMA term
        {$3::$1}

revidentseq:
    |   {[]}
    |   IDENT {[$1.v]}               
    |   revidentseq COMMA IDENT {$3.v::$1}
        
      
     









      

