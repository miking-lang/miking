
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

  let unique_ident = us"X"

%}

/* Misc tokens */
%token EOF

/* Use the non-terminals 'con_ident', 'var_ident', 'type_ident', and 'ident' instead of the below */
%token <Ustring.ustring Ast.tokendata> CON_IDENT
%token <Ustring.ustring Ast.tokendata> VAR_IDENT
%token <Ustring.ustring Ast.tokendata> TYPE_IDENT
%token <Ustring.ustring Ast.tokendata> LABEL_IDENT
%token <Ustring.ustring Ast.tokendata> UC_IDENT  /* An identifier that starts with an upper-case letter */
%token <Ustring.ustring Ast.tokendata> LC_IDENT  /* An identifier that starts with "_" or a lower-case letter */
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
%token <unit Ast.tokendata> NEVER
%token <unit Ast.tokendata> USING

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
%token <unit Ast.tokendata> AND           /* "&"   */
%token <unit Ast.tokendata> NOT           /* "!"   */
%token <unit Ast.tokendata> CONCAT        /* "++"  */

%start main
%start main_mexpr

%type <Ast.program> main
%type <Ast.program> main_mexpr

%%

main:
  | includes tops mexpr_opt EOF
    { Program ($1, $2, $3) }

main_mexpr:
  | mexpr EOF
    { Program ([], [], $1) }

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
    { tmUnit }

tops:
  | top tops
    { $1 :: $2 }
  |
    { [] }
  // TODO: These should matter with a type system
  | TYPE type_ident type_params tops
    { $4 }
  | TYPE type_ident type_params EQ ty tops
    { $6 }

type_params:
  | type_ident type_params
    { $1 :: $2 }
  |
    { [] }

top:
  | mlang
    { TopLang($1) }
  | toplet
    { TopLet($1) }
  | topRecLet
    { TopRecLet($1) }
  | topcon
    { TopCon($1) }
  | toputest
    { TopUtest($1) }

toplet:
  | LET var_ident ty_op EQ mexpr
    { let fi = mkinfo $1.i $4.i in
      Let (fi, $2.v, $5) }

topRecLet:
  | REC lets END
    { let fi = mkinfo $1.i $3.i in
      RecLet (fi, $2) }

topcon:
  | CON con_ident ty_op
    { let fi = mkinfo $1.i $2.i in
      Con (fi, $2.v, $3) }

toputest:
  | UTEST mexpr WITH mexpr
      { let fi = mkinfo $1.i (tm_info $4) in
        Utest (fi,$2,$4,None) }
  | UTEST mexpr WITH mexpr USING mexpr
      { let fi = mkinfo $1.i (tm_info $6) in
        Utest (fi,$2,$4,Some $6) }

mlang:
  | LANG ident lang_includes lang_body
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
  | ident ADD lang_list
    { $1 :: $3 }
  | ident
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
  | SYN type_ident EQ constrs
    { let fi = mkinfo $1.i $3.i in
      Data (fi, $2.v, $4) }
  | SEM var_ident params EQ cases
    { let fi = mkinfo $1.i $4.i in
      Inter (fi, $2.v, $3, $5) }

constrs:
  | constr constrs
    { $1 :: $2 }
  |
    { [] }
constr:
  | BAR con_ident constr_params
    { let fi = mkinfo $1.i $2.i in
      CDecl(fi, $2.v, $3) }

constr_params:
  | ty
    { $1 }
  |
    { TyUnit }

params:
  | LPAREN var_ident COLON ty RPAREN params
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
  | BAR pat ARROW mexpr
    { ($2, $4) }

/// Expression language ///////////////////////////////



mexpr:
  | left
      { $1 }
  | TYPE type_ident IN mexpr
      { $4 }
  | TYPE type_ident EQ ty IN mexpr
      { $6 }
  | REC lets IN mexpr
      { let fi = mkinfo $1.i $3.i in
        let lst = List.map (fun (fi,x,t) -> (fi,x,0,t)) $2 in
         TmRecLets(fi,lst,$4) }
  | LET var_ident ty_op EQ mexpr IN mexpr
      { let fi = mkinfo $1.i $6.i in
        TmLet(fi,$2.v,0,$5,$7) }
  | LAM var_ident ty_op DOT mexpr
      { let fi = mkinfo $1.i (tm_info $5) in
        TmLam(fi,$2.v,0,$3,$5) }
  | IF mexpr THEN mexpr ELSE mexpr
      { let fi = mkinfo $1.i (tm_info $6) in
        TmMatch(fi,$2,PatBool(NoInfo,true),$4,$6) }
  | CON con_ident ty_op IN mexpr
      { let fi = mkinfo $1.i $4.i in
        TmCondef(fi,$2.v,0,$3,$5)}
  | MATCH mexpr WITH pat THEN mexpr ELSE mexpr
      { let fi = mkinfo $1.i (tm_info $8) in
         TmMatch(fi,$2,$4,$6,$8) }
  | USE ident IN mexpr
      { let fi = mkinfo $1.i $3.i in
        TmUse(fi,$2.v,$4) }
  | UTEST mexpr WITH mexpr IN mexpr
      { let fi = mkinfo $1.i (tm_info $4) in
        TmUtest(fi,$2,$4,None,$6) }
  | UTEST mexpr WITH mexpr USING mexpr IN mexpr
      { let fi = mkinfo $1.i (tm_info $6) in
        TmUtest(fi,$2,$4,Some $6,$8) }

lets:
  | LET var_ident ty_op EQ mexpr
      { let fi = mkinfo $1.i (tm_info $5) in
        [(fi, $2.v, $5)] }
  | LET var_ident ty_op EQ mexpr lets
      { let fi = mkinfo $1.i (tm_info $5) in
        (fi, $2.v, $5)::$6 }


left:
  | atom
      { $1 }
  | left atom
      { let fi = mkinfo (tm_info $1) (tm_info $2) in
        TmApp(fi,$1,$2) }
  | con_ident atom
      { let fi = mkinfo $1.i (tm_info $2) in
        TmConapp(fi,$1.v,nosym,$2) }


atom:
  | atom DOT proj_label
      { let fi = mkinfo (tm_info $1) (fst $3) in
        let id = unique_ident in
        TmMatch(fi,$1,PatRecord(fi,Record.singleton (snd $3) (PatNamed(fi,NameStr(id,nosym)))),
                                TmVar(fi,id,nosym), TmNever(fi)) }
  | LPAREN seq RPAREN
      { if List.length $2 = 1 then List.hd $2
        else tuple2record (mkinfo $1.i $3.i) $2 }
  | LPAREN mexpr COMMA RPAREN
      { TmRecord(mkinfo $1.i $4.i, Record.singleton (us "0") $2) }
  | LPAREN RPAREN        { TmRecord($1.i, Record.empty) }
  | var_ident                { TmVar($1.i,$1.v,nosym) }
  | CHAR                 { TmConst($1.i, CChar(List.hd (ustring2list $1.v))) }
  | UINT                 { TmConst($1.i,CInt($1.v)) }
  | UFLOAT               { TmConst($1.i,CFloat($1.v)) }
  | TRUE                 { TmConst($1.i,CBool(true)) }
  | FALSE                { TmConst($1.i,CBool(false)) }
  | NEVER                { TmNever($1.i) }
  | STRING               { TmSeq($1.i, Mseq.map (fun x -> TmConst($1.i,CChar(x)))
                                                  (Mseq.of_ustring $1.v)) }
  | LSQUARE seq RSQUARE  { TmSeq(mkinfo $1.i $3.i, Mseq.of_list $2) }
  | LSQUARE RSQUARE      { TmSeq(mkinfo $1.i $2.i, Mseq.empty) }
  | LBRACKET labels RBRACKET
      { TmRecord(mkinfo $1.i $3.i, $2 |> List.fold_left
        (fun acc (k,v) -> Record.add k v acc) Record.empty) }
  | LBRACKET RBRACKET    { TmRecord(mkinfo $1.i $2.i, Record.empty)}
  | LBRACKET mexpr WITH var_ident EQ mexpr RBRACKET
      { TmRecordUpdate(mkinfo $1.i $7.i, $2, $4.v, $6) }

proj_label:
  | UINT
    { ($1.i, ustring_of_int $1.v) }
  | label_ident
    { ($1.i,$1.v) }



seq:
  | mexpr
      { [$1] }
  | mexpr COMMA seq
      { $1::$3 }

labels:
  | label_ident EQ mexpr
    {[($1.v, $3)]}
  | label_ident EQ mexpr COMMA labels
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

pat_labels:
  | label_ident EQ pat
    {[($1.v, $3)]}
  | label_ident EQ pat COMMA pat_labels
    {($1.v, $3)::$5}


name:
  | var_ident
      { if $1.v =. us"_"
        then ($1.i, NameWildcard)
        else ($1.i, NameStr($1.v,0)) }

pat:
  | pat_conj BAR pat
      { PatOr(mkinfo (pat_info $1) (pat_info $3), $1, $3) }
  | pat_conj
      { $1 }
pat_conj:
  | pat_atom AND pat_conj
      { PatAnd(mkinfo (pat_info $1) (pat_info $3), $1, $3)}
  | pat_atom
      { $1 }
pat_atom:
  | name
      { PatNamed(fst $1, snd $1) }
  | NOT pat_atom
      { PatNot(mkinfo $1.i (pat_info $2), $2) }
  | con_ident pat_atom
      { PatCon(mkinfo $1.i (pat_info $2), $1.v, nosym, $2) }
  | patseq
      { PatSeqTot($1 |> fst, $1 |> snd |> Mseq.of_list) }
  | patseq CONCAT name CONCAT patseq
      { let fi = mkinfo (fst $1) (fst $5) in
        let l = $1 |> snd |> Mseq.of_list in
        let r = $5 |> snd |> Mseq.of_list in
        PatSeqEdg(fi, l, snd $3, r) }
  | patseq CONCAT name
      { PatSeqEdg(mkinfo (fst $1) (fst $3), $1 |> snd |> Mseq.of_list, snd $3, Mseq.empty) }
  | name CONCAT patseq
      { PatSeqEdg(mkinfo (fst $1) (fst $3), Mseq.empty, snd $1, $3 |> snd |> Mseq.of_list) }
  | LPAREN pat RPAREN
      { $2 }
  | LPAREN pat COMMA pat_list RPAREN
      { let fi = mkinfo $1.i $5.i in
        let r = List.fold_left (fun (i,a) x ->
          (i+1,Record.add (ustring_of_int i) x a)) (0,Record.empty) ($2::$4) in
                               PatRecord(fi,snd r) }
  | LBRACKET RBRACKET
      { PatRecord(mkinfo $1.i $2.i, Record.empty) }
  | LBRACKET pat_labels RBRACKET
      { PatRecord(mkinfo $1.i $3.i, $2 |> List.fold_left
                  (fun acc (k,v) -> Record.add k v acc) Record.empty) }
  | UINT /* TODO: enable matching against negative ints */
      { PatInt($1.i, $1.v) }
  | CHAR
      { PatChar($1.i, List.hd (ustring2list $1.v)) }
  | TRUE
      { PatBool($1.i, true) }
  | FALSE
      { PatBool($1.i, false) }
  | LPAREN RPAREN
      { PatRecord(mkinfo $1.i $2.i, Record.empty) }

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
  | ty_left
      { $1 }
  | ty_left ARROW ty
      { TyArrow($1,$3) }

ty_left:
  | ty_atom
    { $1 }
  | ty_left ty_atom
    { TyApp($1,$2) }

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
  | type_ident
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
  | label_ident COLON ty
    {[($1.v, $3)]}
  | label_ident COLON ty COMMA label_tys
    {($1.v, $3)::$5}


/// Identifiers ///////////////////////////////

ident:
  | UC_IDENT {$1}
  | LC_IDENT {$1}

var_ident:
  | LC_IDENT {$1}
  | VAR_IDENT {$1}

con_ident:
  | UC_IDENT {$1}
  | CON_IDENT {$1}

type_ident:
  | ident {$1}
  | TYPE_IDENT {$1}

label_ident:
  | ident {$1}
  | LABEL_IDENT {$1}
