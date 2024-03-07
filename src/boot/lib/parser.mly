
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
  open Intrinsics

  (** Create a new info, taking left and right part *)
  let mkinfo fi1 fi2 =
    match (fi1,fi2) with
      | (Info(fn,r1,c1,_,_), Info(_,_,_,r2,c2)) -> Info(fn,r1,c1,r2,c2)
      | (Info(fn,r1,c1,r2,c2), NoInfo) -> Info(fn,r1,c1,r2,c2)
      | (NoInfo, Info(fn,r1,c1,r2,c2)) -> Info(fn,r1,c1,r2,c2)
      | (_,_) -> NoInfo

  let unique_ident = us"X"

  let set_con_params params = function
    | CDecl (fi, _, name, ty) -> CDecl (fi, params, name, ty)

  let ty_from_either = function
    | Either.Right ty -> ty
    | Either.Left (fi, _) ->
       raise_error fi "This looks like a constructor type restriction, but appears in an invalid location"

%}

/* Misc tokens */
%token EOF

/* Use the non-terminals 'con_ident', 'var_ident', 'frozen_ident', 'type_ident', and 'ident' instead of the below */
%token <Ustring.ustring Ast.tokendata> CON_IDENT
%token <Ustring.ustring Ast.tokendata> VAR_IDENT
%token <Ustring.ustring Ast.tokendata> FROZEN_IDENT
%token <Ustring.ustring Ast.tokendata> TYPE_IDENT
%token <Ustring.ustring Ast.tokendata> LABEL_IDENT
%token <Ustring.ustring Ast.tokendata> UC_IDENT  /* An identifier that starts with an upper-case letter */
%token <Ustring.ustring Ast.tokendata> LC_IDENT  /* An identifier that starts with "_" or a lower-case letter */
%token <Ustring.ustring Ast.tokendata> STRING
%token <Ustring.ustring Ast.tokendata> CHAR
%token <int Ast.tokendata> INT
%token <float Ast.tokendata> FLOAT


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
%token <unit Ast.tokendata> EXTERNAL
%token <unit Ast.tokendata> SWITCH
%token <unit Ast.tokendata> CASE
%token <unit Ast.tokendata> ALL
%token <unit Ast.tokendata> DIVE
%token <unit Ast.tokendata> PRERUN


/* Types */
%token <unit Ast.tokendata> TUNKNOWN
%token <unit Ast.tokendata> TBOOL
%token <unit Ast.tokendata> TINT
%token <unit Ast.tokendata> TFLOAT
%token <unit Ast.tokendata> TCHAR
%token <unit Ast.tokendata> TSTRING
%token <unit Ast.tokendata> TTENSOR

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
%token <unit Ast.tokendata> DCOLON        /* "::"  */
%token <unit Ast.tokendata> COMMA         /* ","   */
%token <unit Ast.tokendata> SEMI          /* ";"   */
%token <unit Ast.tokendata> DOT           /* "."   */
%token <unit Ast.tokendata> BAR           /* "|"   */
%token <unit Ast.tokendata> AND           /* "&"   */
%token <unit Ast.tokendata> NOT           /* "!"   */
%token <unit Ast.tokendata> UNDERSCORE    /* "_"   */
%token <unit Ast.tokendata> CONCAT        /* "++"  */
%token <unit Ast.tokendata> GREATER       /* ">"   */
%token <unit Ast.tokendata> LESS          /* "<"   */

%start main
%start main_mexpr
%start main_mexpr_tm

%type <Ast.program> main
%type <Ast.program> main_mexpr
%type <Ast.tm> main_mexpr_tm

%%

main:
  | includes tops mexpr_opt EOF
    { Program ($1, $2, $3) }

main_mexpr:
  | mexpr EOF
    { Program ([], [], $1) }

main_mexpr_tm:
  | mexpr EOF
    { $1 }

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
    { tm_unit }

tops:
  | top tops
    { $1 :: $2 }
  |
    { [] }

type_params:
  | var_ident type_params
    { $1.v :: $2 }
  |
    { [] }

top:
  | mlang
    { TopLang($1) }
  | toplet
    { TopLet($1) }
  | toptype
    { TopType($1) }
  | topRecLet
    { TopRecLet($1) }
  | topcon
    { TopCon($1) }
  | toputest
    { TopUtest($1) }
  | topext
    { TopExt($1) }

toplet:
  | LET var_ident ty_op EQ mexpr
    { let fi = mkinfo $1.i $4.i in
      Let (fi, $2.v, $3 $1.i, $5) }

toptype:
  | TYPE type_ident type_params
     { let fi = mkinfo $1.i $2.i in
       Type (fi, $2.v, $3, TyVariant (fi, [])) }
  | TYPE type_ident type_params EQ ty
     { let fi = mkinfo $1.i (ty_info $5) in
       Type (fi, $2.v, $3, $5) }

topRecLet:
  | REC lets END
    { let fi = mkinfo $1.i $3.i in
      RecLet (fi, $2) }

topcon:
  | CON con_ident ty_op
    { let fi = mkinfo $1.i $2.i in
      Con (fi, $2.v, $3 $1.i) }

toputest:
  | UTEST mexpr WITH mexpr
      { let fi = mkinfo $1.i (tm_info $4) in
        Utest (fi,$2,$4,None,None) }
  | UTEST mexpr WITH mexpr USING mexpr
      { let fi = mkinfo $1.i (tm_info $6) in
        Utest (fi,$2,$4,Some $6,None) }
  | UTEST mexpr WITH mexpr ELSE mexpr
      { let fi = mkinfo $1.i (tm_info $6) in
        Utest (fi,$2,$4,None,Some $6) }
  | UTEST mexpr WITH mexpr USING mexpr ELSE mexpr
      { let fi = mkinfo $1.i (tm_info $8) in
        Utest (fi,$2,$4,Some $6,Some $8) }

mlang:
  | LANG ident lang_includes decls END
    { let incs, withs = $3 in
      let fi = if List.length incs > 0 then
                 mkinfo $1.i (List.nth incs (List.length incs - 1)).i
               else
                 mkinfo $1.i $2.i
      in
      Lang (fi, $2.v, List.map (fun l -> l.v) incs, withs, $4) }

topext:
  | EXTERNAL ident COLON ty
    { let fi = mkinfo $1.i (ty_info $4) in
      Ext (fi, $2.v, false, $4) }
  | EXTERNAL ident NOT COLON ty
    { let fi = mkinfo $1.i (ty_info $5) in
      Ext (fi, $2.v, true, $5) }

lang_includes:
  | EQ lang_list with_list
    { $2, List.rev $3 }
  |
    { [], [] }
lang_list:
  | ident ADD lang_list
    { $1 :: $3 }
  | ident
    { [$1] }
with_list:
  |
    { [] }
  | with_list WITH type_ident EQ with_type_list
    { let fi = mkinfo $2.i $4.i in
      With (fi, WithType, $3.v, List.rev $5) :: $1 }
  | with_list WITH var_ident EQ with_var_list
    { let fi = mkinfo $2.i $4.i in
      With (fi, WithValue, $3.v, List.rev $5) :: $1 }
with_type_list:
  | with_type_list ADD ident DOT type_ident
    { ($3.v, $5.v) :: $1 }
  | ident DOT type_ident
    { [($1.v, $3.v)] }
with_var_list:
  | with_var_list ADD ident DOT var_ident
    { ($3.v, $5.v) :: $1 }
  | ident DOT var_ident
    { [($1.v, $3.v)] }

decls:
  | decl decls
    { $1 :: $2 }
  |
    { [] }
decl:
  | SYN type_ident type_params EQ constrs
    { let fi = mkinfo $1.i $4.i in
      Data (fi, $2.v, List.length $3, List.map (set_con_params $3) $5) }
  | SEM var_ident params EQ cases
    { let fi = mkinfo $1.i $4.i in
      Inter (fi, $2.v, TyUnknown fi, Some $3, $5) }
  | SEM var_ident COLON ty
    { let fi = mkinfo $1.i (ty_info $4) in
      Inter (fi, $2.v, $4, None, []) }
  | TYPE type_ident type_params EQ ty
    { let fi = mkinfo $1.i $4.i in
      Alias (fi, $2.v, $3, $5) }

constrs:
  | constr constrs
    { $1 :: $2 }
  |
    { [] }
constr:
  | BAR con_ident constr_params
    { let fi = mkinfo $1.i $2.i in
      CDecl(fi, [], $2.v, $3 $1.i) }

constr_params:
  | ty
    { fun _ -> $1 }
  |
    { fun i -> ty_unit i }

params:
  | LPAREN var_ident COLON ty RPAREN params
    { let fi = mkinfo $1.i $5.i in
      Param (fi, $2.v, $4) :: $6 }
  | var_ident params
    { let fi = mkinfo $1.i $1.i in
      Param (fi, $1.v, TyUnknown fi) :: $2 }
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
  | sequence
      { $1 }
  | TYPE type_ident type_params IN mexpr
      { let fi = mkinfo $1.i $4.i in
        TmType(fi, $2.v, $3, TyVariant (fi, []), $5) }
  | TYPE type_ident type_params EQ ty IN mexpr
      { let fi = mkinfo $1.i (tm_info $7) in
        TmType(fi, $2.v, $3, $5, $7) }
  | REC lets IN mexpr
      { let fi = mkinfo $1.i $3.i in
        let lst = List.map (fun (fi,x,ty,t) -> (fi,x,Symb.Helpers.nosym,ty,t)) $2 in
         TmRecLets(fi,lst,$4) }
  | LET var_ident ty_op EQ mexpr IN mexpr
      { let fi = mkinfo $1.i $6.i in
        TmLet(fi,$2.v,Symb.Helpers.nosym,$3 $1.i,$5,$7) }
  | LAM var_ident ty_op DOT mexpr
      { let fi = mkinfo $1.i (tm_info $5) in
        TmLam(fi,$2.v,Symb.Helpers.nosym,false,$3 $1.i,$5) }
  | LAM DOT mexpr
      { let fi = mkinfo $1.i (tm_info $3) in
        TmLam(fi,us"",Symb.Helpers.nosym,false,TyUnknown(fi),$3) }
  | IF mexpr THEN mexpr ELSE mexpr
      { let fi = mkinfo $1.i (tm_info $6) in
        TmMatch(fi,$2,PatBool(fi,true),$4,$6) }
  | CON con_ident ty_op IN mexpr
      { let fi = mkinfo $1.i $4.i in
        TmConDef(fi,$2.v,Symb.Helpers.nosym,$3 $1.i,$5)}
  | MATCH mexpr WITH pat THEN mexpr ELSE mexpr
      { let fi = mkinfo $1.i (tm_info $8) in
        TmMatch(fi,$2,$4,$6,$8) }
  | MATCH mexpr WITH pat IN mexpr
      { let fi = mkinfo $1.i (tm_info $6) in
        TmMatch(fi,$2,$4,$6,TmNever(fi)) }
  | SWITCH mexpr swcases
      {
        let fi = mkinfo $1.i (tm_info $3) in
        TmLet(fi,unique_ident,Symb.Helpers.nosym,TyUnknown(fi),$2,$3)
      }
  | DIVE mexpr
    { let fi = mkinfo $1.i (tm_info $2) in
      TmDive(fi, 0, $2) }
  | PRERUN mexpr
    { let fi = mkinfo $1.i (tm_info $2) in
      TmPreRun(fi, 0, $2) }
  | USE ident IN mexpr
      { let fi = mkinfo $1.i $3.i in
        TmUse(fi,$2.v,$4) }
  | UTEST mexpr WITH mexpr IN mexpr
      { let fi = mkinfo $1.i $5.i in
        TmUtest(fi,$2,$4,None,None,$6) }
  | UTEST mexpr WITH mexpr USING mexpr IN mexpr
      { let fi = mkinfo $1.i (tm_info $6) in
        TmUtest(fi,$2,$4,Some $6,None,$8) }
  | UTEST mexpr WITH mexpr USING mexpr ELSE mexpr IN mexpr
      { let fi = mkinfo $1.i (tm_info $8) in
        TmUtest(fi,$2,$4,Some $6,Some $8,$10) }
  | EXTERNAL ident COLON ty IN mexpr
      { let fi = mkinfo $1.i (tm_info $6) in
        TmExt(fi,$2.v,Symb.Helpers.nosym,false,$4,$6) }
  | EXTERNAL ident NOT COLON ty IN mexpr
      { let fi = mkinfo $1.i (tm_info $7) in
        TmExt(fi,$2.v,Symb.Helpers.nosym,true,$5,$7) }

lets:
  | LET var_ident ty_op EQ mexpr
      { let fi = mkinfo $1.i (tm_info $5) in
        [(fi, $2.v, $3 $1.i, $5)] }
  | LET var_ident ty_op EQ mexpr lets
      { let fi = mkinfo $1.i (tm_info $5) in
        (fi, $2.v, $3 $1.i, $5)::$6 }

sequence:
  | left
     { $1 }
  | left SEMI mexpr
     { let fi = tm_info $1 in
       TmLet(fi, us"", Symb.Helpers.nosym, TyUnknown(fi), $1, $3) }

left:
  | atom
      { $1 }
  | left atom
      { let fi = mkinfo (tm_info $1) (tm_info $2) in
        TmApp(fi,$1,$2) }
  | con_ident atom
      { let fi = mkinfo $1.i (tm_info $2) in
        TmConApp(fi,$1.v,Symb.Helpers.nosym,$2) }

swcases:
  | CASE pat THEN mexpr swcases
      { let fi = mkinfo $1.i (tm_info $5) in
        let id = TmVar(fi, unique_ident, Symb.Helpers.nosym, false, false) in
        TmMatch(fi,id,$2,$4,$5) }
  | END
      { TmNever($1.i) }

atom:
  | atom DOT proj_label
      { let fi = mkinfo (tm_info $1) (fst $3) in
        let id = unique_ident in
        TmMatch(fi,$1,PatRecord(fi,Record.singleton (snd $3) (PatNamed(fi,NameStr(id,Symb.Helpers.nosym)))),
                                TmVar(fi,id,Symb.Helpers.nosym,false,false), TmNever(fi)) }
  | LPAREN seq RPAREN
      { if List.length $2 = 1 then List.hd $2
        else tuple2record (mkinfo $1.i $3.i) $2 }
  | LPAREN mexpr COMMA RPAREN
      { TmRecord(mkinfo $1.i $4.i, Record.singleton (us "0") $2) }
  | LPAREN RPAREN        { TmRecord($1.i, Record.empty) }
  | var_ident            { TmVar($1.i,$1.v,Symb.Helpers.nosym, false, false) }
  | frozen_ident         { TmVar($1.i,$1.v,Symb.Helpers.nosym, false, true) }
  | CHAR                 { TmConst($1.i, CChar(List.hd (ustring2list $1.v))) }
  | INT                  { TmConst($1.i,CInt($1.v)) }
  | FLOAT                { TmConst($1.i,CFloat($1.v)) }
  | TRUE                 { TmConst($1.i,CBool(true)) }
  | FALSE                { TmConst($1.i,CBool(false)) }
  | NEVER                { TmNever($1.i) }
  | STRING               { TmSeq($1.i, Mseq.map (fun x -> TmConst($1.i,CChar(x)))
                                                  (Mseq.Helpers.of_ustring $1.v)) }
  | LSQUARE seq RSQUARE  { TmSeq(mkinfo $1.i $3.i, Mseq.Helpers.of_list $2) }
  | LSQUARE RSQUARE      { TmSeq(mkinfo $1.i $2.i, Mseq.empty) }
  | LBRACKET labels RBRACKET
      { TmRecord(mkinfo $1.i $3.i, $2 |> List.fold_left
        (fun acc (k,v) -> Record.add k v acc) Record.empty) }
  | LBRACKET RBRACKET    { TmRecord(mkinfo $1.i $2.i, Record.empty)}
  | LBRACKET mexpr WITH labels RBRACKET
      { List.fold_left (fun acc (k,v) ->
          TmRecordUpdate (mkinfo $1.i $5.i, acc, k, v)
        ) $2 $4}

proj_label:
  | INT
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
    { ($1.i, NameStr($1.v,Symb.Helpers.nosym)) }
  | UNDERSCORE
    { ($1.i, NameWildcard) }

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
      { PatCon(mkinfo $1.i (pat_info $2), $1.v, Symb.Helpers.nosym, $2) }
  | patseq
      { PatSeqTot($1 |> fst, $1 |> snd |> Mseq.Helpers.of_list) }
  | patseq CONCAT name CONCAT patseq
      { let fi = mkinfo (fst $1) (fst $5) in
        let l = $1 |> snd |> Mseq.Helpers.of_list in
        let r = $5 |> snd |> Mseq.Helpers.of_list in
        PatSeqEdge(fi, l, snd $3, r) }
  | patseq CONCAT name
      { PatSeqEdge(mkinfo (fst $1) (fst $3), $1 |> snd |> Mseq.Helpers.of_list, snd $3, Mseq.empty) }
  | name CONCAT patseq
      { PatSeqEdge(mkinfo (fst $1) (fst $3), Mseq.empty, snd $1, $3 |> snd |> Mseq.Helpers.of_list) }
  | LPAREN pat RPAREN
      { $2 }
  | LPAREN pat COMMA RPAREN
      { let fi = mkinfo $1.i $4.i in
        PatRecord(fi,Record.singleton (us"0") $2) }
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
  | INT
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
      { fun _ -> $2 }
  |
      { fun i -> TyUnknown i }


ty:
  | ty_left
      { $1 }
  | ty_left ARROW ty
      { let fi = mkinfo (ty_info $1) (ty_info $3) in
        TyArrow(fi,$1,$3) }
  | ALL var_ident DOT ty
      { let fi = mkinfo $1.i (ty_info $4) in
        TyAll(fi, $2.v, None, $4) }
  | ALL var_ident DCOLON data_kind DOT ty
      { let fi = mkinfo $1.i (ty_info $6) in
        TyAll(fi, $2.v, Some $4, $6) }
  | USE ident IN ty
      { let fi = mkinfo $1.i $3.i in
        TyUse(fi, $2.v, $4) }

ty_left:
  | ty_ish_atom
    { ty_from_either $1 }
  | f=ty_left a=ty_ish_atom
    { match a with
      | Either.Right ty -> TyApp(mkinfo (ty_info f) (ty_info ty), f, ty)
      | Either.Left (fi, data) ->
         match f with
         | TyCon (lfi, name, None) -> TyCon (mkinfo lfi fi, name, Some data)
         | _ -> raise_error fi "This looks like a constructor type restriction, but appears in an invalid location" }

ty_ish_atom:
  | ty_atom
    { Either.Right $1 }
  | ty_data
    { Either.Left $1 }

%inline ty_atom:
  | LPAREN RPAREN
    { ty_unit (mkinfo $1.i $2.i) }
  | LPAREN ty RPAREN
    { $2 }
  | LSQUARE ty RSQUARE
    { TySeq(mkinfo $1.i $3.i, $2) }
  | LPAREN ty COMMA ty_list RPAREN
    { tuplety2recordty (mkinfo $1.i $5.i) ($2::$4) }
  | LPAREN ty COMMA RPAREN
    { TyRecord(mkinfo $1.i $4.i, Record.singleton (us "0") $2) }
  | LBRACKET RBRACKET
    { ty_unit (mkinfo $1.i $2.i) }
  | LBRACKET label_tys RBRACKET
    { let r = $2 |> List.fold_left
                      (fun acc (k,v) -> Record.add k v acc)
                      Record.empty
      in
      TyRecord(mkinfo $1.i $3.i, r) }
  | TTENSOR LSQUARE ty RSQUARE
    { TyTensor(mkinfo $1.i $4.i, $3) }
  | TUNKNOWN
    { TyUnknown $1.i }
  | TBOOL
    { TyBool $1.i }
  | TINT
    { TyInt $1.i }
  | TFLOAT
    { TyFloat $1.i }
  | TCHAR
    { TyChar $1.i }
  | TSTRING
    { TySeq($1.i,TyChar $1.i) }
  | type_ident
    { TyCon($1.i,$1.v,None) }
  | var_ident
    { TyVar($1.i,$1.v) }
  | UNDERSCORE
    { TyVar($1.i, us"_") }

%inline ty_data:
  | LBRACKET var_ident RBRACKET
    { (mkinfo $1.i $3.i, DVar $2.v) }
  | LBRACKET con_ident con_list RBRACKET
    { (mkinfo $1.i $4.i, DCons ($2.v :: $3)) }
  | LBRACKET NOT con_list RBRACKET
    { (mkinfo $1.i $4.i, DNCons $3) }

ty_list:
  | ty COMMA ty_list
    { $1 :: $3 }
  | ty
    { [$1] }

data_kind:
  | LBRACKET separated_list(COMMA, type_with_cons) RBRACKET
    { $2 }

type_with_cons:
  | type_ident LSQUARE GREATER con_list RSQUARE
    { ($1.v, $4, None) }
  | type_ident LSQUARE BAR con_list RSQUARE
    { ($1.v, $4, Some []) }
  | type_ident LSQUARE LESS con_list RSQUARE
    { ($1.v, [], Some $4) }
  | type_ident LSQUARE LESS con_list BAR con_list RSQUARE
    { ($1.v, $6, Some $4) }

con_list:
  | con_ident con_list
    { $1.v :: $2 }
  |
    { [] }

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

frozen_ident:
  | FROZEN_IDENT {$1}

con_ident:
  | UC_IDENT {$1}
  | CON_IDENT {$1}

type_ident:
  | UC_IDENT {$1}
  | TYPE_IDENT {$1}

label_ident:
  | ident {$1}
  | LABEL_IDENT {$1}
