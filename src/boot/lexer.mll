
(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   lexer.mll includes the lexer that generates tokens. The token
   definitions are located in file parser.mly
*)

{
  open Ustring.Op
  open Ast
  open Msg
  exception Lex_error of Msg.message

(* TODO: Remove unused keywords *)
let reserved_strings = [
  (* Keywords *)
  ("if",            fun(i) -> Parser.IF{i=i;v=()});
  ("then",          fun(i) -> Parser.THEN{i=i;v=()});
  ("else",          fun(i) -> Parser.ELSE{i=i;v=()});
  ("true",          fun(i) -> Parser.TRUE{i=i;v=()});
  ("false",         fun(i) -> Parser.FALSE{i=i;v=()});
  ("match",         fun(i) -> Parser.MATCH{i=i;v=()});
  ("with",          fun(i) -> Parser.WITH{i=i;v=()});
  ("utest",         fun(i) -> Parser.UTEST{i=i;v=()});
  ("type",          fun(i) -> Parser.TYPE{i=i;v=()});
  ("con",           fun(i) -> Parser.CON{i=i;v=()});
  ("lang",          fun(i) -> Parser.LANG{i=i;v=()});
  ("let",           fun(i) -> Parser.LET{i=i;v=()});
  ("recursive",     fun(i) -> Parser.REC{i=i;v=()});
  ("lam",           fun(i) -> Parser.LAM{i=i;v=()});
  ("in",            fun(i) -> Parser.IN{i=i;v=()});
  ("end",           fun(i) -> Parser.END{i=i;v=()});
  ("syn",           fun(i) -> Parser.SYN{i=i;v=()});
  ("sem",           fun(i) -> Parser.SEM{i=i;v=()});
  ("use",           fun(i) -> Parser.USE{i=i;v=()});
  ("mexpr",         fun(i) -> Parser.MEXPR{i=i;v=()});
  ("include",       fun(i) -> Parser.INCLUDE{i=i;v=()});


  (* v *)
  ("=",             fun(i) -> Parser.EQ{i=i;v=()});
  ("+",             fun(i) -> Parser.ADD{i=i;v=()});
  ("++",            fun(i) -> Parser.CONCAT{i=i;v=()});

  (* Symbolic Tokens *)
  ("(",             fun(i) -> Parser.LPAREN{i=i;v=()});
  (")",             fun(i) -> Parser.RPAREN{i=i;v=()});
  ("[",             fun(i) -> Parser.LSQUARE{i=i;v=()});
  ("]",             fun(i) -> Parser.RSQUARE{i=i;v=()});
  ("{",             fun(i) -> Parser.LBRACKET{i=i;v=()});
  ("}",             fun(i) -> Parser.RBRACKET{i=i;v=()});
  (":",             fun(i) -> Parser.COLON{i=i;v=()});
  (",",             fun(i) -> Parser.COMMA{i=i;v=()});
  (".",             fun(i) -> Parser.DOT{i=i;v=()});
  ("|",             fun(i) -> Parser.BAR{i=i;v=()});
  ("->",            fun(i) -> Parser.ARROW{i=i;v=()});

]

(* Info handling *)
let tabsize = ref 8
let filename = ref (us"")
let rowno = ref 1
let colno = ref 0
let last_info = ref NoInfo
let utf8strlen s = Ustring.length (Ustring.from_utf8 s)
let newrow() =
  incr rowno;
  colno := 0
(* Updates both columns and rows in a safe way *)
let count_ustring s =
  rowno := !rowno + (Ustring.count s (uc '\n'));
  colno := try Ustring.length s - Ustring.rindex s (uc '\n') - 1
	     with Not_found -> !colno + Ustring.length s
let count_utf8 s = count_ustring (Ustring.from_utf8 s)
let colcount_fast s = colno := !colno + (String.length s)
let colcount_utf8 s = colno := !colno + (utf8strlen s)
let add_colno i = colno := !colno + i
let mkinfo_fast s =
  last_info := Info(!filename,!rowno,!colno,!rowno,!colno+(String.length s));
  colcount_fast s; !last_info
let mkinfo_utf8_fast s =
  last_info := Info(!filename,!rowno,!colno,!rowno,!colno + (utf8strlen s));
  colcount_utf8 s; !last_info
(* mkinfo_ustring also counts newlines correctly in string [s] *)
let mkinfo_ustring s =
  let row = !rowno in
  let col = !colno in
  count_ustring s;
  last_info := Info(!filename,row,col,!rowno,!colno);
  !last_info

(* Init the lexer with file name and tab-size. *)
let init file_name tab_size=
  filename := file_name;
  rowno := 1;
  colno := 0;
  tabsize := tab_size

(* Handle identifiers, keywords, and operators *)
type buildfun = info -> Parser.token
let (str_tab : (string,buildfun) Hashtbl.t) =
  Hashtbl.create 1024
let _ = List.iter (fun (str,f) -> Hashtbl.add str_tab str f)
  reserved_strings

(* Make identfier, keyword, or operator  *)
let mkid s =
  try
    let f = Hashtbl.find str_tab s in f (mkinfo_fast s)
  with Not_found ->
    let s2 = Ustring.from_utf8 s in
    Parser.IDENT {i=mkinfo_ustring s2; v=s2}

(* String handling *)
let string_buf = Buffer.create 80

(* Parse error message *)
let parse_error_message() =
  (PARSE_ERROR,ERROR,!last_info,[])


}

let utf8_1byte = ['\x00'-'\x7F']
let utf8_2byte = ['\xC0'-'\xDF'] ['\x80'-'\xBF']
let utf8_3byte = ['\xE0'-'\xEF'] ['\x80'-'\xBF'] ['\x80'-'\xBF']
let utf8_4byte = ['\xF0'-'\xF7'] ['\x80'-'\xBF'] ['\x80'-'\xBF'] ['\x80'-'\xBF']

let ascii = utf8_1byte
let noascii =  utf8_2byte | utf8_3byte | utf8_4byte
let utf8 = ascii | noascii
let lcase_letter = ['a'-'z']
let ucase_letter = ['A'-'Z']
let us_letter = lcase_letter | ucase_letter
let newline = ('\013' | '\010' | "\013\010")
let whitespace = (' '| '\012')
let tab = '\t'
let digit = ['0'-'9']
let s_escape = "\\'" | "\\\"" | "\\?"  | "\\\\" |
               "\\a"  | "\\b" | "\\f"  | "\\n" | "\\r" | "\\t" | "\\v"
let ident = ('_'| lcase_letter) (digit | '_' | us_letter)*
let uident = ucase_letter (digit | '_' | us_letter)*

let symtok =  "="  | "+" |  "-" | "*"  | "/" | "%"  | "<"  | "<=" | ">" | ">=" | "<<" | ">>" | ">>>" | "==" |
              "!=" | "!" | "&&" | "||" | "++"| "$"  | "("  | ")"  | "["  | "]" | "{"  | "}"  |
              "::" | ":" | ","  | "."  | "|" | "->" | "=>" | "++"


let line_comment = "//" [^ '\013' '\010']*
let line_comment_alt = "--" [^ '\013' '\010']*
let unsigned_integer = digit+
let signed_integer = unsigned_integer  | '-' unsigned_integer
let unsigned_number = unsigned_integer ('.' (unsigned_integer)?)?
                      (('e'|'E') ("+"|"-")? unsigned_integer)?


(* Main lexing *)
rule main = parse
  | whitespace+ as s
      { colcount_fast s; main lexbuf }
  | line_comment
      { main lexbuf }
  | line_comment_alt
      { main lexbuf }
  | "/*" as s
      { Buffer.reset string_buf ;
	Buffer.add_string string_buf s; section_comment lexbuf;
	count_utf8 (Buffer.contents string_buf);
	main lexbuf}
  | tab
      { add_colno !tabsize; main lexbuf }
  | newline
      { newrow(); main lexbuf }
  | (unsigned_integer as str)
      { Parser.UINT{i=mkinfo_fast str; v=int_of_string str} }
  | unsigned_number as str
      { Parser.UFLOAT{i=mkinfo_fast str; v=float_of_string str} }
  | ident | symtok as s
      { mkid s }
  | uident as s
      { Parser.IDENT{i=mkinfo_fast s; v=Ustring.from_utf8 s} }  (* UIDENT *)
  | '\'' (utf8 as c) '\''
      { let s = Ustring.from_utf8 c in
        Parser.CHAR{i=mkinfo_ustring (us"'" ^. s ^. us"'"); v=s}}
  | '#' (("con" | "type" | "var") as ident) '"'
       { Buffer.reset string_buf ;  parsestring lexbuf;
	 let s = Ustring.from_utf8 (Buffer.contents string_buf) in
         let esc_s = Ustring.convert_escaped_chars s in
         let fi = mkinfo_ustring (s ^. us"  #" ^. us(ident)) in
	 let rval = (match ident with
            | "var" -> Parser.IDENT{i=fi; v=esc_s}
            | _ -> Parser.IDENT{i=fi; v=esc_s})  (* UIDENT *)
         in
	 add_colno 3; colcount_fast ident; rval}
  | '"'
      { Buffer.reset string_buf ;  parsestring lexbuf;
	 let s = Ustring.from_utf8 (Buffer.contents string_buf) in
         let esc_s = Ustring.convert_escaped_chars s in
	 let rval = Parser.STRING{i=mkinfo_ustring (s ^. us"  "); v=esc_s} in
	 add_colno 2; rval}
  | eof
      { Parser.EOF }
  | utf8 as c
      { let s = Ustring.from_utf8 c in
	raise (Lex_error (LEX_UNKNOWN_CHAR,ERROR,mkinfo_utf8_fast c,[s])) }

and parsestring = parse
  | '"'
      { }
  | eof
      { let s = Ustring.from_utf8 ("\"" ^ (Buffer.contents string_buf)) in
	raise (Lex_error (LEX_STRING_NOT_TERMINATED,ERROR,
		 mkinfo_ustring s, [s])) }
  | s_escape as s
      { Buffer.add_string string_buf s; parsestring lexbuf }
  | '\\' utf8 as s
      { count_ustring  (Ustring.from_utf8 ("\""^(Buffer.contents string_buf)));
        let s2 = Ustring.from_utf8 s in
	raise (Lex_error (LEX_INVALID_ESCAPE,ERROR,
		 mkinfo_ustring s2, [s2])) }
  | [^ '\\' '\"'] as c
      { Buffer.add_char string_buf c; parsestring lexbuf }


(* Section comment *)
and section_comment = parse
  | "*/" as s
      { Buffer.add_string string_buf s }
  | eof
      { let s = Ustring.from_utf8 ("/*" ^ (Buffer.contents string_buf)) in
	raise (Lex_error (LEX_COMMENT_NOT_TERMINATED,ERROR,
	 	 mkinfo_ustring s, [s])) }
  | _ as c
      { Buffer.add_char string_buf c; section_comment lexbuf }
