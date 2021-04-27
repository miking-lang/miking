open Ast
open Msg

let float_ fi f = TmConst (fi, CFloat f)

let int_ fi n = TmConst (fi, CInt n)

let unit_ fi = TmRecord (fi, Record.empty)

let app_ fi f v = TmApp (fi, f, v)

let tuple_ = tuple2record

let fail_extapp pprint f v fi =
  raise_error fi
    ( "Incorrect application. External function: "
    ^ Ustring.to_utf8 (pprint f)
    ^ " value: "
    ^ Ustring.to_utf8 (Pprint.ustring_of_tm v) )
