(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   msg.ml includes standard error messages for the lexer and the
   parser. It also keeps track of row and column numbers for reporting
   error messages.
*)

open Ustring.Op

type row = int

type col = int

type filename = ustring

type info = Info of filename * row * col * row * col | NoInfo

type id =
  | LEX_UNKNOWN_CHAR
  | LEX_COMMENT_NOT_TERMINATED
  | LEX_STRING_NOT_TERMINATED
  | LEX_INVALID_ESCAPE
  | PARSE_ERROR
  | ERROR of string

type severity = ERROR | WARNING

type arguments = ustring list

(** Error and warning messages. Created by the lexer, parser,
    and type checker.  *)
type message = id * severity * info * arguments

exception Error of message

let eq_info a b =
  match (a, b) with
  | NoInfo, NoInfo ->
      true
  | Info (f1, l11, c11, l21, c21), Info (f2, l12, c12, l22, c22) ->
      l11 = l12 && c11 = c12 && l21 = l22 && c21 = c22 && f1 =. f2
  | _ ->
      false

(** [id2str id] returns the identifier string for [id], e.g.,
    "LEX_UNKNOWN_CHAR" *)
let id2str id =
  match id with
  | LEX_UNKNOWN_CHAR ->
      us "Unknown character"
  | LEX_COMMENT_NOT_TERMINATED ->
      us "Comment is not terminated"
  | LEX_STRING_NOT_TERMINATED ->
      us "String is not terminated"
  | LEX_INVALID_ESCAPE ->
      us "Invalid escape characters"
  | PARSE_ERROR ->
      us "Parse error"
  | ERROR msg ->
      us msg

(** [severity2str s] returns the severity strings ["ERROR"] or
    ["WARNING"]. *)
let severity2str s =
  match s with ERROR -> us "ERROR" | WARNING -> us "WARNING"

let info2str_startline fi =
  match fi with Info (_, l1, _, _, _) -> l1 | NoInfo -> assert false

let info2str = function
  | Info (filename, l1, c1, l2, c2) ->
      us "<" ^. filename ^. us " " ^. ustring_of_int l1 ^. us ":"
      ^. ustring_of_int c1 ^. us "-" ^. ustring_of_int l2 ^. us ":"
      ^. ustring_of_int c2 ^. us ">"
  | NoInfo ->
      us "NO INFO"

(** [message2str m] returns a string representation of message [m].
    Is message is not intended to be read by humans. *)
let message2str (id, sev, info, _) =
  severity2str sev ^. us " " ^. info2str info ^. us ": " ^. id2str id
  ^. us "\n"

let error_message fi sev msg : message = (ERROR msg, sev, fi, [])

let raise_error fi msg = raise (Error (error_message fi ERROR msg))

let error fi msg = raise_error fi (msg |> Ustring.to_utf8)
