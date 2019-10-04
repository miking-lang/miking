

(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
 *)

open Ast

let translate t =
  match t with
  | TmlExpr(_,e) -> e
