(* open Printf *)
open Extast
open Ast
open Msg

let externals =
  List.map (fun x -> (fst x,  CExt (snd x)))
  [
    ("sin", Esin);
    ("cos", Ecos)
  ]

let arity = function
  | Esin -> 1
  | Ecos -> 1

let fail_extapp f v fi = raise_error fi
                           ("Incorrect application. External function: "
                            ^ Ustring.to_utf8 (Extpprint.pprint f)
                            ^ " value: "
                            ^ Ustring.to_utf8 (Pprint.pprintME v))

let delta c v =
  let fail_extapp = fail_extapp c v in
  match c, v with
  | Esin, TmConst(fi, CFloat(f)) -> TmConst(fi, CFloat (sin f))
  | Esin, t -> fail_extapp (tm_info t)

  | Ecos, TmConst(fi, CFloat(f)) -> TmConst(fi, CFloat (cos f))
  | Ecos, t -> fail_extapp (tm_info t)
