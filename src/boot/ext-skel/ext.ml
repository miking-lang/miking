open Extast
open Ast
open Msg

let externals =
  List.map (fun x -> (fst x,  TmConst(NoInfo,CExt (snd x))))
  [
    ("eapp", EApp None)
  ]

let arity = function
  | EApp _ -> 2

let fail_extapp f v fi = raise_error fi
                           ("Incorrect application. External function: "
                            ^ Ustring.to_utf8 (Extpprint.pprint f)
                            ^ " value: "
                            ^ Ustring.to_utf8
                              (Pprint.ustring_of_tm v))

let delta eval env _ c v =
  let fail_extapp = fail_extapp c v in
  let mk_ext fi e = TmConst (fi, CExt e) in
  let mk_app fi f v = TmApp (fi, f, v) in

  match c, v with
  | EApp None, TmClos (fi, _, _, _, _) | EApp None, TmConst (fi,  _) ->
     mk_ext fi (EApp (Some (fun x -> eval env (mk_app NoInfo v x))))
  | EApp (Some f), _ -> (f v)
  | EApp _, t -> fail_extapp (tm_info t)
