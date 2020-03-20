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
                            ^ Ustring.to_utf8 (Pprint.pprintME v))

let delta eval env c v =
  let fail_extapp = fail_extapp c v in
  let _ext fi e = TmConst (fi, CExt e) in
  let _app fi l r = TmApp (fi, l, r) in
  match c, v with
  | EApp None, TmClos (fi, _, _, _, _) | EApp None, TmConst (fi,  _) ->
     _ext fi (EApp (Some (fun x -> eval env (_app NoInfo v x))))
  | EApp (Some f), _ -> (f v)
  | EApp _, t -> fail_extapp (tm_info t)
