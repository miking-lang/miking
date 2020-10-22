open Extast
open Extpprint
open Ast
open Msg

let externals =
  List.map
    (fun x -> (fst x, TmConst (NoInfo, CExt (snd x))))
    [ (* Elementary functions *)
      ("extSin", Esin)
    ; ("extCos", Ecos)
    ; ("extAtan", Eatan)
    ; ("extExp", Eexp) ]

let arity = function
  (* Elementary functions *)
  | Esin ->
      1
  | Ecos ->
      1
  | Eatan ->
      1
  | Eexp ->
      1

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

let delta _ _ fi c v =
  let fail_extapp = fail_extapp pprint c v in
  match (c, v) with
  (* Elementary functions *)
  | Esin, TmConst (_, CFloat x) ->
      float_ fi (sin x)
  | Esin, _ ->
      fail_extapp fi
  | Ecos, TmConst (_, CFloat x) ->
      float_ fi (cos x)
  | Ecos, _ ->
      fail_extapp fi
  | Eatan, TmConst (_, CFloat x) ->
      float_ fi (atan x)
  | Eatan, _ ->
      fail_extapp fi
  | Eexp, TmConst (_, CFloat x) ->
      float_ fi (exp x)
  | Eexp, _ ->
      fail_extapp fi
