open Extast
open Ast
open Msg

let externals =
  List.map (fun x -> (fst x,  CExt (snd x)))
    [
      (* Elementary funtions *)
      ("sin", Esin);
      ("cos", Ecos);
      (* SundialsML related functions *)
      ("sArrCreate", ESArrayCreate);
      ("sArrGet", ESArrayGet None);
      ("sArrSet", ESArraySet (None, None))
      (* ("idaInit", EIdaInit (None, None, None, None)) *)
    ]

let arity = function
  (* Elementary funtions *)
  | Esin -> 1
  | Ecos -> 1
  (* SundialsML related functions *)
  | ESArray _ -> 0
  | ESArrayCreate -> 1
  | ESArrayGet _ -> 2
  | ESArraySet _ -> 3
  | EIdaSession _ -> 0
  (* | EIdaInit _ -> 5 *)

let fail_extapp f v fi = raise_error fi
                           ("Incorrect application. External function: "
                            ^ Ustring.to_utf8 (Extpprint.pprint f)
                            ^ " value: "
                            ^ Ustring.to_utf8 (Pprint.pprintME v))

let delta c v =
  let fail_extapp = fail_extapp c v in
  let _float fi f = TmConst (fi, CFloat f) in
  let _ext fi e = TmConst (fi, CExt e) in
  let _unit fi = TmConst (fi, Cunit) in
  match c, v with
  (* Elementary funtions *)
  | Esin, TmConst (fi, CFloat f) -> _float fi (sin f)
  | Esin, t -> fail_extapp (tm_info t)

  | Ecos, TmConst (fi, CFloat f) -> _float fi (cos f)
  | Ecos, t -> fail_extapp (tm_info t)

  (* SundialsML related functions *)
  | ESArray _, t -> fail_extapp (tm_info t)

  | ESArrayCreate, TmConst (fi, CInt n) ->
     _ext fi (ESArray (Sundials.RealArray.create n))
  | ESArrayCreate, t -> fail_extapp (tm_info t)

  | ESArrayGet None, TmConst (fi, CExt (ESArray a)) ->
     _ext fi (ESArrayGet (Some a))
  | ESArrayGet (Some a), TmConst (fi, CInt n) ->
     _float fi (try Bigarray.Array1.get a n with _ ->
                  raise_error fi "Index out of bounds")
  | ESArrayGet _, t -> fail_extapp (tm_info t)

  | ESArraySet (None, None), TmConst (fi, CExt (ESArray a)) ->
     _ext fi (ESArraySet (Some a, None))
  | ESArraySet (Some a, None), TmConst (fi, CInt n) ->
     _ext fi (ESArraySet (Some a, Some n))
  | ESArraySet (Some a, Some n), TmConst (fi, CFloat f) ->
     (try Bigarray.Array1.set a n f with _ ->
        raise_error fi "Index out of bounds");
     _unit fi
  | ESArraySet _, t -> fail_extapp (tm_info t)

  | EIdaSession _, t -> fail_extapp (tm_info t)

  (* | EIdaInit (None, _, _, _),
   *   TmTuple (fi, (TmConst (_, CFloat rtol))::((TmConst (_, CFloat atol))::[])) ->
   *    TmConst (fi, CExt (EIdaInit (Some (rtol, atol), None, None, None)))
   * | EIdaInit (Some(tol), None, None, None), TmClos  *)
