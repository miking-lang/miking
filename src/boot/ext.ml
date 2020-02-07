open Extast
open Ast
open Msg
open Sundials
open Bigarray

let externals =
  List.map (fun x -> (fst x,  CExt (snd x)))
    [
      ("eapp", EApp None);
      (* Elementary funtions *)
      ("sin", Esin);
      ("cos", Ecos);
      (* SundialsML related functions *)
      ("sArrCreate", ESArrayCreate);
      ("sArrGet", ESArrayGet None);
      ("sArrSet", ESArraySet (None, None));
      ("sArrLength", ESArrayLength);
      ("idaInit", EIdaInit (None, None, None, None));
      ("idaSolveNormal", EIdaSolveNormal (None, None, None))
    ]

let arity = function
  | EApp _ -> 2
  (* Elementary funtions *)
  | Esin -> 1
  | Ecos -> 1
  (* SundialsML related functions *)
  | ESArray _ -> 0
  | ESArrayCreate -> 1
  | ESArrayGet _ -> 2
  | ESArraySet _ -> 3
  | ESArrayLength -> 1
  | EIdaSession _ -> 0
  | EIdaInit _ -> 5
  | EIdaSolveNormal _ -> 4

let fail_extapp f v fi = raise_error fi
                           ("Incorrect application. External function: "
                            ^ Ustring.to_utf8 (Extpprint.pprint f)
                            ^ " value: "
                            ^ Ustring.to_utf8 (Pprint.pprintME v))

let delta eval env c v =
  let fail_extapp = fail_extapp c v in
  let mk_float fi f = TmConst (fi, CFloat f) in
  let mk_int fi n = TmConst (fi, CInt n) in
  let mk_ext fi e = TmConst (fi, CExt e) in
  let mk_unit fi = TmConst (fi, Cunit) in
  let mk_app fi f v = TmApp (fi, f, v) in
  let mk_sa_array fi a = mk_ext fi (ESArray a) in
  let mk_tuple fi l = TmTuple (fi, l) in

  match c, v with
  | EApp None, TmClos (fi, _, _, _, _) | EApp None, TmConst (fi,  _) ->
     mk_ext fi (EApp (Some (fun x -> eval env (mk_app NoInfo v x))))
  | EApp (Some f), _ -> (f v)
  | EApp _, t -> fail_extapp (tm_info t)
  (* Elementary funtions *)
  | Esin, TmConst (fi, CFloat f) -> mk_float fi (sin f)
  | Esin, t -> fail_extapp (tm_info t)

  | Ecos, TmConst (fi, CFloat f) -> mk_float fi (cos f)
  | Ecos, t -> fail_extapp (tm_info t)

  (* SundialsML related functions *)
  | ESArray _, t -> fail_extapp (tm_info t)

  | ESArrayCreate, TmConst (fi, CInt n) ->
     mk_ext fi (ESArray (RealArray.create n))
  | ESArrayCreate, t -> fail_extapp (tm_info t)

  | ESArrayGet None, TmConst (fi, CExt (ESArray a)) ->
     mk_ext fi (ESArrayGet (Some a))
  | ESArrayGet (Some a), TmConst (fi, CInt n) ->
     mk_float fi (try Array1.get a n with _ ->
                    raise_error fi "Index out of bounds")
  | ESArrayGet _, t -> fail_extapp (tm_info t)

  | ESArraySet (None, None), TmConst (fi, CExt (ESArray a)) ->
     mk_ext fi (ESArraySet (Some a, None))
  | ESArraySet (Some a, None), TmConst (fi, CInt n) ->
     mk_ext fi (ESArraySet (Some a, Some n))
  | ESArraySet (Some a, Some n), TmConst (fi, CFloat f) ->
     (try Array1.set a n f with _ -> raise_error fi "Index out of bounds");
     mk_unit fi
  | ESArraySet _, t -> fail_extapp (tm_info t)

  | ESArrayLength, TmConst (fi, CExt (ESArray a)) ->
     mk_int fi (Sundials.RealArray.length a)
  | ESArrayLength, t -> fail_extapp (tm_info t)

  | EIdaSession _, t -> fail_extapp (tm_info t)

  | EIdaInit (None, _, _, _),
    TmTuple (fi
           , (TmConst (_, CFloat rtol))::((TmConst (_, CFloat atol))::[])) ->
     TmConst (fi, CExt (EIdaInit (Some (rtol, atol), None, None, None)))
  | EIdaInit (Some tol, None, None, None), tm_resf ->
     let resf t y y' r =
       let _ = eval env (List.fold_left (mk_app NoInfo) tm_resf
                   [mk_float NoInfo t;
                    mk_sa_array NoInfo y;
                    mk_sa_array NoInfo y';
                    mk_sa_array NoInfo r])
       in ()
     in
     mk_ext (tm_info tm_resf) (EIdaInit (Some tol, Some resf, None, None))
  | EIdaInit (Some tol, Some resf, None, None), TmConst (fi, CFloat t0) ->
     mk_ext fi (EIdaInit (Some tol, Some resf, Some t0, None))
  | EIdaInit (Some tol, Some resf, Some t0, None),
    TmConst (fi, CExt (ESArray y0)) ->
     mk_ext fi (EIdaInit (Some tol, Some resf, Some t0, Some y0))
  | EIdaInit (Some (rtol, atol), Some resf, Some t0, Some y0),
    TmConst (fi, CExt (ESArray y0')) ->
     let m = Matrix.dense (RealArray.length y0) in
     let v = Nvector_serial.wrap y0 in
     let v' = Nvector_serial.wrap y0' in
     let s = Ida.(init Dls.(solver (dense v m))
                    (SStolerances (rtol, atol))
                    resf t0 v v')
     in
     mk_ext fi (EIdaSession s)
  | EIdaInit _, t -> fail_extapp (tm_info t)

  | EIdaSolveNormal (None, None, None), TmConst (fi, CExt (EIdaSession s)) ->
     mk_ext fi (EIdaSolveNormal (Some s, None, None))
  | EIdaSolveNormal (Some s, None, None), TmConst (fi, CFloat t) ->
     mk_ext fi (EIdaSolveNormal (Some s, Some t, None))
  | EIdaSolveNormal (Some s, Some t, None), TmConst (fi, CExt (ESArray y)) ->
     mk_ext fi (EIdaSolveNormal (Some s, Some t, Some (Nvector_serial.wrap y)))
  | EIdaSolveNormal (Some s, Some t, Some v), TmConst (fi, CExt (ESArray y')) ->
     let ret2int = function
       | Ida.Success -> 0
       | Ida.RootsFound -> 2
       | Ida.StopTimeReached -> 1
     in
     let v' = Nvector_serial.wrap y' in
     let (t', r) = Ida.solve_normal s t v v' in
     mk_tuple fi [mk_float NoInfo t'; mk_int NoInfo (ret2int r)]
  | EIdaSolveNormal _, t -> fail_extapp (tm_info t)
