open Extast
open Ast
open Msg
open Sundials
open Bigarray

let externals =
  List.map (fun x -> (fst x,  TmConst (NoInfo,CExt (snd x))))
    [
      ("eapp", EApp None);
      (* Elementary functions *)
      ("sin", Esin);
      ("cos", Ecos);
      (* SundialsML related functions *)
      ("sArrMake", ESArrayMake None);
      ("sArrGet", ESArrayGet None);
      ("sArrSet", ESArraySet (None, None));
      ("sArrLength", ESArrayLength);
      ("sMatrixDenseSet", ESMatrixDenseSet (None, None, None));
      ("idaInitDense", EIdaInitDense (None, None, None, None));
      ("idaInitDenseJac", EIdaInitDenseJac (None, None, None, None, None));
      ("idaSolveNormal", EIdaSolveNormal (None, None, None));
      ("idaCalcICYY", EIdaCalcICYY (None, None))
    ]

let arity = function
  | EApp None -> 2
  | EApp (Some _) -> 1
  (* Elementary functions *)
  | Esin -> 1
  | Ecos -> 1
  (* SundialsML related functions *)
  | ESArray _ -> 0
  | ESArrayMake None -> 2
  | ESArrayMake (Some _) -> 1
  | ESArrayGet None -> 2
  | ESArrayGet (Some _) -> 1
  | ESArraySet (None, None) -> 3
  | ESArraySet (Some _, None) -> 2
  | ESArraySet (_, Some _) -> 1
  | ESArrayLength -> 1
  | ESMatrixDense _ -> 0
  | ESMatrixDenseSet (None, None, None) -> 4
  | ESMatrixDenseSet (Some _, None, None) -> 3
  | ESMatrixDenseSet (_, Some _, None) -> 2
  | ESMatrixDenseSet (_, _, Some _) -> 1
  | EIdaSession _ -> 0
  | EIdaInitDense (None, None, None, None) -> 5
  | EIdaInitDense (Some _, None, None, None) -> 4
  | EIdaInitDense (_, Some _, None, None) -> 3
  | EIdaInitDense (_, _, Some _, None) -> 2
  | EIdaInitDense (_, _, _, Some _) -> 1
  | EIdaInitDenseJac (None, None, None, None, None) -> 6
  | EIdaInitDenseJac (Some _, None, None, None, None) -> 5
  | EIdaInitDenseJac (_, Some _, None, None, None) -> 4
  | EIdaInitDenseJac (_, _, Some _, None, None) -> 3
  | EIdaInitDenseJac (_, _, _, Some _, None) -> 2
  | EIdaInitDenseJac (_, _, _, _, Some _) -> 1
  | EIdaSolveNormal (None, None, None) -> 4
  | EIdaSolveNormal (Some _, None, None) -> 3
  | EIdaSolveNormal (_, Some _, None) -> 2
  | EIdaSolveNormal (_, _, Some _) -> 1
  | EIdaCalcICYY (None, None) -> 3
  | EIdaCalcICYY (Some _, None) -> 2
  | EIdaCalcICYY (_, Some _) -> 1

let fail_extapp f v fi = raise_error fi
                           ("Incorrect application. External function: "
                            ^ Ustring.to_utf8 (Extpprint.pprint f)
                            ^ " value: "
                            ^ Ustring.to_utf8 (Pprint.pprintME v))

let delta eval env fi c v =
  let fail_extapp = fail_extapp c v in
  let mk_float fi f = TmConst (fi, CFloat f) in
  let mk_int fi n = TmConst (fi, CInt n) in
  let mk_ext fi e = TmConst (fi, CExt e) in
  let mk_unit fi = TmConst (fi, Cunit) in
  let mk_app fi f v = TmApp (fi, f, v) in
  let mk_sa_array fi a = mk_ext fi (ESArray a) in
  let mk_sa_matrix_dense fi m = mk_ext fi (ESMatrixDense m) in
  let mk_tuple fi l = TmTuple (fi, l) in

  let mk_resf tm_resf =
     let resf t y y' r =
       let _ = eval env (List.fold_left (mk_app NoInfo) tm_resf
                           [mk_float NoInfo t;
                            mk_sa_array NoInfo y;
                            mk_sa_array NoInfo y';
                            mk_sa_array NoInfo r])
       in ()
     in resf
  in

  match c, v with
  | EApp None, TmClos (fi, _, _, _, _) | EApp None, TmConst (fi,  _) ->
     mk_ext fi (EApp (Some (fun x -> eval env (mk_app NoInfo v x))))
  | EApp (Some f), _ -> (f v)
  | EApp _,_ -> fail_extapp fi
  (* Elementary functions *)
  | Esin, TmConst (fi, CFloat f) -> mk_float fi (sin f)
  | Esin,_ -> fail_extapp fi

  | Ecos, TmConst (fi, CFloat f) -> mk_float fi (cos f)
  | Ecos,_ -> fail_extapp fi

  (* SundialsML related functions *)
  | ESArray _,_ -> fail_extapp fi
  | ESArrayMake None, TmConst (fi, CInt n) ->
     mk_ext fi (ESArrayMake (Some n))
  | ESArrayMake (Some n), TmConst (fi, CFloat v) ->
     mk_ext fi (ESArray (RealArray.make n v))
  | ESArrayMake _,_ -> fail_extapp fi

  | ESArrayGet None, TmConst (fi, CExt (ESArray a)) ->
     mk_ext fi (ESArrayGet (Some a))
  | ESArrayGet (Some a), TmConst (fi, CInt n) ->
     mk_float fi (try Array1.get a n with _ ->
                    raise_error fi (Printf.sprintf "Index: %d out of bounds" n))
  | ESArrayGet _,_ -> fail_extapp fi

  | ESArraySet (None, None), TmConst (fi, CExt (ESArray a)) ->
     mk_ext fi (ESArraySet (Some a, None))
  | ESArraySet (Some a, None), TmConst (fi, CInt n) ->
     mk_ext fi (ESArraySet (Some a, Some n))
  | ESArraySet (Some a, Some n), TmConst (fi, CFloat f) ->
     (try Array1.set a n f with _ ->
        raise_error fi (Printf.sprintf "Index: %d out of bounds" n));
     mk_unit fi
  | ESArraySet _,_ -> fail_extapp fi

  | ESArrayLength, TmConst (fi, CExt (ESArray a)) ->
     mk_int fi (RealArray.length a)
  | ESArrayLength,_ -> fail_extapp fi

  | ESMatrixDense _,_ -> fail_extapp fi

  | ESMatrixDenseSet (None, None, None), TmConst (fi, CExt (ESMatrixDense m)) ->
     mk_ext fi (ESMatrixDenseSet (Some m, None, None))
  | ESMatrixDenseSet (Some m, None, None), TmConst (fi, CInt i) ->
     mk_ext fi (ESMatrixDenseSet (Some m, Some i, None))
  | ESMatrixDenseSet (Some m, Some i, None), TmConst (fi, CInt j) ->
     mk_ext fi (ESMatrixDenseSet (Some m, Some i, Some j))
  | ESMatrixDenseSet (Some m, Some i, Some j), TmConst (fi, CFloat f) ->
     (try Matrix.Dense.set m i j f with _ ->
        raise_error fi (Printf.sprintf "Index: (%d,%d) out of bounds" i j));
     mk_unit fi
  | ESMatrixDenseSet _,_ -> fail_extapp fi

  | EIdaSession _,_ -> fail_extapp fi

  | EIdaInitDense (None, None, None, None),
    TmTuple (fi ,
             (TmConst (_, CFloat rtol))::((TmConst (_, CFloat atol))::[])) ->
     mk_ext fi (EIdaInitDense (Some (rtol, atol), None, None, None))
  | EIdaInitDense (Some tol, None, None, None), tm_resf ->
     mk_ext (tm_info tm_resf)
       (EIdaInitDense (Some tol, Some (mk_resf tm_resf), None, None))
  | EIdaInitDense (Some tol, Some resf, None, None),
    TmConst (fi, CFloat t0) ->
     mk_ext fi (EIdaInitDense (Some tol, Some resf, Some t0, None))
  | EIdaInitDense (Some tol, Some resf, Some t0, None),
    TmConst (fi, CExt (ESArray y0)) ->
     mk_ext fi (EIdaInitDense (Some tol, Some resf, Some t0, Some y0))
  | EIdaInitDense (Some (rtol, atol), Some resf, Some t0, Some y0),
    TmConst (fi, CExt (ESArray y0')) ->
     let m = Matrix.dense (RealArray.length y0) in
     let v = Nvector_serial.wrap y0 in
     let v' = Nvector_serial.wrap y0' in
     let s = Ida.(init Dls.(solver (dense v m))
                    (SStolerances (rtol, atol))
                    resf t0 v v')
     in
     mk_ext fi (EIdaSession s)
  | EIdaInitDense _,_ -> fail_extapp fi

  | EIdaInitDenseJac (None, None, None, None, None),
    TmTuple (fi ,
             (TmConst (_, CFloat rtol))::((TmConst (_, CFloat atol))::[])) ->
     mk_ext fi (EIdaInitDenseJac (Some (rtol, atol), None, None, None, None))
  | EIdaInitDenseJac (Some tol, None, None, None, None), tm_jacf ->
     let jacf arg mm =
       match arg with
         {
           Ida.jac_t=t;
           Ida.jac_coef=cj;
           Ida.jac_y=y;
           Ida.jac_y'=y';
           _;
         } ->
          let _ = eval env (List.fold_left (mk_app NoInfo) tm_jacf
                              [mk_float NoInfo t;
                               mk_float NoInfo cj;
                               mk_sa_array NoInfo y;
                               mk_sa_array NoInfo y';
                               mk_sa_matrix_dense NoInfo mm])
          in ()
     in
     mk_ext (tm_info tm_jacf)
       (EIdaInitDenseJac (Some tol, Some jacf, None, None, None))
  | EIdaInitDenseJac (Some tol, Some jacf, None, None, None), tm_resf ->
     mk_ext (tm_info tm_resf)
       (EIdaInitDenseJac (Some tol, Some jacf, Some (mk_resf tm_resf),
                          None, None))
  | EIdaInitDenseJac (Some tol, Some jacf, Some resf, None, None),
    TmConst (fi, CFloat t0) ->
     mk_ext fi
       (EIdaInitDenseJac (Some tol, Some jacf, Some resf, Some t0, None))
  | EIdaInitDenseJac (Some tol, Some jacf, Some resf, Some t0, None),
    TmConst (fi, CExt (ESArray y0)) ->
     mk_ext fi
       (EIdaInitDenseJac (Some tol, Some jacf, Some resf, Some t0, Some y0))
  | EIdaInitDenseJac (Some (rtol, atol), Some jacf, Some resf, Some t0, Some y0),
    TmConst (fi, CExt (ESArray y0')) ->
     let m = Matrix.dense (RealArray.length y0) in
     let v = Nvector_serial.wrap y0 in
     let v' = Nvector_serial.wrap y0' in
     let s = Ida.(init Dls.(solver ~jac:jacf (dense v m))
                    (SStolerances (rtol, atol))
                    resf t0 v v')
     in
     mk_ext fi (EIdaSession s)
  | EIdaInitDenseJac _,_ -> fail_extapp fi

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
  | EIdaSolveNormal _,_ -> fail_extapp fi

  | EIdaCalcICYY (None, None), TmConst (fi, CExt (EIdaSession s)) ->
     mk_ext fi (EIdaCalcICYY (Some s, None))
  | EIdaCalcICYY (Some s, None), TmConst (fi, CExt (ESArray y)) ->
     mk_ext fi (EIdaCalcICYY (Some s, Some (Nvector_serial.wrap y)))
  | EIdaCalcICYY (Some s, Some y), TmConst (fi, CFloat t) ->
     Ida.calc_ic_y s ~y:y t;
     mk_unit fi
  | EIdaCalcICYY _,_ -> fail_extapp fi
