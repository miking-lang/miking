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
      ("sMatrixDenseCreate", ESMatrixDenseCreate None);
      ("sMatrixDenseGet", ESMatrixDenseGet (None, None));
      ("sMatrixDenseSet", ESMatrixDenseSet (None, None, None));
      ("idaInitDense", EIdaInitDense (None, None, None, None, None));
      ("idaInitDenseJac", EIdaInitDenseJac (None, None, None, None, None, None));
      ("idaSolveNormal", EIdaSolveNormal (None, None, None));
      ("idaCalcICYY", EIdaCalcICYY (None, None));
      ("idaReinit", EIdaReinit (None, None, None));
      ("idaGetDky", EIdaGetDky (None, None, None));
      ("idaGetCurrentTime", EIdaGetCurrentTime);
      ("idaGetLastStep", EIdaGetLastStep)
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
  | ESMatrixDenseCreate None -> 2
  | ESMatrixDenseCreate (Some _) -> 1
  | ESMatrixDenseGet (None, None) -> 3
  | ESMatrixDenseGet (Some _, None) -> 2
  | ESMatrixDenseGet (_, Some _) -> 1
  | ESMatrixDenseSet (None, None, None) -> 4
  | ESMatrixDenseSet (Some _, None, None) -> 3
  | ESMatrixDenseSet (_, Some _, None) -> 2
  | ESMatrixDenseSet (_, _, Some _) -> 1
  | EIdaSession _ -> 0
  | EIdaInitDense (None, None, None, None, None) -> 6
  | EIdaInitDense (Some _, None, None, None, None) -> 5
  | EIdaInitDense (_, Some _, None, None, None) -> 4
  | EIdaInitDense (_, _, Some _, None, None) -> 3
  | EIdaInitDense (_, _, _, Some _, None) -> 2
  | EIdaInitDense (_, _, _, _, Some _) -> 1
  | EIdaInitDenseJac (None, None, None, None, None, None) -> 7
  | EIdaInitDenseJac (Some _, None, None, None, None, None) -> 6
  | EIdaInitDenseJac (_, Some _, None, None, None, None) -> 5
  | EIdaInitDenseJac (_, _, Some _, None, None, None) -> 4
  | EIdaInitDenseJac (_, _, _, Some _, None, None) -> 3
  | EIdaInitDenseJac (_, _, _, _, Some _, None) -> 2
  | EIdaInitDenseJac (_, _, _, _, _, Some _) -> 1
  | EIdaSolveNormal (None, None, None) -> 4
  | EIdaSolveNormal (Some _, None, None) -> 3
  | EIdaSolveNormal (_, Some _, None) -> 2
  | EIdaSolveNormal (_, _, Some _) -> 1
  | EIdaCalcICYY (None, None) -> 3
  | EIdaCalcICYY (Some _, None) -> 2
  | EIdaCalcICYY (_, Some _) -> 1
  | EIdaReinit (None, None, None) -> 4
  | EIdaReinit (Some _, None, None) -> 3
  | EIdaReinit (_, Some _, None) -> 2
  | EIdaReinit (_, _, Some _) -> 1
  | EIdaGetDky (None, None, None) -> 4
  | EIdaGetDky (Some _, None, None) -> 3
  | EIdaGetDky (_, Some _, None) -> 2
  | EIdaGetDky (_, _, Some _) -> 1
  | EIdaGetCurrentTime -> 1
  | EIdaGetLastStep -> 1

let fail_extapp f v fi = raise_error fi
                           ("Incorrect application. External function: "
                            ^ Ustring.to_utf8 (Extpprint.pprint f)
                            ^ " value: "
                            ^ Ustring.to_utf8
                              (Pprint.ustring_of_tm v))

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

  let mk_idafun tm_fun =
     let resf t y y' r =
       let _ = eval env (List.fold_left (mk_app NoInfo) tm_fun
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
  | Esin, TmConst (_, CFloat f) -> mk_float fi (sin f)
  | Esin,_ -> fail_extapp fi

  | Ecos, TmConst (_, CFloat f) -> mk_float fi (cos f)
  | Ecos,_ -> fail_extapp fi

  (* SundialsML related functions *)
  | ESArray _,_ -> fail_extapp fi
  | ESArrayMake None, TmConst (_, CInt n) ->
     mk_ext fi (ESArrayMake (Some n))
  | ESArrayMake (Some n), TmConst (_, CFloat v) ->
     mk_ext fi (ESArray (RealArray.make n v))
  | ESArrayMake _,_ -> fail_extapp fi

  | ESArrayGet None, TmConst (_, CExt (ESArray a)) ->
     mk_ext fi (ESArrayGet (Some a))
  | ESArrayGet (Some a), TmConst (_, CInt n) ->
     mk_float fi (try Array1.get a n with _ ->
                    raise_error fi (Printf.sprintf "Index: %d out of bounds" n))
  | ESArrayGet _,_ -> fail_extapp fi

  | ESArraySet (None, None), TmConst (_, CExt (ESArray a)) ->
     mk_ext fi (ESArraySet (Some a, None))
  | ESArraySet (Some a, None), TmConst (_, CInt n) ->
     mk_ext fi (ESArraySet (Some a, Some n))
  | ESArraySet (Some a, Some n), TmConst (_, CFloat f) ->
     (try Array1.set a n f with _ ->
        raise_error fi (Printf.sprintf "Index: %d out of bounds" n));
     mk_unit fi
  | ESArraySet _,_ -> fail_extapp fi

  | ESArrayLength, TmConst (_, CExt (ESArray a)) ->
     mk_int fi (RealArray.length a)
  | ESArrayLength,_ -> fail_extapp fi

  | ESMatrixDense _,_ -> fail_extapp fi

  | ESMatrixDenseCreate (None), TmConst (_, CInt i) ->
     mk_ext fi (ESMatrixDenseCreate (Some i))
  | ESMatrixDenseCreate (Some i), TmConst (_, CInt j) ->
     mk_ext fi (ESMatrixDense (Matrix.Dense.create i j))
  | ESMatrixDenseCreate _,_ -> fail_extapp fi

  | ESMatrixDenseGet (None, None), TmConst (_, CExt (ESMatrixDense m)) ->
     mk_ext fi (ESMatrixDenseGet (Some m, None))
  | ESMatrixDenseGet (Some m, None), TmConst (_, CInt i) ->
     mk_ext fi (ESMatrixDenseGet (Some m, Some i))
  | ESMatrixDenseGet (Some m, Some i), TmConst (_, CInt j) ->
     let (k, l) = Matrix.Dense.size m in
     if i >= 0 && i < k && j >= 0 && j < l then
       mk_float fi (Matrix.Dense.get m i j)
     else
       raise_error fi (Printf.sprintf "Index: (%d,%d) out of bounds" i j)
  | ESMatrixDenseGet _,_ -> fail_extapp fi

  | ESMatrixDenseSet (None, None, None), TmConst (_, CExt (ESMatrixDense m)) ->
     mk_ext fi (ESMatrixDenseSet (Some m, None, None))
  | ESMatrixDenseSet (Some m, None, None), TmConst (_, CInt i) ->
     mk_ext fi (ESMatrixDenseSet (Some m, Some i, None))
  | ESMatrixDenseSet (Some m, Some i, None), TmConst (_, CInt j) ->
     mk_ext fi (ESMatrixDenseSet (Some m, Some i, Some j))
  | ESMatrixDenseSet (Some m, Some i, Some j), TmConst (_, CFloat f) ->
     (try Matrix.Dense.set m i j f with _ ->
        raise_error fi (Printf.sprintf "Index: (%d,%d) out of bounds" i j));
     mk_unit fi
  | ESMatrixDenseSet _,_ -> fail_extapp fi

  | EIdaSession _,_ -> fail_extapp fi

  | EIdaInitDense (None, None, None, None, None),
    TmTuple (_,
             (TmConst (_, CFloat rtol))::((TmConst (_, CFloat atol))::[])) ->
     mk_ext fi (EIdaInitDense (Some (rtol, atol), None, None, None, None))
  | EIdaInitDense (Some tol, None, None, None, None), tm_resf ->
     mk_ext (tm_info tm_resf)
       (EIdaInitDense (Some tol, Some (mk_idafun tm_resf), None, None, None))
  | EIdaInitDense (Some tol, Some resf, None, None, None),
    TmTuple (_, (TmConst (_, CInt n))::(tm_rootf::[])) ->
     mk_ext fi (EIdaInitDense (Some tol,
                               Some resf,
                               Some (n, mk_idafun tm_rootf),
                               None, None))
  | EIdaInitDense (Some tol, Some resf, Some (n, rootf), None, None),
    TmConst (_, CFloat t0) ->
     mk_ext fi (EIdaInitDense (Some tol,
                               Some resf,
                               Some (n, rootf),
                               Some t0,
                               None))
  | EIdaInitDense (Some tol, Some resf, Some (n, rootf), Some t0, None),
    TmConst (_, CExt (ESArray y0)) ->
     mk_ext fi (EIdaInitDense (Some tol,
                               Some resf,
                               Some (n, rootf),
                               Some t0,
                               Some y0))
  | EIdaInitDense (Some (rtol, atol), Some resf, Some (n, rootf), Some t0,
                   Some y0),
    TmConst (_, CExt (ESArray y0')) ->
     let m = Matrix.dense (RealArray.length y0) in
     let v = Nvector_serial.wrap y0 in
     let v' = Nvector_serial.wrap y0' in
     let s = Ida.(init Dls.(solver (dense v m))
                    (SStolerances (rtol, atol))
                    resf ~roots:(n, rootf) t0 v v')
     in
     mk_ext fi (EIdaSession s)
  | EIdaInitDense _,_ -> fail_extapp fi

  | EIdaInitDenseJac (None, None, None, None, None, None),
    TmTuple (_,
             (TmConst (_, CFloat rtol))::((TmConst (_, CFloat atol))::[])) ->
     mk_ext fi (EIdaInitDenseJac (Some (rtol, atol),
                                  None, None, None, None, None))
  | EIdaInitDenseJac (Some tol, None, None, None, None, None), tm_jacf ->
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
     mk_ext (tm_info tm_jacf) (EIdaInitDenseJac (Some tol,
                                                 Some jacf,
                                                 None, None, None, None))
  | EIdaInitDenseJac (Some tol, Some jacf, None, None, None, None), tm_resf ->
     mk_ext (tm_info tm_resf) (EIdaInitDenseJac (Some tol,
                                                 Some jacf,
                                                 Some (mk_idafun tm_resf),
                                                 None, None, None))
  | EIdaInitDenseJac (Some tol, Some jacf, Some resf, None, None, None),
    TmTuple (_, (TmConst (_, CInt n))::(tm_rootf::[])) ->
     mk_ext fi (EIdaInitDenseJac (Some tol,
                                  Some jacf,
                                  Some resf,
                                  Some (n, mk_idafun tm_rootf),
                                  None, None))
  | EIdaInitDenseJac (Some tol, Some jacf, Some resf, Some (n, rootf),
                      None, None),
    TmConst (_, CFloat t0) ->
     mk_ext fi (EIdaInitDenseJac (Some tol,
                                  Some jacf,
                                  Some resf,
                                  Some (n, rootf),
                                  Some t0,
                                  None))
  | EIdaInitDenseJac (Some tol, Some jacf, Some resf, Some (n, rootf), Some t0,
                      None),
    TmConst (fi, CExt (ESArray y0)) ->
     mk_ext fi (EIdaInitDenseJac (Some tol,
                                  Some jacf,
                                  Some resf,
                                  Some (n, rootf),
                                  Some t0,
                                  Some y0))
  | EIdaInitDenseJac (Some (rtol, atol), Some jacf, Some resf, Some (n, rootf),
                      Some t0, Some y0),
    TmConst (_, CExt (ESArray y0')) ->
     let m = Matrix.dense (RealArray.length y0) in
     let v = Nvector_serial.wrap y0 in
     let v' = Nvector_serial.wrap y0' in
     let s = Ida.(init Dls.(solver ~jac:jacf (dense v m))
                    ~roots:(n, rootf)
                    (SStolerances (rtol, atol))
                    resf t0 v v')
     in
     mk_ext fi (EIdaSession s)
  | EIdaInitDenseJac _,_ -> fail_extapp fi

  | EIdaSolveNormal (None, None, None), TmConst (_, CExt (EIdaSession s)) ->
     mk_ext fi (EIdaSolveNormal (Some s, None, None))
  | EIdaSolveNormal (Some s, None, None), TmConst (_, CFloat t) ->
     mk_ext fi (EIdaSolveNormal (Some s, Some t, None))
  | EIdaSolveNormal (Some s, Some t, None), TmConst (_, CExt (ESArray y)) ->
     mk_ext fi (EIdaSolveNormal (Some s, Some t, Some (Nvector_serial.wrap y)))
  | EIdaSolveNormal (Some s, Some t, Some v), TmConst (_, CExt (ESArray y')) ->
     let ret2int = function
       | Ida.Success -> 0
       | Ida.RootsFound -> 2
       | Ida.StopTimeReached -> 1
     in
     let v' = Nvector_serial.wrap y' in
     let (t', r) = Ida.solve_normal s t v v' in
     mk_tuple fi [mk_float NoInfo t'; mk_int NoInfo (ret2int r)]
  | EIdaSolveNormal _,_ -> fail_extapp fi

  | EIdaCalcICYY (None, None), TmConst (_, CExt (EIdaSession s)) ->
     mk_ext fi (EIdaCalcICYY (Some s, None))
  | EIdaCalcICYY (Some s, None), TmConst (_, CExt (ESArray y)) ->
     mk_ext fi (EIdaCalcICYY (Some s, Some (Nvector_serial.wrap y)))
  | EIdaCalcICYY (Some s, Some v), TmConst (_, CFloat t) ->
     Ida.calc_ic_y s ~y:v t;
     mk_unit fi
  | EIdaCalcICYY _,_ -> fail_extapp fi

  | EIdaReinit (None, None, None), TmConst (_, CExt (EIdaSession s)) ->
     mk_ext fi (EIdaReinit (Some s, None, None))
  | EIdaReinit (Some s, None, None), TmConst (_, CFloat t) ->
     mk_ext fi (EIdaReinit (Some s, Some t, None))
  | EIdaReinit (Some s, Some t, None), TmConst (_, CExt (ESArray y)) ->
     mk_ext fi (EIdaReinit (Some s, Some t, Some (Nvector_serial.wrap y)))
  | EIdaReinit (Some s, Some t, Some v), TmConst (_, CExt (ESArray y')) ->
     Ida.reinit s t v (Nvector_serial.wrap y');
     mk_unit fi
  | EIdaReinit _,_ -> fail_extapp fi

  | EIdaGetDky (None, None, None), TmConst (_, CExt (EIdaSession s)) ->
     mk_ext fi (EIdaGetDky (Some s, None, None))
  | EIdaGetDky (Some s, None, None), TmConst (_, CExt (ESArray y)) ->
     mk_ext fi (EIdaGetDky (Some s, Some (Nvector_serial.wrap y), None))
  | EIdaGetDky (Some s, Some y, None), TmConst (_, CFloat t) ->
     mk_ext fi (EIdaGetDky (Some s, Some y, Some t))
  | EIdaGetDky (Some s, Some y, Some t), TmConst (_, CInt n) ->
     Ida.get_dky s y t n;
     mk_unit fi
  | EIdaGetDky _,_ -> fail_extapp fi

  | EIdaGetCurrentTime, TmConst (_, CExt (EIdaSession s)) ->
     mk_float fi (Ida.get_current_time s)
  | EIdaGetCurrentTime, _ -> fail_extapp fi

  | EIdaGetLastStep, TmConst (_, CExt (EIdaSession s)) ->
     mk_float fi (Ida.get_last_step s)
  | EIdaGetLastStep, _ -> fail_extapp fi
