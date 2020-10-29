open Ext
open Sdast
open Sdpprint
open Ast
open Msg
open Sundials
open Bigarray
open Ustring.Op

let externals =
  List.map
    (fun x -> (fst x, TmConst (NoInfo, CSd (snd x))))
    [ (* SundialsML related functions *)
      ("sArrMake", SArrayMake None)
    ; ("sArrGet", SArrayGet None)
    ; ("sArrSet", SArraySet (None, None))
    ; ("sArrLength", SArrayLength)
    ; ("sMatrixDenseCreate", SMatrixDenseCreate None)
    ; ("sMatrixDenseGet", SMatrixDenseGet (None, None))
    ; ("sMatrixDenseSet", SMatrixDenseSet (None, None, None))
    ; ("idaInitDense", SIdaInitDense (None, None, None, None, None))
    ; ("idaInitDenseJac", SIdaInitDenseJac (None, None, None, None, None, None))
    ; ("idaSolveNormal", SIdaSolveNormal (None, None, None))
    ; ("idaCalcICYY", SIdaCalcICYY (None, None))
    ; ("idaCalcICYYYP", SIdaCalcICYYYP (None, None, None, None))
    ; ("idaReinit", SIdaReinit (None, None, None))
    ; ("idaGetDky", SIdaGetDky (None, None, None))
    ; ("idaGetCurrentTime", SIdaGetCurrentTime)
    ; ("idaGetLastStep", SIdaGetLastStep) ]

let arity = function
  (* SundialsML related functions *)
  | SArray _ ->
      0
  | SArrayMake None ->
      2
  | SArrayMake (Some _) ->
      1
  | SArrayGet None ->
      2
  | SArrayGet (Some _) ->
      1
  | SArraySet (None, None) ->
      3
  | SArraySet (Some _, None) ->
      2
  | SArraySet (_, Some _) ->
      1
  | SArrayLength ->
      1
  | SMatrixDense _ ->
      0
  | SMatrixDenseCreate None ->
      2
  | SMatrixDenseCreate (Some _) ->
      1
  | SMatrixDenseGet (None, None) ->
      3
  | SMatrixDenseGet (Some _, None) ->
      2
  | SMatrixDenseGet (_, Some _) ->
      1
  | SMatrixDenseSet (None, None, None) ->
      4
  | SMatrixDenseSet (Some _, None, None) ->
      3
  | SMatrixDenseSet (_, Some _, None) ->
      2
  | SMatrixDenseSet (_, _, Some _) ->
      1
  | SIdaSession _ ->
      0
  | SIdaInitDense (None, None, None, None, None) ->
      6
  | SIdaInitDense (Some _, None, None, None, None) ->
      5
  | SIdaInitDense (_, Some _, None, None, None) ->
      4
  | SIdaInitDense (_, _, Some _, None, None) ->
      3
  | SIdaInitDense (_, _, _, Some _, None) ->
      2
  | SIdaInitDense (_, _, _, _, Some _) ->
      1
  | SIdaInitDenseJac (None, None, None, None, None, None) ->
      7
  | SIdaInitDenseJac (Some _, None, None, None, None, None) ->
      6
  | SIdaInitDenseJac (_, Some _, None, None, None, None) ->
      5
  | SIdaInitDenseJac (_, _, Some _, None, None, None) ->
      4
  | SIdaInitDenseJac (_, _, _, Some _, None, None) ->
      3
  | SIdaInitDenseJac (_, _, _, _, Some _, None) ->
      2
  | SIdaInitDenseJac (_, _, _, _, _, Some _) ->
      1
  | SIdaSolveNormal (None, None, None) ->
      4
  | SIdaSolveNormal (Some _, None, None) ->
      3
  | SIdaSolveNormal (_, Some _, None) ->
      2
  | SIdaSolveNormal (_, _, Some _) ->
      1
  | SIdaCalcICYY (None, None) ->
      3
  | SIdaCalcICYY (Some _, None) ->
      2
  | SIdaCalcICYY (_, Some _) ->
      1
  | SIdaCalcICYYYP (None, None, None, None) ->
      5
  | SIdaCalcICYYYP (Some _, None, None, None) ->
      4
  | SIdaCalcICYYYP (_, Some _, None, None) ->
      3
  | SIdaCalcICYYYP (_, _, Some _, None) ->
      2
  | SIdaCalcICYYYP (_, _, _, Some _) ->
      1
  | SIdaReinit (None, None, None) ->
      4
  | SIdaReinit (Some _, None, None) ->
      3
  | SIdaReinit (_, Some _, None) ->
      2
  | SIdaReinit (_, _, Some _) ->
      1
  | SIdaGetDky (None, None, None) ->
      4
  | SIdaGetDky (Some _, None, None) ->
      3
  | SIdaGetDky (_, Some _, None) ->
      2
  | SIdaGetDky (_, _, Some _) ->
      1
  | SIdaGetCurrentTime ->
      1
  | SIdaGetLastStep ->
      1

let delta eval env fi c v =
  let fail_extapp = fail_extapp pprint c v in
  let sd_ fi e = TmConst (fi, CSd e) in
  let sa_array_ fi a = sd_ fi (SArray a) in
  let sa_matrix_dense_ fi m = sd_ fi (SMatrixDense m) in
  let mk_idafun tm_fun =
    let resf t y y' r =
      let _ =
        eval env
          (List.fold_left (app_ NoInfo) tm_fun
             [ float_ NoInfo t
             ; sa_array_ NoInfo y
             ; sa_array_ NoInfo y'
             ; sa_array_ NoInfo r ])
      in
      ()
    in
    resf
  in
  let get_tol fi r =
    if Record.mem (us "0") r && Record.mem (us "1") r then
      match (Record.find (us "0") r, Record.find (us "1") r) with
      | TmConst (_, CFloat rtol), TmConst (_, CFloat atol) ->
          (rtol, atol)
      | _, _ ->
          fail_extapp fi
    else fail_extapp fi
  in
  let get_roots fi r =
    if Record.mem (us "0") r && Record.mem (us "1") r then
      match (Record.find (us "0") r, Record.find (us "1") r) with
      | TmConst (_, CInt n), tm_rootf ->
          (n, mk_idafun tm_rootf)
      | _, _ ->
          fail_extapp fi
    else fail_extapp fi
  in
  match (c, v) with
  (* SundialsML related functions *)
  | SArray _, _ ->
      fail_extapp fi
  | SArrayMake None, TmConst (_, CInt n) ->
      sd_ fi (SArrayMake (Some n))
  | SArrayMake (Some n), TmConst (_, CFloat v) ->
      sd_ fi (SArray (RealArray.make n v))
  | SArrayMake _, _ ->
      fail_extapp fi
  | SArrayGet None, TmConst (_, CSd (SArray a)) ->
      sd_ fi (SArrayGet (Some a))
  | SArrayGet (Some a), TmConst (_, CInt n) ->
      float_ fi
        ( try Array1.get a n
          with _ ->
            raise_error fi (Printf.sprintf "Index: %d out of bounds" n) )
  | SArrayGet _, _ ->
      fail_extapp fi
  | SArraySet (None, None), TmConst (_, CSd (SArray a)) ->
      sd_ fi (SArraySet (Some a, None))
  | SArraySet (Some a, None), TmConst (_, CInt n) ->
      sd_ fi (SArraySet (Some a, Some n))
  | SArraySet (Some a, Some n), TmConst (_, CFloat f) ->
      ( try Array1.set a n f
        with _ -> raise_error fi (Printf.sprintf "Index: %d out of bounds" n)
      ) ;
      unit_ fi
  | SArraySet _, _ ->
      fail_extapp fi
  | SArrayLength, TmConst (_, CSd (SArray a)) ->
      int_ fi (RealArray.length a)
  | SArrayLength, _ ->
      fail_extapp fi
  | SMatrixDense _, _ ->
      fail_extapp fi
  | SMatrixDenseCreate None, TmConst (_, CInt i) ->
      sd_ fi (SMatrixDenseCreate (Some i))
  | SMatrixDenseCreate (Some i), TmConst (_, CInt j) ->
      sd_ fi (SMatrixDense (Matrix.Dense.create i j))
  | SMatrixDenseCreate _, _ ->
      fail_extapp fi
  | SMatrixDenseGet (None, None), TmConst (_, CSd (SMatrixDense m)) ->
      sd_ fi (SMatrixDenseGet (Some m, None))
  | SMatrixDenseGet (Some m, None), TmConst (_, CInt i) ->
      sd_ fi (SMatrixDenseGet (Some m, Some i))
  | SMatrixDenseGet (Some m, Some i), TmConst (_, CInt j) ->
      let k, l = Matrix.Dense.size m in
      if i >= 0 && i < k && j >= 0 && j < l then
        float_ fi (Matrix.Dense.get m i j)
      else raise_error fi (Printf.sprintf "Index: (%d,%d) out of bounds" i j)
  | SMatrixDenseGet _, _ ->
      fail_extapp fi
  | SMatrixDenseSet (None, None, None), TmConst (_, CSd (SMatrixDense m)) ->
      sd_ fi (SMatrixDenseSet (Some m, None, None))
  | SMatrixDenseSet (Some m, None, None), TmConst (_, CInt i) ->
      sd_ fi (SMatrixDenseSet (Some m, Some i, None))
  | SMatrixDenseSet (Some m, Some i, None), TmConst (_, CInt j) ->
      sd_ fi (SMatrixDenseSet (Some m, Some i, Some j))
  | SMatrixDenseSet (Some m, Some i, Some j), TmConst (_, CFloat f) ->
      ( try Matrix.Dense.set m i j f
        with _ ->
          raise_error fi (Printf.sprintf "Index: (%d,%d) out of bounds" i j) ) ;
      unit_ fi
  | SMatrixDenseSet _, _ ->
      fail_extapp fi
  | SIdaSession _, _ ->
      fail_extapp fi
  | SIdaInitDense (None, None, None, None, None), TmRecord (_, r) ->
      let rtol, atol = get_tol fi r in
      sd_ fi (SIdaInitDense (Some (rtol, atol), None, None, None, None))
  | SIdaInitDense (Some tol, None, None, None, None), tm_resf ->
      sd_ (tm_info tm_resf)
        (SIdaInitDense (Some tol, Some (mk_idafun tm_resf), None, None, None))
  | SIdaInitDense (Some tol, Some resf, None, None, None), TmRecord (_, r) ->
      let n, rootf = get_roots fi r in
      sd_ fi (SIdaInitDense (Some tol, Some resf, Some (n, rootf), None, None))
  | ( SIdaInitDense (Some tol, Some resf, Some (n, rootf), None, None)
    , TmConst (_, CFloat t0) ) ->
      sd_ fi
        (SIdaInitDense (Some tol, Some resf, Some (n, rootf), Some t0, None))
  | ( SIdaInitDense (Some tol, Some resf, Some (n, rootf), Some t0, None)
    , TmConst (_, CSd (SArray y0)) ) ->
      sd_ fi
        (SIdaInitDense (Some tol, Some resf, Some (n, rootf), Some t0, Some y0))
  | ( SIdaInitDense
        (Some (rtol, atol), Some resf, Some (n, rootf), Some t0, Some y0)
    , TmConst (_, CSd (SArray y0')) ) ->
      let m = Matrix.dense (RealArray.length y0) in
      let v = Nvector_serial.wrap y0 in
      let v' = Nvector_serial.wrap y0' in
      let s =
        Ida.(
          init
            Dls.(solver (dense v m))
            (SStolerances (rtol, atol))
            resf ~roots:(n, rootf) t0 v v')
      in
      sd_ fi (SIdaSession s)
  | SIdaInitDense _, _ ->
      fail_extapp fi
  | SIdaInitDenseJac (None, None, None, None, None, None), TmRecord (_, r) ->
      let rtol, atol = get_tol fi r in
      sd_ fi
        (SIdaInitDenseJac (Some (rtol, atol), None, None, None, None, None))
  | SIdaInitDenseJac (Some tol, None, None, None, None, None), tm_jacf ->
      let jacf arg mm =
        match arg with
        | {Ida.jac_t= t; Ida.jac_coef= cj; Ida.jac_y= y; Ida.jac_y'= y'; _} ->
            let _ =
              eval env
                (List.fold_left (app_ NoInfo) tm_jacf
                   [ float_ NoInfo t
                   ; float_ NoInfo cj
                   ; sa_array_ NoInfo y
                   ; sa_array_ NoInfo y'
                   ; sa_matrix_dense_ NoInfo mm ])
            in
            ()
      in
      sd_ (tm_info tm_jacf)
        (SIdaInitDenseJac (Some tol, Some jacf, None, None, None, None))
  | SIdaInitDenseJac (Some tol, Some jacf, None, None, None, None), tm_resf ->
      sd_ (tm_info tm_resf)
        (SIdaInitDenseJac
           (Some tol, Some jacf, Some (mk_idafun tm_resf), None, None, None))
  | ( SIdaInitDenseJac (Some tol, Some jacf, Some resf, None, None, None)
    , TmRecord (_, r) ) ->
      let n, rootf = get_roots fi r in
      sd_ fi
        (SIdaInitDenseJac
           (Some tol, Some jacf, Some resf, Some (n, rootf), None, None))
  | ( SIdaInitDenseJac
        (Some tol, Some jacf, Some resf, Some (n, rootf), None, None)
    , TmConst (_, CFloat t0) ) ->
      sd_ fi
        (SIdaInitDenseJac
           (Some tol, Some jacf, Some resf, Some (n, rootf), Some t0, None))
  | ( SIdaInitDenseJac
        (Some tol, Some jacf, Some resf, Some (n, rootf), Some t0, None)
    , TmConst (fi, CSd (SArray y0)) ) ->
      sd_ fi
        (SIdaInitDenseJac
           (Some tol, Some jacf, Some resf, Some (n, rootf), Some t0, Some y0))
  | ( SIdaInitDenseJac
        ( Some (rtol, atol)
        , Some jacf
        , Some resf
        , Some (n, rootf)
        , Some t0
        , Some y0 )
    , TmConst (_, CSd (SArray y0')) ) ->
      let m = Matrix.dense (RealArray.length y0) in
      let v = Nvector_serial.wrap y0 in
      let v' = Nvector_serial.wrap y0' in
      let s =
        Ida.(
          init
            Dls.(solver ~jac:jacf (dense v m))
            ~roots:(n, rootf)
            (SStolerances (rtol, atol))
            resf t0 v v')
      in
      sd_ fi (SIdaSession s)
  | SIdaInitDenseJac _, _ ->
      fail_extapp fi
  | SIdaSolveNormal (None, None, None), TmConst (_, CSd (SIdaSession s)) ->
      sd_ fi (SIdaSolveNormal (Some s, None, None))
  | SIdaSolveNormal (Some s, None, None), TmConst (_, CFloat t) ->
      sd_ fi (SIdaSolveNormal (Some s, Some t, None))
  | SIdaSolveNormal (Some s, Some t, None), TmConst (_, CSd (SArray y)) ->
      sd_ fi (SIdaSolveNormal (Some s, Some t, Some (Nvector_serial.wrap y)))
  | SIdaSolveNormal (Some s, Some t, Some v), TmConst (_, CSd (SArray y')) ->
      let ret2int = function
        | Ida.Success ->
            0
        | Ida.RootsFound ->
            2
        | Ida.StopTimeReached ->
            1
      in
      let v' = Nvector_serial.wrap y' in
      let t', r = Ida.solve_normal s t v v' in
      tuple_ fi [float_ NoInfo t'; int_ NoInfo (ret2int r)]
  | SIdaSolveNormal _, _ ->
      fail_extapp fi
  | SIdaCalcICYY (None, None), TmConst (_, CSd (SIdaSession s)) ->
      sd_ fi (SIdaCalcICYY (Some s, None))
  | SIdaCalcICYY (Some s, None), TmConst (_, CSd (SArray y)) ->
      sd_ fi (SIdaCalcICYY (Some s, Some (Nvector_serial.wrap y)))
  | SIdaCalcICYY (Some s, Some v), TmConst (_, CFloat t) ->
      Ida.calc_ic_y s ~y:v t ; unit_ fi
  | SIdaCalcICYY _, _ ->
      fail_extapp fi
  | SIdaCalcICYYYP (None, None, None, None), TmConst (_, CSd (SIdaSession s))
    ->
      sd_ fi (SIdaCalcICYYYP (Some s, None, None, None))
  | SIdaCalcICYYYP (Some s, None, None, None), TmConst (_, CSd (SArray y)) ->
      sd_ fi
        (SIdaCalcICYYYP (Some s, Some (Nvector_serial.wrap y), None, None))
  | SIdaCalcICYYYP (Some s, Some y, None, None), TmConst (_, CSd (SArray y'))
    ->
      sd_ fi
        (SIdaCalcICYYYP (Some s, Some y, Some (Nvector_serial.wrap y'), None))
  | SIdaCalcICYYYP (Some s, Some y, Some y', None), TmConst (_, CSd (SArray v))
    ->
      sd_ fi
        (SIdaCalcICYYYP (Some s, Some y, Some y', Some (Nvector_serial.wrap v)))
  | SIdaCalcICYYYP (Some s, Some y, Some y', Some v), TmConst (_, CFloat t) ->
      Ida.calc_ic_ya_yd' s ~y ~y' ~varid:v t ;
      unit_ fi
  | SIdaCalcICYYYP _, _ ->
      fail_extapp fi
  | SIdaReinit (None, None, None), TmConst (_, CSd (SIdaSession s)) ->
      sd_ fi (SIdaReinit (Some s, None, None))
  | SIdaReinit (Some s, None, None), TmConst (_, CFloat t) ->
      sd_ fi (SIdaReinit (Some s, Some t, None))
  | SIdaReinit (Some s, Some t, None), TmConst (_, CSd (SArray y)) ->
      sd_ fi (SIdaReinit (Some s, Some t, Some (Nvector_serial.wrap y)))
  | SIdaReinit (Some s, Some t, Some v), TmConst (_, CSd (SArray y')) ->
      Ida.reinit s t v (Nvector_serial.wrap y') ;
      unit_ fi
  | SIdaReinit _, _ ->
      fail_extapp fi
  | SIdaGetDky (None, None, None), TmConst (_, CSd (SIdaSession s)) ->
      sd_ fi (SIdaGetDky (Some s, None, None))
  | SIdaGetDky (Some s, None, None), TmConst (_, CSd (SArray y)) ->
      sd_ fi (SIdaGetDky (Some s, Some (Nvector_serial.wrap y), None))
  | SIdaGetDky (Some s, Some y, None), TmConst (_, CFloat t) ->
      sd_ fi (SIdaGetDky (Some s, Some y, Some t))
  | SIdaGetDky (Some s, Some y, Some t), TmConst (_, CInt n) ->
      Ida.get_dky s y t n ; unit_ fi
  | SIdaGetDky _, _ ->
      fail_extapp fi
  | SIdaGetCurrentTime, TmConst (_, CSd (SIdaSession s)) ->
      float_ fi (Ida.get_current_time s)
  | SIdaGetCurrentTime, _ ->
      fail_extapp fi
  | SIdaGetLastStep, TmConst (_, CSd (SIdaSession s)) ->
      float_ fi (Ida.get_last_step s)
  | SIdaGetLastStep, _ ->
      fail_extapp fi
