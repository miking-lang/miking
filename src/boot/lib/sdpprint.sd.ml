open Sdast
open Ustring.Op
open Sundials

let pprint = function
  (* SundialsML related functions *)
  | SArray a ->
    let l = RealArray.to_list a in
    let l' = List.map (fun x -> us (Printf.sprintf "%f" x)) l in
    us"<|" ^. Ustring.concat (us",") l' ^. us"|>"
  | SArrayMake _ -> us"sArrMake"
  | SArrayGet _ -> us"sArrGet"
  | SArraySet _ -> us"sArrSet"
  | SMatrixDense _ -> us"SMatrixDense"
  | SMatrixDenseCreate _ -> us"sMatrixDenseCreate"
  | SMatrixDenseGet _ -> us"sMatrixDenseGet"
  | SMatrixDenseSet _ -> us"sMatrixDenseSet"
  | SArrayLength -> us "sArrLength"
  | SIdaSession _ -> us"idaSession"
  | SIdaInitDense _ -> us"idaInitDense"
  | SIdaInitDenseJac _ -> us"idaInitDenseJac"
  | SIdaSolveNormal _ -> us"idaSolveNormal"
  | SIdaCalcICYY _ -> us"idaCalcICYY"
  | SIdaCalcICYYYP _ -> us"idaCalcICYYYP"
  | SIdaReinit _ -> us"idaReinit"
  | SIdaGetDky _ -> us"idaGetDky"
  | SIdaGetCurrentTime -> us"idaGetCurrentTime"
  | SIdaGetLastStep -> us"idaGetLastStep"
