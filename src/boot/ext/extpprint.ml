open Extast
open Ustring.Op
open Sundials

let pprint = function
  | EApp _ -> us "eapp"
  (* Elementary functions *)
  | Esin -> us "sin"
  | Ecos -> us "cos"
  (* SundialsML related functions *)
  | ESArray a ->
     let l = RealArray.to_list a in
     let l' = List.map (fun x -> us (Printf.sprintf "%f" x)) l in
     us"<|" ^. Ustring.concat (us",") l' ^. us"|>"
  | ESArrayMake _ -> us"sArrMake"
  | ESArrayGet _ -> us"sArrGet"
  | ESArraySet _ -> us"sArrSet"
  | ESMatrixDense _ -> us"SMatrixDense"
  | ESMatrixDenseCreate _ -> us"sMatrixDenseCreate"
  | ESMatrixDenseGet _ -> us"sMatrixDenseGet"
  | ESMatrixDenseSet _ -> us"sMatrixDenseSet"
  | ESArrayLength -> us "sArrLength"
  | EIdaSession _ -> us"idaSession"
  | EIdaInitDense _ -> us"idaInitDense"
  | EIdaInitDenseJac _ -> us"idaInitDenseJac"
  | EIdaSolveNormal _ -> us"idaSolveNormal"
  | EIdaCalcICYY _ -> us"idaCalcICYY"
  | EIdaReinit _ -> us"idaReinit"
  | EIdaGetDky _ -> us"idaGetDky"
  | EIdaGetCurrentTime -> us"idaGetCurrentTime"
  | EIdaGetLastStep -> us"idaGetLastStep"
