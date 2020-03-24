open Extast
open Ustring.Op
#ifdef SUNDIALS
open Sundials
#endif

let pprint = function
  | EApp _ -> us "eapp"
#ifdef SUNDIALS
  (* Elementary functions *)
  | Esin -> us "sin"
  | Ecos -> us "cos"
  (* SundialsML related functions *)
  | ESArray a ->
     let l = RealArray.to_list a in
     let l' = List.map (fun x -> us (Printf.sprintf "%f" x)) l in
     us"<|" ^. Ustring.concat (us",") l' ^. us"|>"
  | ESArrayCreate -> us"sArrCreate"
  | ESArrayGet _ -> us"sArrGet"
  | ESArraySet _ -> us"sArrSet"
  | ESMatrixDense _ -> us"SMatrixDense"
  | ESMatrixDenseSet _ -> us"sMatrixDenseSet"
  | ESArrayLength -> us "sArrLength"
  | EIdaSession _ -> us"idaSession"
  | EIdaInitDense _ -> us"idaInitDense"
  | EIdaInitDenseJac _ -> us"idaInitDenseJac"
  | EIdaSolveNormal _ -> us"idaSolveNormal"
  | EIdaCalcICYY _ -> us"idaCalcICYY"
#endif
