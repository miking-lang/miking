open Extast
open Ustring.Op

let pprint = function
  | EApp _ -> us "eapp"
  (* Elementary functions *)
  | Esin -> us "sin"
  | Ecos -> us "cos"
  (* SundialsML related functions *)
  | ESArray a ->
     let l = Sundials.RealArray.to_list a in
     let l' = List.map (fun x -> us (Printf.sprintf "%f" x)) l in
     us"<|" ^. Ustring.concat (us",") l' ^. us"|>"
  | ESArrayCreate -> us"sArrCreate"
  | ESArrayGet _ -> us"sArrGet"
  | ESArraySet _ -> us"sArrSet"
  | ESArrayLength -> us "sArrLength"
  | EIdaSession _ -> us"idaSession"
  | EIdaInit _ -> us"idaInit"
  | EIdaSolveNormal _ -> us"idaSolveNormal"
  | EIdaCalcICYY _ -> us"idaCalcICYY"

