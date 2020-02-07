open Sundials

type 'a ext =
  | EApp of ('a -> 'a) option
  (* Elementary functions *)
  | Esin
  | Ecos
  (* SundialsML related functions *)
  | ESArray of RealArray.t
  | ESArrayCreate
  | ESArrayGet of RealArray.t option
  | ESArraySet of RealArray.t option * int option
  | ESArrayLength
  | EIdaSession of Nvector_serial.kind Ida.serial_session
  | EIdaInit of (float * float) option
                * (float ->
                   RealArray.t ->
                   RealArray.t ->
                   RealArray.t ->
                   unit) option
                * float option
                * RealArray.t option
  | EIdaSolveNormal of Nvector_serial.kind Ida.serial_session option
                       * float option
                       * Nvector_serial.t option

