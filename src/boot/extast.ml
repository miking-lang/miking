type ext =
  (* Elementary functions *)
  | Esin
  | Ecos
  (* SundialsML related functions *)
  | ESArray of Sundials.RealArray.t
  | ESArrayCreate
  | ESArrayGet of Sundials.RealArray.t option
  | ESArraySet of Sundials.RealArray.t option * int option
  | EIdaSession of Nvector_serial.kind
                     Ida.serial_session * Nvector_serial.t * Nvector_serial.t

  (* | EIdaInit of (float * float) option
   *               * (float ->
   *                  Sundials.RealArray.t ->
   *                  Sundials.RealArray.t ->
   *                  Sundials.RealArray.t ->
   *                  unit) option
   *               * float option
   *               * Sundials.RealArray.t option *)
