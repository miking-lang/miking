open Sundials

type ext =
  (* SundialsML related functions *)
  | SArray of RealArray.t
  | SArrayMake of int option
  | SArrayGet of RealArray.t option
  | SArraySet of RealArray.t option * int option
  | SArrayLength
  | SMatrixDense of Matrix.Dense.t
  | SMatrixDenseCreate of int option
  | SMatrixDenseGet of Matrix.Dense.t option * int option
  | SMatrixDenseSet of Matrix.Dense.t option * int option * int option
  | SIdaSession of Nvector_serial.kind Ida.serial_session
  | SIdaInitDense of
      (float * float) option
      * (float -> RealArray.t -> RealArray.t -> RealArray.t -> unit) option
      * (int * (float -> RealArray.t -> RealArray.t -> RealArray.t -> unit))
        option
      * float option
      * RealArray.t option
  | SIdaInitDenseJac of
      (float * float) option
      * (   (RealArray.t Ida.triple, RealArray.t) Ida.jacobian_arg
         -> Matrix.Dense.t
         -> unit)
        option
      * (float -> RealArray.t -> RealArray.t -> RealArray.t -> unit) option
      * (int * (float -> RealArray.t -> RealArray.t -> RealArray.t -> unit))
        option
      * float option
      * RealArray.t option
  | SIdaSolveNormal of
      Nvector_serial.kind Ida.serial_session option
      * float option
      * Nvector_serial.t option
  | SIdaCalcICYY of
      Nvector_serial.kind Ida.serial_session option * Nvector_serial.t option
  | SIdaCalcICYYYP of
      Nvector_serial.kind Ida.serial_session option
      * Nvector_serial.t option
      * Nvector_serial.t option
      * Nvector_serial.t option
  | SIdaReinit of
      Nvector_serial.kind Ida.serial_session option
      * float option
      * Nvector_serial.t option
  | SIdaGetDky of
      Nvector_serial.kind Ida.serial_session option
      * Nvector_serial.t option
      * float option
  | SIdaGetCurrentTime
  | SIdaGetLastStep
