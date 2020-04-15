open Sundials

type 'a ext =
  | EApp of ('a -> 'a) option
  (* Elementary functions *)
  | Esin
  | Ecos
  (* SundialsML related functions *)
  | ESArray of RealArray.t
  | ESArrayMake of int option
  | ESArrayGet of RealArray.t option
  | ESArraySet of RealArray.t option * int option
  | ESArrayLength
  | ESMatrixDense of Matrix.Dense.t
  | ESMatrixDenseCreate of int option
  | ESMatrixDenseGet of Matrix.Dense.t option
                        * int option
  | ESMatrixDenseSet of Matrix.Dense.t option
                        * int option
                        * int option

  | EIdaSession of Nvector_serial.kind Ida.serial_session
  | EIdaInitDense of (float * float) option
                     * (float ->
                        RealArray.t ->
                        RealArray.t ->
                        RealArray.t ->
                        unit) option
                        * (int * (float ->
                                  RealArray.t ->
                                  RealArray.t ->
                                  RealArray.t ->
                                  unit)) option
                     * float option
                     * RealArray.t option

  | EIdaInitDenseJac of (float * float) option
                        * ((RealArray.t Ida.triple, RealArray.t)
                             Ida.jacobian_arg ->
                           Matrix.Dense.t ->
                           unit) option
                        * (float ->
                           RealArray.t ->
                           RealArray.t ->
                           RealArray.t ->
                           unit) option
                        * (int * (float ->
                                  RealArray.t ->
                                  RealArray.t ->
                                  RealArray.t ->
                                  unit)) option
                        * float option
                        * RealArray.t option

  | EIdaSolveNormal of Nvector_serial.kind Ida.serial_session option
                       * float option
                       * Nvector_serial.t option

  | EIdaCalcICYY of Nvector_serial.kind Ida.serial_session option
                    * Nvector_serial.t option

  | EIdaReinit of Nvector_serial.kind Ida.serial_session option
                  * float option
                  * Nvector_serial.t option

  | EIdaGetDky of Nvector_serial.kind Ida.serial_session option
                  * Nvector_serial.t option
                  * float option

  | EIdaGetCurrentTime
  | EIdaGetLastStep
