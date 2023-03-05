open Ustring.Op

(* The functions in this module have their time-complexity in their
 * documentation. Many depend on the complexity of some underlying operation in
 * OCaml, which does not have a documented complexity. In these cases we assume
 * what it *should* be, and note that it is undocumented using (?).
 *
 * Note that the rope complexities assume the normal array representation, not
 * the bigarray representation.
 *
 * For the rope operations, we additionally document whether they flatten the
 * rope. The height of a flattened rope is 1. There are two possibilities:
 * - The input is left as is and the output is a flat rope, which we write as
 *   "output is flat".
 * - The input is flattened, and the output rope (if any) is flat, which we
 *   write as "flattens".
 *)
module Mseq : sig
  type 'a t = List of 'a List.t | Rope of 'a Rope.t

  (* Defaults to create_rope, see its documentation. *)
  val create : int -> (int -> 'a) -> 'a t

  (* Complexity (?): O(n*k) where n is the first argument and k is the
   * complexity of f. *)
  val create_rope : int -> (int -> 'a) -> 'a t

  (* Complexity (?): O(n*k) where n is the first argument and k is the
   * complexity of f. *)
  val create_list : int -> (int -> 'a) -> 'a t

  (* Complexity: O(1) *)
  val is_rope : 'a t -> bool

  (* Complexity: O(1) *)
  val is_list : 'a t -> bool

  (* Defaults to empty_rope, see its documentation. *)
  val empty : 'a t

  (* Complexity: O(1) *)
  val empty_rope : 'a t

  (* Complexity: O(1) *)
  val empty_list : 'a t

  (* Complexity:
   * rope (?): O(1) assuming OCaml's Array.length is O(1)
   * list (?): O(n), where n is the length of the sequence
   *)
  val length : 'a t -> int

  (* Complexity:
   * rope (?): O(1) assuming OCaml's Array.length is O(1)
   * list (?): O(i), where i is the provided length to compare with
   *)
  val is_length_at_least : 'a t -> int -> bool

  (* Complexity:
   * rope (?): O(1) assuming OCaml's Array.length is O(1)
   * list (?): O(n), where n is the length of the first argument
   *)
  val concat : 'a t -> 'a t -> 'a t

  (* Complexity:
   * rope (?): O(h), where h is the height of the rope (worst case is linear in
   *   the length of the sequence)
   * list (?): O(m), where m is the int
   *)
  val get : 'a t -> int -> 'a

  (* Complexity:
   * rope (?): O(n), where n is the length of the sequence
   * list (?): O(m), where m is the int
   *)
  val set : 'a t -> int -> 'a -> 'a t

  (* Complexity:
   * rope (?): O(1)
   * list: O(1)
   *)
  val cons : 'a -> 'a t -> 'a t

  (* Complexity:
   * rope (?): O(1)
   * list (?): O(n), where n is the length of the sequence
   *)
  val snoc : 'a t -> 'a -> 'a t

  (* Complexity:
   * rope (?): O(n), where n is the length of the sequence (flattens)
   * list (?): O(n), where n is the length of the sequence
   *)
  val reverse : 'a t -> 'a t

  (* Complexity:
   * rope (?): O(h), see `get`
   * list: O(1)
   *)
  val head : 'a t -> 'a

  (* Complexity:
   * rope (?): O(1), if rope is flat, otherwise O(n) (flattens)
   * list: O(1)
   *)
  val tail : 'a t -> 'a t

  (* Complexity:
   * rope (?): O(1)
   * list: O(1)
   *)
  val null : 'a t -> bool

  (* Complexity:
   * rope (?): O(n*k), where n is the length of the sequence and k is the
   *   complexity of the function
   * list: O(n*k), where n is the length of the sequence and k is the complexity
   *   of the function
   *)
  val iter : ('a -> unit) -> 'a t -> unit

  (* Complexity:
   * rope (?): O(n*k), where n is the length of the sequence and k is the
   *   complexity of the function
   * list: O(n*k), where n is the length of the sequence and k is the complexity
   *   of the function
   *)
  val iteri : (int -> 'a -> unit) -> 'a t -> unit

  (* Complexity:
   * rope (?): O(1), if the rope is flat, otherwise O(n) (flattens)
   * list (?): O(m), where m is the int
   *)
  val split_at : 'a t -> int -> 'a t * 'a t

  (* Complexity:
   * rope (?): O(1), if the rope is flat, otherwise O(n) (flattens)
   * list (?): O(k + m), where k and m are the int inputs
   *)
  val subsequence : 'a t -> int -> int -> 'a t

  (* Complexity:
   * rope (?): O(n*k), where n is the length of the sequence, k is the
   *   complexity of the function (flattens)
   * list (?): O(n*k), where n is the length of the sequence, k is the
   *   complexity of the function
   *)
  val map : ('a -> 'b) -> 'a t -> 'b t

  (* Complexity:
   * rope (?): O(n*k), where n is the length of the sequence, k is the
   *   complexity of the function (flattens)
   * list (?): O(n*k), where n is the length of the sequence, k is the
   *   complexity of the function
   *)
  val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t

  module Helpers : sig
    val to_seq : 'a t -> 'a Seq.t

    val of_list : 'a list -> 'a t

    val of_list_list : 'a list -> 'a t

    val of_list_rope : 'a list -> 'a t

    val to_list : 'a t -> 'a list

    val of_array : 'a array -> 'a t

    val of_array_copy : 'a array -> 'a t

    val of_array_list : 'a array -> 'a t

    val of_array_rope : 'a array -> 'a t

    val to_array : 'a t -> 'a array

    val to_array_copy : 'a t -> 'a array

    val of_ustring : ustring -> int t

    val of_ustring_rope : ustring -> int t

    val of_ustring_list : ustring -> int t

    val to_ustring : int t -> ustring

    val to_utf8 : int t -> string

    val of_utf8 : string -> int t

    (* Complexity:
     * rope (?): O(n*k), where n is the length of the sequence, k is the
     *   complexity of the function (flattens)
     * list (?): O(n*k), where n is the length of the sequence, k is the
     *   complexity of the function
     *)
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

    (* Complexity:
     * rope (?): O(n*k), where n is the length of the sequence, k is the
     *   complexity of the function (flattens)
     * list (?): O(n*k), where n is the length of the sequence, k is the
     *   complexity of the function
     *)
    val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc

    (* Complexity:
     * rope (?): O(n*k), where n is the length of the sequence, k is the
     *   complexity of the function (flattens)
     * list (?): O(n*k), where n is the length of the sequence, k is the
     *    complexity of the function
     *)
    val fold_right : ('a -> 'acc -> 'acc) -> 'acc -> 'a t -> 'acc

    (* Crashes if the two input sequences have different lengths.
     * Complexity:
     * rope (?): O(n), where n is the length of the sequences (flattens)
     * list (?): O(n), where n is the length of the sequences
     *)
    val combine : 'a t -> 'b t -> ('a * 'b) t

    (* Crashes if the two input sequences have different lengths.
     * Complexity:
     * rope (?): O(n*k), where n is the length of the sequence, k is the
     *   complexity of the function (flattens)
     * list (?): O(n*k), where n is the length of the sequence, k is the
     *   complexity of the function
     *)
    val fold_right2 :
      ('a -> 'b -> 'acc -> 'acc) -> 'a t -> 'b t -> 'acc -> 'acc

    (* Complexity:
     * rope (?): O(n*k), where n is the length of the sequence, k is the
     *   complexity of the function (flattens)
     * list (?): O(n*k), where n is the length of the sequence, k is the
     *   complexity of the function
     *)
    val map_accum_left :
      ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a t -> 'acc * 'b t
  end
end

module T : sig
  open Bigarray

  type 'a t =
    | TBootInt of (int, int_elt) Tensor.Barray.t
    | TBootFloat of (float, float64_elt) Tensor.Barray.t
    | TBootGen of ('a, 'a) Tensor.Generic.t

  type ('a, 'b) u =
    | TInt : (int, int_elt) Tensor.Barray.t -> (int, int_elt) u
    | TFloat : (float, float64_elt) Tensor.Barray.t -> (float, float64_elt) u
    | TGen : ('a, 'b) Tensor.Generic.t -> ('a, 'b) u

  module type OP_MSEQ = sig
    type ('a, 'b) t

    val get_exn : ('a, 'b) t -> int Mseq.t -> 'a

    val set_exn : ('a, 'b) t -> int Mseq.t -> 'a -> unit

    val linear_get_exn : ('a, 'b) t -> int -> 'a

    val linear_set_exn : ('a, 'b) t -> int -> 'a -> unit

    val shape : ('a, 'b) t -> int Mseq.t

    val reshape_exn : ('a, 'b) t -> int Mseq.t -> ('a, 'b) t

    val slice_exn : ('a, 'b) t -> int Mseq.t -> ('a, 'b) t
  end

  module Op_mseq_generic :
    OP_MSEQ with type ('a, 'b) t = ('a, 'b) Tensor.Generic.t

  module Op_mseq_barray :
    OP_MSEQ with type ('a, 'b) t = ('a, 'b) Tensor.Barray.t

  val uninit_int : int Mseq.t -> (int, int_elt) Tensor.Barray.t

  val uninit_float : int Mseq.t -> (float, float64_elt) Tensor.Barray.t

  val create_int :
    int Mseq.t -> (int Mseq.t -> int) -> (int, int_elt) Tensor.Barray.t

  val create_float :
    int Mseq.t -> (int Mseq.t -> float) -> (float, float64_elt) Tensor.Barray.t

  val create_generic :
    int Mseq.t -> (int Mseq.t -> 'a) -> ('a, 'a) Tensor.Generic.t

  val uninit_int_packed : int Mseq.t -> (int, int_elt) u

  val uninit_float_packed : int Mseq.t -> (float, float64_elt) u

  val create_int_packed : int Mseq.t -> (int Mseq.t -> int) -> (int, int_elt) u

  val create_float_packed :
    int Mseq.t -> (int Mseq.t -> float) -> (float, float64_elt) u

  val create_generic_packed : int Mseq.t -> (int Mseq.t -> 'a) -> ('a, 'b) u

  val get_exn : ('a, 'b) u -> int Mseq.t -> 'a

  val set_exn : ('a, 'b) u -> int Mseq.t -> 'a -> unit

  val linear_get_exn : ('a, 'b) u -> int -> 'a

  val linear_set_exn : ('a, 'b) u -> int -> 'a -> unit

  val shape : ('a, 'b) u -> int Mseq.t

  val reshape_exn : ('a, 'b) u -> int Mseq.t -> ('a, 'b) u

  val slice_exn : ('a, 'b) u -> int Mseq.t -> ('a, 'b) u

  val sub_exn : ('a, 'b) u -> int -> int -> ('a, 'b) u

  val copy : ('a, 'b) u -> ('a, 'b) u

  val transpose_exn : ('a, 'b) u -> int -> int -> ('a, 'b) u

  val iter_slice : (int -> ('a, 'b) u -> unit) -> ('a, 'b) u -> unit

  val rank : ('a, 'b) u -> int

  val equal : ('a -> 'b -> bool) -> ('a, 'c) u -> ('b, 'd) u -> bool

  val to_string : ('a -> int Mseq.t) -> ('a, 'b) u -> int Mseq.t

  module Helpers : sig
    val to_genarray_clayout : ('a, 'b) u -> ('a, 'b, c_layout) Genarray.t

    val to_array1_clayout : ('a, 'b) u -> ('a, 'b, c_layout) Array1.t

    val to_array2_clayout : ('a, 'b) u -> ('a, 'b, c_layout) Array2.t

    val of_genarray_clayout : ('a, 'b, c_layout) Genarray.t -> ('a, 'b) u

    val of_array1_clayout : ('a, 'b, c_layout) Array1.t -> ('a, 'b) u

    val of_array2_clayout : ('a, 'b, c_layout) Array2.t -> ('a, 'b) u
  end
end

module Symb : sig
  type t

  val gensym : unit -> t

  val eqsym : t -> t -> bool

  val hash : t -> int

  val compare : t -> t -> int

  module Helpers : sig
    val nosym : t

    val ustring_of_sym : t -> ustring

    val string_of_sym : t -> string
  end
end

module File : sig
  val read : int Mseq.t -> int Mseq.t

  val write : int Mseq.t -> int Mseq.t -> unit

  val exists : int Mseq.t -> bool

  val delete : int Mseq.t -> unit
end

module FloatConversion : sig
  val floorfi : float -> int

  val ceilfi : float -> int

  val roundfi : float -> int

  val string_is_float : int Mseq.t -> bool

  val string2float : int Mseq.t -> float

  val float2string : float -> int Mseq.t
end

module IO : sig
  val print : int Mseq.t -> unit

  val print_error : int Mseq.t -> unit

  val dprint : 'a -> unit

  val flush_stdout : unit -> unit

  val flush_stderr : unit -> unit

  val read_line : unit -> int Mseq.t
end

module RNG : sig
  val set_seed : int -> unit

  val int_u : int -> int -> int
end

module MSys : sig
  val exit : int -> unit

  val error : int Mseq.t -> exn

  val argv : int Mseq.t Mseq.t

  val command : int Mseq.t -> int
end

module Time : sig
  val get_wall_time_ms : unit -> float

  val sleep_ms : int -> unit
end

module ConTag : sig
  val constructor_tag : Obj.t -> int
end
