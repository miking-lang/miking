(*
   Modelyze II is licensed under the MIT license.  
   Copyright (C) David Broman. See file LICENSE.txt  
*)

(** Different utility functions that are missing in the standard library *)


module IntSet :
  sig
    type elt = int
    type t
    val empty : t
    val is_empty : t -> bool
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val singleton : elt -> t
    val remove : elt -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (elt -> unit) -> t -> unit
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val filter : (elt -> bool) -> t -> t
    val partition : (elt -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> elt list
    val min_elt : t -> elt
    val max_elt : t -> elt
    val choose : t -> elt
    val split : elt -> t -> t * bool * t
  end
(* General definition of an integer set. The implementation is using the
   standard [Set] module from OCaml standard library. This definition
   is generated using command 'ocamlc -i utils.ml' *)

type intset = IntSet.t

val last : 'a list -> 'a
(** Returns the last element in a list. Raises [Invalid_argument "Utils.last"]
    if the list is empty. *)

val findindex : 'a -> 'a list -> int
(** Function [findindex x l] returns the index for the first occurance of [x] in list [l]. Raises [Not_found] if [x] does not exist in [l]. *)


val find_associndex : 'a -> ('a * 'b) list -> ('b * int)
(** Expression [find_associndex x l] returns a tuple with value and index for
    the first occurance of [x] in the association list [l]. 
    Raises [Not_found] if [x] is not a key in [l].*)


val ( <| ) :  ('a -> 'b) -> 'a -> 'b
(** Pipe-backward operator *)

val ( >> ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
(** Forward composition operator *)

val map_option : ('a -> 'b) -> 'a option -> 'b option

val map2sc : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
(* Map2 short-ciruit *)


val filtermap : ('a -> 'b option) -> 'a list -> 'b list

val foldmap : ('a -> 'b -> 'a * 'c) -> 'a -> 'b list -> 'a * 'c list


val string_of_intlist : int list -> string
(** Converts a list of integers to a string, where the least 8 significant bits
    are used of each integer. *)

val intlist_of_string : string -> int list
(** Converts a string into a list of integers *)

val write_binfile : string -> string -> unit
(** Call [write_binfile n d] creates a binary file named [n] and stores 
    string data [d] in the file. Raises [Sys_error] if error creating or
    writing to file. *)

val read_binfile : string -> string
(** Call [read_binfile n] reads the binary file with filename [n] and
    returns the binary data as a string. Exception [Sys_error] is raised
    if the file cannot be found or cannot be read. *)

val fold_interval : ('a -> int -> 'a) -> 'a -> int -> int -> 'a
(** [fold_interval f a start end] folds an integer interval starting at 
   [start] and ending with [end]. For each number in the interval, function
   [f] is called. *) 

val genlist : (int -> 'a) -> int -> 'a list
(** Call [genlist f n] Generates a list with [n] elements, where expression [f i] 
    is the value of each element and [i] is the index in the list starting at 0. *)

val xor : bool -> bool -> bool

module Int :
sig
  type t = int
  val compare : t -> t -> int
end
(** Integer module with functions [compare] and type [t], which makes it easy to be
    passed as argument to functors [Set.Make] and [Map.Make]
*)


