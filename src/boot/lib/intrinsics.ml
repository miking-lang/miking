open Ustring.Op

module Mseq = struct
  type 'a t = 'a BatFingerTree.t

  let make n v = BatFingerTree.of_list (List.init n (fun _ -> v))

  let empty = BatFingerTree.empty

  let length = BatFingerTree.size

  let concat = BatFingerTree.append

  let get = BatFingerTree.get

  let set = BatFingerTree.set

  let cons e s = BatFingerTree.cons s e

  let snoc = BatFingerTree.snoc

  let reverse = BatFingerTree.reverse

  let split_at s n =
    if n == 0 then (empty, s) (* O(1) *)
    else if n == 1 then
      ( BatFingerTree.singleton (BatFingerTree.head_exn s)
      , BatFingerTree.tail_exn s ) (* Amortized O(1) *)
    else if n == length s - 1 then
      ( BatFingerTree.init_exn s
      , BatFingerTree.singleton (BatFingerTree.last_exn s) )
      (* Amortized O(1) *)
    else if n == length s then (s, empty) (* O(1) *)
    else BatFingerTree.split_at s n

  (* O(log n) *)

  module Helpers = struct
    let of_list = BatFingerTree.of_list

    let to_list = BatFingerTree.to_list

    let of_array a = of_list (Array.to_list a)

    let to_array s = Array.of_list (to_list s)

    let of_ustring u = of_list (ustring2list u)

    let to_ustring s = list2ustring (to_list s)

    let equal = BatFingerTree.equal

    let map = BatFingerTree.map

    let fold_right f s a = BatFingerTree.fold_right (fun a x -> f x a) a s

    let combine s1 s2 =
      let rec work a s1 s2 =
        if length s1 == 0 then a
        else
          work
            (snoc a (BatFingerTree.head_exn s1, BatFingerTree.head_exn s2))
            (BatFingerTree.tail_exn s1)
            (BatFingerTree.tail_exn s2)
      in
      if length s1 != length s2 then
        raise (Invalid_argument "sequences of different length")
      else work empty s1 s2

    let fold_right2 f s1 s2 a =
      fold_right (fun x a -> f (fst x) (snd x) a) (combine s1 s2) a
  end
end

module Symb = struct
  type t = int

  let symid = ref 0

  let gensym _ =
    symid := !symid + 1 ;
    !symid

  let eqsym l r = l = r

  let hash s = s

  module Helpers = struct
    let nosym = -1

    let ustring_of_sym = ustring_of_int

    let string_of_sym s = Ustring.to_utf8 (ustring_of_sym s)
  end
end

module File = struct
  let read f = f |> Ustring.to_utf8 |> Ustring.read_file

  let write f d = Ustring.write_file (Ustring.to_utf8 f) d

  let exists f = f |> Ustring.to_utf8 |> Sys.file_exists

  let delete f = f |> Ustring.to_utf8 |> Sys.remove
end
