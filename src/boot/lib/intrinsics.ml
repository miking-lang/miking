open Ustring.Op

module Mseq = struct
  type 'a t = 'a Rope.t

  let make n v = Rope.make n v

  let empty = Rope.empty

  let length = Rope.length

  let concat = Rope.concat

  let get = Rope.get

  let set = Rope.set

  let cons = Rope.cons

  let snoc = Rope.snoc

  let reverse = Rope.reverse

  let split_at = Rope.split_at

  module Helpers = struct
    let of_list = Rope.Convert.of_list

    let to_list = Rope.Convert.to_list

    let of_array = Rope.Convert.of_array

    let to_array = Rope.Convert.to_array

    let of_ustring = Rope.Convert.of_ustring

    let to_ustring = Rope.Convert.to_ustring

    let equal = Rope.equal

    let map = Rope.map

    let fold_right = Rope.foldr

    let combine = Rope.combine

    let fold_right2 = Rope.foldr2
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

module FloatConversion = struct
  let floorfi f = f |> Float.floor |> int_of_float

  let ceilfi f = f |> Float.ceil |> int_of_float

  let roundfi f = f |> Float.round |> int_of_float

  let string2float s = s |> Ustring.to_utf8 |> Float.of_string
end
