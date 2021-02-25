open Ustring.Op

module Mseq = struct
  type 'a t = 'a array Rope.t

  let create = Rope.create_array

  let empty = Rope.empty_array

  let length = Rope.length_array

  let concat = Rope.concat_array

  let get = Rope.get_array

  let set = Rope.set_array

  let cons = Rope.cons_array

  let snoc = Rope.snoc_array

  let reverse = Rope.reverse_array

  let split_at = Rope.split_at_array

  let subsequence = Rope.sub_array

  module Helpers = struct
    let of_list = Rope.Convert.of_list_array

    let to_list = Rope.Convert.to_list_array

    let of_array = Rope.Convert.of_array_array

    let to_array = Rope.Convert.to_array_array

    let of_ustring = Rope.Convert.of_ustring_array

    let to_ustring = Rope.Convert.to_ustring_array

    let equal = Rope.equal_array

    let map = Rope.map_array_array

    let fold_right = Rope.foldr_array

    let combine = Rope.combine_array_array

    let fold_right2 = Rope.foldr2_array
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
