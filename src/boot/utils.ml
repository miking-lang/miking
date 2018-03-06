
open Printf


module IntSet = Set.Make(
  struct
    let compare = Pervasives.compare
    type t = int
  end)

type intset = IntSet.t


(* Returns the last element *)
let rec last xs =
  match xs with
    | [] -> raise (Invalid_argument "Utils.last")
    | [x] -> x
    | x::xs -> last xs

let findindex x l =
  let rec findidx l c =
    match l with
      | [] -> raise Not_found
      | y::ys -> if x = y then c else findidx ys (c+1)
  in findidx l 0

let find_associndex x l =
  let rec findidx l c =
    match l with
      | [] -> raise Not_found
      | (y,v)::ys -> if x = y then (v,c) else findidx ys (c+1)
  in findidx l 0


let (<|) f x = f x

let (>>) f g x = g(f x)

let map_option f op =
  match op with
    | Some t -> Some (f t)
    | None -> None

let rec map2sc f l1 l2 =
  match l1,l2 with
    | [],_ -> []
    | _,[] -> []
    | (x::xs),(y::ys) -> (f x y)::(map2sc f xs ys)

let rec filtermap f ls =
  match ls with
    | x::xs -> (match f x with
		  | Some y -> y::(filtermap f xs)
		  | None -> filtermap f xs)
    | [] -> []

let foldmap f k ls =
  let rec work f k ls a =
    match ls with
      | x::xs ->
        let (k',x') = f k x in
          work f k' xs (x'::a)
      | [] -> (k,List.rev a)
  in work f k ls []


let rec option_split lst =
  match lst with
    | (Some x)::xs ->
	(match option_split xs with
	  | Some xs' -> Some (x::xs')
	  | None -> None)
    | (None)::xs -> None
    | [] -> Some []



let string_of_intlist il =
  let s = Bytes.create (List.length il) in
  il |> List.fold_left (fun i x -> (Bytes.set s i (char_of_int x)); i+1) 0 |> ignore;
  Bytes.to_string s

let intlist_of_string s =
  let rec work n a = if n >= 0
    then work (n-1) ((int_of_char (s.[n]))::a) else a in
  work (String.length s) []

let write_binfile filename str =
  let f = open_out_bin filename in
  output_bytes f str;
  flush f;
  close_out f

let read_binfile filename =
  let f = open_in_bin filename in
  let size = in_channel_length f in
  let s = Bytes.create size in
  try
    let rec readinput pos size =
      let read = input f s pos size in
      if read != 0 then readinput (pos+read) (size-read) else ()
    in
    readinput 0 size;
    close_in f;
    s
  with
  | Invalid_argument _ -> raise (Sys_error "Cannot read file")


let rec fold_interval f a s e =
  if s = e then (f a s) else fold_interval f (f a s) (s+1) e



let genlist f n =
  let rec work i a =
    if i >= 0 then work (i-1) ((f (i-1))::a) else a
  in work n []

let xor b1 b2 = (b1 || b2) && (not (b1 && b2))

let sign_extension v n =
  if ((v lsr (n-1)) land 1) = 0 then v else (-1 lsl n) lor v



module Int =
struct
  type t = int
  let compare = compare
end
