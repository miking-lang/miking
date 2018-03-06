(*
Copyright (c) 2010, David Broman
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice,
      this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the Linköping University nor the names of its
      contributors may be used to endorse or promote products derived from
      this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

type uchar = int
type len = int
type pos = int
type tree =
  | Uchars of uchar array
  | Branch of tree * tree
type encoding =
    Ascii | Latin1 | Utf8 | Utf16le | Utf16be | Utf32le | Utf32be | Auto

exception Decode_error of (encoding * int)
exception Unknown_sid



let space_char = 0x20


(*
  Comments state which test case the differnet functions are tested in.
  ST = successful test, ET=Exception test, i.e., when the funtion raise
  an exception
*)



let valid_uchar c = c >= 0 && c <= 0x1FFFFF

(* Internal function for generate one uchar out of a tree *)
let collapse t =
  let rec make_list us ls =
      match us with
	| Uchars(a) -> a::ls
        | Branch(t1,t2) -> make_list t1 (make_list t2 ls)
  in
    Array.concat (make_list t [])

(* If necessary, collapse a ustring and update the reference *)
let collapse_ustring s =
    match !s with
      | Uchars(a) -> a
      | Branch(_,_) as t ->
	  let a = collapse t in
	  s := Uchars(collapse t);
	  a


(* Create a new string where "\x0D\x0A" or "\x0D" are replaced with '\x0A'.
   A with the new string and the size is returned. *)
let normalize_newlines s =
  let len = String.length s in
  let s2 = Bytes.create len in
  let rec worker i n prev_x0d =
    if i < len then begin
      let c = s.[i] in
	if c = '\x0D' then (Bytes.set s2 n '\x0A'; worker (i+1) (n+1) true)
	else if c = '\x0A' && prev_x0d then worker (i+1) n false
	else (Bytes.set s2 n c; worker (i+1) (n+1) false)
    end else n
  in let n = worker 0 0 false in (Bytes.to_string s2,n)


(* Internal and can be used if we shall convert a UTF-8 stream later on.
   Returns a tuple with the size in bytes of the encoded string (source string)
   and an array with the uchars. *)
let from_utf8_worker s slen fail =
  (* Due to peformance requirements, we do not use the validate function.*)
  let rec calc_size_from_utf8 s i c =
    if i < slen then
      begin
	if ((int_of_char s.[i]) land 0b10000000) = 0 then
	  calc_size_from_utf8 s (i+1) (c+1)
	else if ((int_of_char s.[i]) land 0b11100000) = 0b11000000 then
          calc_size_from_utf8 s (i+2) (c+1)
	else if ((int_of_char s.[i]) land 0b11110000) = 0b11100000 then
          calc_size_from_utf8 s (i+3) (c+1)
	else if ((int_of_char s.[i]) land 0b11111000) = 0b11110000 then
          calc_size_from_utf8 s (i+4) (c+1)
	else
	  fail()
      end
    else if i > slen then c-1 else c
  in
  let alen = calc_size_from_utf8 s 0 0 in
  let a = (Array.make alen 0)  in
  let rec convert i j =
    if j >= alen then i
    else begin
      let s1 = int_of_char s.[i] in
	if s1 land 0b10000000 = 0 then begin
	  a.(j) <- s1; convert (i+1) (j+1)
        end else if (s1 land 0b11100000) = 0b11000000 then begin
	  let s2 = int_of_char s.[i+1] in
	  if (s2 land 0b11000000 <> 0b10000000) then fail() else
	  let c = ((s1 land 0b11111) lsl 6) lor (s2 land 0b111111) in
          if c <= 0b1111111 then fail()
          else (a.(j) <- c; convert (i+2) (j+1))
        end else if (s1 land 0b11110000) = 0b11100000 then begin
	  let s2 = int_of_char s.[i+1] in
	  let s3 = int_of_char s.[i+2] in
	  if (s2 land 0b11000000 <> 0b10000000) ||
	     (s3 land 0b11000000 <> 0b10000000) then fail() else
	  let c = ((s1 land 0b1111) lsl 12) lor ((s2 land 0b111111) lsl 6) lor
	    (s3 land 0b111111) in
          if c <= 0b11111111111 then fail()
          else (a.(j) <- c; convert (i+3) (j+1))
        end else if (s1 land 0b11111000) = 0b11110000 then begin
	  let s2 = int_of_char s.[i+1] in
	  let s3 = int_of_char s.[i+2] in
	  let s4 = int_of_char s.[i+3] in
	  if (s2 land 0b11000000 <> 0b10000000) ||
	     (s3 land 0b11000000 <> 0b10000000) ||
	     (s4 land 0b11000000 <> 0b10000000) then fail() else
	  let c = ((s1 land 0b111) lsl 18) lor ((s2 land 0b111111) lsl 12) lor
	    ((s3 land 0b111111) lsl 6) lor (s4 land 0b111111) in
          if c <= 0b1111111111111111 then fail()
          else (a.(j) <- c; convert (i+4) (j+1))
        end else fail();
    end
  in
  let i = convert 0 0 in (i,a)

let rec to_latin1 s =
  match !s with
    | Uchars(a) -> begin
	let len = Array.length a in
	let sout = Bytes.create len in
	  try
	    for i = 0 to len-1 do Bytes.set sout i (char_of_int (a.(i))) done;
	    Bytes.to_string sout
	  with
	      Invalid_argument _ -> raise (Invalid_argument "Ustring.to_latin1")
      end
    | Branch(s1,s2) as t -> s := Uchars(collapse t); to_latin1 s


let from_uchars a =
  Array.iter (fun c -> if not (valid_uchar c) then
		         raise (Invalid_argument "Ustring.from_uchars")
		       else ()) a; ref (Uchars(a))

(*   Note: Function should not throw an exception, since only well defined
         unicode characters are available internally. *)
let rec to_utf8 s =
  let rec calc_size_to_utf8 a = Array.fold_left
    (fun n ae->
       if ae <= 0b1111111 then n+1
       else if ae <= 0b11111111111 then n+2
       else if ae <= 0b1111111111111111 then n+3
       else n+4) 0 a
  in
  match !s with
    | Uchars(a) ->
        let ilen = Array.length a in
	let olen = calc_size_to_utf8 a in
	let sout = Bytes.create olen in
	let rec convert i j =
	  if i >= ilen then () else begin
	    let ai = a.(i) in
	    if ai <= 0b1111111 then begin
              Bytes.set sout j (char_of_int ai);
	      convert (i+1) (j+1)
	    end else if ai <= 0b11111111111 then begin
	      Bytes.set sout j (char_of_int ((ai lsr 6) lor 0b11000000));
	      Bytes.set sout (j+1) (char_of_int ((ai land 0b111111)
					 lor 0b10000000));

	      convert (i+1) (j+2)
	    end else if ai <= 0b1111111111111111 then begin
	      Bytes.set sout j (char_of_int ((ai lsr 12) lor 0b11100000));
	      Bytes.set sout (j+1) (char_of_int (((ai lsr 6) land 0b111111)
					 lor 0b10000000));
	      Bytes.set sout (j+2) (char_of_int ((ai land 0b111111) lor 0b10000000));
	      convert (i+1) (j+3)
	    end else begin
	      Bytes.set sout j  (char_of_int ((ai lsr 18) lor 0b11110000));
	      Bytes.set sout (j+1) (char_of_int (((ai lsr 12) land 0b111111)
					 lor 0b10000000));
	      Bytes.set sout (j+2) (char_of_int (((ai lsr 6) land 0b111111)
					 lor 0b10000000));
	      Bytes.set sout (j+3) (char_of_int ((ai land 0b111111)
					 lor 0b10000000));
	      convert (i+1) (j+4)
	    end
	  end
	in
	  convert 0 0; Bytes.to_string sout
    | Branch(s1,s2) as t -> s := Uchars(collapse t); to_utf8 s



(**** Op module  **********************************************************)

module Op =
struct

  type ustring = tree ref

  type sid = int

  module SidSet = Set.Make(
    struct
      let compare = Pervasives.compare
      type t = sid
    end)

  type sidset = SidSet.t


  let (^.) s1 s2 = ref (Branch(!s1,!s2))

  let (^..) s1 s2 =
    let s1 = collapse_ustring s1 in
    let s2 = collapse_ustring s2 in
    ref (Uchars(Array.append s1 s2))

  let (=.) s1 s2 =
    let s1 = collapse_ustring s1 in
    let s2 = collapse_ustring s2 in
    s1 = s2

  let (<>.) s1 s2 = not (s1 =. s2)


  let us s =
    let (s2,len2) = normalize_newlines s in
    ref (Uchars(Array.init len2 (fun i -> int_of_char (String.get s2 i))))

  let uc c = int_of_char (if c = '\x0D' then '\x0A' else c)

  module OrderedUString =
    struct
    type t = ustring
    let equal x y =  x =. y
    let hash t = Hashtbl.hash (collapse_ustring t)
  end
  module USHashtbl = Hashtbl.Make(OrderedUString)

  let symtab1  = USHashtbl.create 1024
  let (symtab2 : (int,ustring) Hashtbl.t) = Hashtbl.create 1024
  let idcount = ref 0
  let empty = 0

  let sid_of_ustring s =
  try USHashtbl.find symtab1 s
  with
      Not_found ->
	incr idcount;
	USHashtbl.add symtab1 s !idcount;
	Hashtbl.add symtab2 !idcount s;
	!idcount

  let ustring_of_sid i = Hashtbl.find symtab2 i

  let usid s = sid_of_ustring (us s)

  let ustring_of_bool b = if b then us"true" else us"false"

  let bool_of_ustring s =
    if s =. us"true" then true
    else if s =. us"false" then false
    else raise (Invalid_argument "bool_of_ustring")

  let ustring_of_int i = us (string_of_int i)

  let int_of_ustring s =
    try int_of_string (to_latin1 s)
    with _ -> raise (Failure "int_of_ustring")

  let ustring_of_float f = us (string_of_float f)

  let float_of_ustring s =
    try float_of_string (to_latin1 s)
    with _ -> raise (Failure "int_of_ustring")

  let uprint_char c = print_string (to_utf8 (from_uchars [|c|]))

  let uprint_string s = print_string (to_utf8 s)

  let uprint_int i = print_int i

  let uprint_float f = print_float f

  let uprint_endline s = print_endline (to_utf8 s)

  let uprint_newline() = print_newline()

  let list2ustring lst = ref (Uchars(Array.of_list lst))

  let ustring2list s = Array.to_list (collapse !s)

  let uprint_bool b = print_string (if b then "true" else "false")

end

type ustring = Op.ustring
type t = Op.ustring

let compare s1 s2 =
  let s1 = collapse_ustring s1 in
  let s2 = collapse_ustring s2 in
  compare s1 s2

let equal s1 s2 = Op.( =. ) s1 s2

let not_equal s1 s2 = Op.( <>. ) s1 s2

let hash t = Hashtbl.hash (collapse_ustring t)



let rec length s =
  match !s with
    | Uchars(a) -> Array.length a
    | Branch(_,_) as t -> s := Uchars(collapse t); length s

let rec get s n =
  match !s with
    | Uchars(a) ->
	(try Array.get a n
         with Invalid_argument _ -> raise (Invalid_argument "Ustring.get"))
    | Branch(_,_) as t -> s := Uchars(collapse t); get s n

let rec set s n c =
  match !s with
    | Uchars(a) ->
	(try Array.set a n c
         with Invalid_argument _ -> raise (Invalid_argument "Ustring.set"))
    | Branch(_,_) as t -> s := Uchars(collapse t); set s n c


let make n c = ref (Uchars (Array.make n c))

let create n = make n (Op.uc ' ')

let copy s = ref (Uchars(collapse_ustring s))

let sub s start len =
  let s2 = collapse_ustring s in
  try
    ref (Uchars(Array.sub s2 start len))
  with
      Invalid_argument _ -> raise (Invalid_argument "Ustring.sub")

let rec rindex_from_internal s i c =
  try
    if s.(i) = c then i
    else if i = 0 then raise Not_found else rindex_from_internal s (i-1) c
  with Invalid_argument _ -> raise (Invalid_argument "Ustring.rindex_from")


let rindex_from s i c =
  let s2 = (collapse_ustring s) in
  if Array.length s2 = 0 then raise Not_found
  else rindex_from_internal (collapse_ustring s) i c

let rindex s c = rindex_from s (length s - 1) c


let fast_append s1 s2 = Op.( ^.) s1 s2

let fast_concat sep sl =
  let rec worker sl ack first =
    match sl with
      | [] -> ack
      | s::ss -> if first then worker ss s false
	         else worker ss (Op.(^.) (Op.(^.) ack sep) s) false
  in worker sl (Op.us"") true

let concat sep sl = copy (fast_concat sep sl)

let count s c =
  let s2 = collapse_ustring s in
  Array.fold_left (fun a b -> if b = c then a + 1 else a) 0 s2

(* Internal *)
let find_trim_left s =
  let len = Array.length s in
  let rec worker i =
    if i >= len then i
    else if s.(i) > space_char then i else worker (i+1)
  in worker 0

(* Internal *)
let find_trim_right s =
  let rec worker i =
    if i = 0 then i
    else if s.(i-1) > space_char then i else worker (i-1)
  in worker (Array.length s)

let trim_left s =
  let s2 = collapse_ustring s in
  let left = find_trim_left s2 in
  let len = (Array.length s2) - left in
  ref (Uchars (Array.sub s2 left len))

let trim_right s =
  let s2 = collapse_ustring s in
  let left = 0 in
  let len = find_trim_right s2 in
  ref (Uchars (Array.sub s2 left len))

let trim s =
  let s2 = collapse_ustring s in
  let left = find_trim_left s2 in
  let len = (find_trim_right s2) - left in
  if len <= 0 then ref (Uchars [||])
  else ref (Uchars (Array.sub s2 left len))


let empty() = ref (Uchars [||])

let split s c =
  let s2 = collapse_ustring s in
  let c2 = collapse_ustring c in
  let len = Array.length s2 in
  let len_c2 = Array.length c2 in
  let rec has_char ch i =
    if i < len_c2 then
      if c2.(i) = ch then true else has_char ch (i+1)
    else false
  in
  let rec worker last i acc =
    if i < len then
      if has_char (s2.(i)) 0 then
        worker (i+1) (i+1) ((ref (Uchars (Array.sub s2 last (i-last))))::acc)
      else
        worker last (i+1) acc
    else
        ((ref (Uchars (Array.sub s2 last (i-last))))::acc)
  in
    if len = 0 then [] else List.rev (worker 0 0 [])

let starts_with s2 s1 =
  try equal (sub s1 0 (length s2)) s2 with _ -> false

let ends_with s2 s1 =
  try equal (sub s1 (length s1 - length s2) (length s2)) s2 with _ -> false

(* TODO implement*)
let unix2dos s = s

let string2hex s =
  let l = String.length s in
  let rec worker i a first=
    let sep = if first then "" else "," in
    if i >= l then a
    else
      let zero = if s.[i] <= '\x0f' then "0" else "" in
      let s2 = Printf.sprintf "%s%s%x" sep zero (int_of_char (s.[i])) in
	worker (i+1) (Op.(^.) a (Op.us s2)) false
  in worker 0 (Op.us"") true


let append s1 s2 = Op.(^..) s1 s2

let from_latin1 s = Op.us s

let from_latin1_char c = Op.us  (String.make 1 c)

let from_utf8 s =
  let fail() = raise (Invalid_argument "Ustring.from_utf8") in
  let (s2,len2) = normalize_newlines s in
  let (i,a) = from_utf8_worker s2 len2 fail in
  if i = len2 then ref (Uchars(a)) else fail()

let rec to_uchars s =
  match !s with
    | Uchars(a) -> a
    | Branch(s1,s2) as t -> s := Uchars(collapse t); to_uchars s

let latin1_to_uchar c = Op.uc c

let validate_utf8_string s n =
  let fail pos = raise (Decode_error (Utf8,pos)) in
  let rec validate i =
    if i >= n then i
    else begin
      let s1 = int_of_char s.[i] in
	if s1 land 0b10000000 = 0 then begin
	  validate (i+1)
        end else if (s1 land 0b11100000) = 0b11000000 then begin
	  if i + 1 >= n then i else
	  let s2 = int_of_char s.[i+1] in
	  if s2 land 0b11000000 <> 0b10000000 then fail i else
	  let c = ((s1 land 0b11111) lsl 6) lor (s2 land 0b111111) in
          if c <= 0b1111111 then fail i else
          validate (i+2)
        end else if (s1 land 0b11110000) = 0b11100000 then begin
	  if i + 2 >= n then i else
	  let s2 = int_of_char s.[i+1] in
	  let s3 = int_of_char s.[i+2] in
	  if (s2 land 0b11000000 <> 0b10000000) ||
	     (s3 land 0b11000000 <> 0b10000000) then fail i else
	  let c = ((s1 land 0b1111) lsl 12) lor ((s2 land 0b111111) lsl 6) lor
	    (s3 land 0b111111) in
          if c <= 0b11111111111 then fail i else
          validate (i+3)
        end else if (s1 land 0b11111000) = 0b11110000 then begin
	  if i + 3 >= n then i else
	  let s2 = int_of_char s.[i+1] in
	  let s3 = int_of_char s.[i+2] in
	  let s4 = int_of_char s.[i+3] in
	  if (s2 land 0b11000000 <> 0b10000000) ||
	     (s3 land 0b11000000 <> 0b10000000) ||
	     (s4 land 0b11000000 <> 0b10000000) then fail i else
	  let c = ((s1 land 0b111) lsl 18) lor ((s2 land 0b111111) lsl 12) lor
	    ((s3 land 0b111111) lsl 6) lor (s4 land 0b111111) in
          if c <= 0b1111111111111111 then fail i else
          validate (i+4)
        end else fail i
    end
 in validate 0



(* INTERNAL - check that an ascii string is correct
   Return the number of correct ascii characters *)
let validate_ascii_string s n =
  let rec validate i =
    if i < n && s.[i] < char_of_int 128 then validate (i+1) else i
  in validate 0


(* INTERNAL - used by lexing_from_channel
   This function is applied to Lexing.from_function.
   Exception "Invalid_argument" from function Pervasies.input should
   not happen. *)
let lexing_function ic enc_type inbuf outbuf stream_pos s n =
  let pos = ref 0 in
  let write_from buf =
    let blen = Bytes.length !buf in
    if (n - !pos) <= blen then begin
      Bytes.blit !buf 0 s !pos (n - !pos);
      buf := Bytes.sub !buf (n - !pos) (blen - (n - !pos));
      pos := n
    end else begin
      Bytes.blit !buf 0 s !pos blen;
      buf := Bytes.empty;
      pos := !pos + blen
    end
  in
  (* Read n characters from input or until end of file
     Make sure it does not a partial read *)
  let input_string ic n =
    let rec worker s pos =
      let rlen = input ic s pos (n-pos) in
	if rlen = 0 then Bytes.sub s 0 pos
	else if rlen + pos = n then s
	else worker s (pos+rlen)
    in Bytes.to_string (worker (Bytes.create n) 0)
  in
  let read_to_inbuf i =
    let l1 = Bytes.length !inbuf in
    if l1 >= i then 0 else begin
      let s2 = input_string ic (i - l1) in
      let l2 = String.length s2 in
      let s3 = Bytes.create (l1 + l2) in
	Bytes.blit !inbuf 0 s3 0 l1;
	Bytes.blit (Bytes.of_string s2) 0 s3 l1 l2;
	inbuf := s3;
	l2
    end
  in
  let rec convert() =
    match !enc_type with
      | Ascii -> begin
	  let rlen = read_to_inbuf n in
	    stream_pos := !stream_pos + rlen;
            let len_inbuf = Bytes.length !inbuf in
	    let n2 = validate_ascii_string (Bytes.to_string !inbuf) len_inbuf in
	      write_from inbuf;
	      if n2 = len_inbuf then !pos
	      else raise (Decode_error(Ascii,!stream_pos-(len_inbuf-n2)))
	end
      | Latin1 -> begin
	  write_from outbuf;
	  let rlen = read_to_inbuf (n - !pos) in
	    outbuf := Bytes.cat (!outbuf)  (Bytes.of_string (to_utf8 (from_latin1 (Bytes.to_string (!inbuf)))));
	    inbuf := Bytes.empty;
	    stream_pos := !stream_pos + rlen;
	    write_from outbuf;
	    !pos
	end
      | Utf8 -> begin
	  let rlen = read_to_inbuf n in
	    stream_pos := !stream_pos + rlen;
	    let len_inbuf = Bytes.length !inbuf in
	      try begin
		let n2 = validate_utf8_string (Bytes.to_string !inbuf) len_inbuf in
		  outbuf := Bytes.cat (!outbuf)  (Bytes.sub !inbuf 0 n2);
		  inbuf := Bytes.sub !inbuf n2 (len_inbuf-n2);
		  write_from outbuf;
		  !pos
	      end with
		  Decode_error (_,errpos) -> raise
		    (Decode_error(Utf8, !stream_pos - (len_inbuf - errpos)))
	end
      | Utf16le -> assert false (* Not yet implemented *)
      | Utf16be -> assert false (* Not yet implemented *)
      | Utf32le -> assert false
      | Utf32be -> assert false
      | Auto -> begin
	  let rlen = read_to_inbuf n in
	    stream_pos := !stream_pos + rlen;
	    let len_inbuf = Bytes.length !inbuf in
	    let n2 = validate_ascii_string (Bytes.to_string !inbuf) len_inbuf in
	      (* Keep on reading just ascii? *)
	      if n2 = len_inbuf then begin
		write_from inbuf;
		!pos
	      end
	      else begin (* Use Utf8 or Latin1? *)
		let rlen = read_to_inbuf (n+3) in (* Enough for utf8 char *)
		stream_pos := !stream_pos + rlen;
		try begin
		  let _ = validate_utf8_string (Bytes.to_string !inbuf) (Bytes.length !inbuf) in
		  enc_type := Utf8;
		  convert()
		end with
		    Decode_error (_,_) -> begin
		      enc_type := Latin1;
		      convert()
		    end
	      end
	end
  in
    convert()

let utf32be = Bytes.of_string "\x00\x00\xFE\xFF"
let utf32le = Bytes.of_string "\xFF\xFE\x00\x00"
let utf16be = Bytes.of_string "\xFE\xFF"
let utf16le = Bytes.of_string "\xFF\xFE"
let utf8    = Bytes.of_string "\xEF\xBB\xBF"


(* INTERNAL - Read in BOM *)
let read_bom ic =
  let s = Bytes.create 4 in
  let l = ref 0 in
  try
    really_input ic s 0 2; l := 2;
    if Bytes.sub s 0 2 = utf16be then (Utf16be,Bytes.empty) else (
    really_input ic s 2 1; l := 3;
    if Bytes.sub s 0 3 = utf8 then (Utf8,Bytes.empty) else (
    if Bytes.sub s 0 2 = utf16le && Bytes.get s 2 != '\x00'
      then (Utf16le,Bytes.sub s 2 1) else (
    really_input ic s 3 1; l := 4;
    if s = utf32be then (Utf32be,Bytes.empty) else
    if s = utf32le then (Utf32le,Bytes.empty) else
    (Auto,s))))
  with
      End_of_file -> (Auto,Bytes.sub s 0 !l)

(* Internal *)
let lexing_function ?(encode_type=Auto) ic =
  match encode_type with
    | Auto -> begin
	let (enc,buf) = read_bom ic in
	  (lexing_function ic (ref enc)
	     (ref buf) (ref Bytes.empty) (ref (Bytes.length buf)))
      end
    | _ -> (lexing_function ic (ref encode_type)
	    (ref Bytes.empty) (ref Bytes.empty) (ref 0))


let lexing_from_channel ?(encode_type=Auto) ic =
  Lexing.from_function (lexing_function ~encode_type:encode_type ic)


let lexing_from_ustring s =
  Lexing.from_string (to_utf8 s)

let read_from_channel ?(encode_type=Auto) ic =
  let reader = lexing_function ~encode_type:encode_type ic in
  let readsize = 4096 in
  let buf = ref Bytes.empty in
  (* Should not fail, since UTF-8 is already checked*)
  let fail() = assert false in
  fun l -> begin
    let s = Bytes.create readsize in
    let read_l = reader s readsize in
    let s2 = Bytes.cat (!buf)  (Bytes.sub s 0 read_l) in
    let len2 = Bytes.length s2 in
    let (i,a) = from_utf8_worker (Bytes.to_string s2) len2 fail in
    buf := Bytes.sub s2 i (len2-i);
    ref (Uchars(a))
  end


let convert_escaped_chars s =
  let rec conv esc s =
    match esc,s with
      | (false,0x5C::ss)  -> conv true ss                (*  \ *)
      | (false,c::ss) -> c::(conv false ss)
      | (false,[]) -> []
      | (true,0x27::ss) -> 0x27::(conv false ss)         (*  "\'" *)
      | (true,0x22::ss) -> 0x22::(conv false ss)         (*  "\"" *)
      | (true,0x3f::ss) -> 0x3f::(conv false ss)         (*  "\?" *)
      | (true,0x5c::ss) -> 0x5c::(conv false ss)         (*  "\\" *)
      | (true,0x6E::ss) -> 0x0A::(conv false ss)         (*  "\n" *)
      | (true,0x74::ss) -> 0x09::(conv false ss)         (*  "\t" *)
      | (true,_) -> raise (Invalid_argument "Ustring.convert_escaped_char")
  in
  let a2 = conv false (Array.to_list (collapse_ustring s)) in
    ref (Uchars(Array.of_list a2))

let read_file ?(encode_type=Auto) fn =
  let ic = open_in fn in
  let reader = read_from_channel ~encode_type:encode_type ic in
  let rec readloop sack =
    let s = reader 4096 in
    if length s = 0 then sack
    else readloop (Op.(^.) sack s)
  in
  let sout = readloop (Op.us"") in
    close_in ic; sout


let write_file ?(encode_type=Utf8) fn s =
  let data = match encode_type with
    | Utf8 -> to_utf8 s
    | Latin1 -> to_latin1 s
    | _ -> failwith "Encoding not supported."
  in
  Utils.write_binfile fn (Bytes.of_string data)
