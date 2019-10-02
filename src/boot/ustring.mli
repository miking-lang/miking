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

(** Unicode string library - Ustring.
    Version 0.01
    This module implements Unicode variants of functions using strings
    in the OCaml standard library, e.g., modules [String] and [Pervasives].
    There are also a number of additional functions available. Several
    basic operators (e.g., equality and string concatenation) are defined in
    sub module {!Ustring.Op}. It is recommended to open up this sub module
    but not [Ustring] directly.

    This module currently supports ASCII, Latin-1, and UTF-8 encoding. If
    another encoding is used, an exception will be raised. In all functions
    below, a ustring [s] is indexed from [0] to [(Ustring.length s)-1].

    Copyright (C) 2010-2012 David Broman. All rights reserved. This file
    is distributed under the "New BSD License".
*)

type uchar = int
(** Unicode char type. It is a basic integer. *)



module Op :
sig

  type ustring
  (** Unicode string type *)

  type sid
  (** Type of an string identifier *)


  module SidSet :
  sig
    type elt = sid
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
  (** Module for handling  set of string identifiers. Uses OCaml's standard set module *)

  type sidset = SidSet.t
  (* Set of string identifiers *)

  val ( ^. ) : ustring -> ustring -> ustring
  (** Fast infix string concatenation operator. Equivalent to function
      [Ustring.fast_append]. Compared to function [append] and
    standard string concatenation operator [^], function [fast_append] do not
    allocate new memory or create a new fresh string. Instead,
    the concatenation is internally stored as a tree, making
    the operation constant time. When the string is later used by some function
    in module [Ustring], the internal tree representation will be automatically
    collapsed to a plain string. Note that in contrary to [append], this
    function do not create a fresh new string directly. Hence, if the sub strings
    are shared and modified in place, this string will also be updated. To
    make sure that the result string is unique, call function [Ustring.copy].
    It is recommended to use [^.] instead of [^..]
  *)

  val ( ^.. ) : ustring -> ustring -> ustring
  (** Infix string concatenation operator. Equivalent to function
      [Ustring.append]. Note that this function is always creating a new fresh
      string after append. For performance demanding application, function
      [fast_append] or operator [^.] are recommended instead.
  *)

  val ( =. ) : ustring -> ustring -> bool
  (** Safe structural equality operator for ustrings. For performance reason, an
      ustring instance can have different representations internally for the same
      string. Hence, use of standard equality operator [=] is unsafe. Always use this
      operator instead. This operator is equivalent to function [Ustring.equal] *)

  val ( <>. ) : ustring -> ustring -> bool
  (** Safe structural inequality operator for ustrings. This operator is
      equivalent to function [Ustring.not_equal]. See also operator [=.] *)

  val us : string -> ustring
  (** Creates a ustring from a Latin-1 encoded OCaml string. This
      function is an alias function for [Ustring.from_latin1]. The purpose
      is to make it a simple short-cut for writing inline Unicode strings
      in programs, e.g., [(us"This is a Unicode string")] defines a ustring. *)

  val uc : char -> uchar
  (** Creates a uchar from a Latin-1 encoded char. *)

  val sid_of_ustring : ustring -> sid
  (** Returns a unique string identifier for the ustring. This identifier can
      only be checked for equality using the standard = operator and for
      looking up using function [ustring_of_sid] (see below). The identifier
      is globally defined. The mechanism is a simple way of implementing a
      fast symbol table. All lookups are performed using a hash tables. *)

  val ustring_of_sid : sid -> ustring
  (** Looks up a [ustring] for a specific [sid] (string identifier).
      If the string identifier has not been defined, exception
      [Not_found] is raised *)

  val usid : string -> sid
  (** Expression [sid s] returns a unique string identifier of string [s].
      Same as expression [sid_of_ustring (us s)] *)

  (** {6 Module Pervasives's functions} *)
  (** The following section defines the Unicode version of several functions
      available in the [Pervasives] module. *)

  val ustring_of_bool : bool -> ustring
  (** Returns the string representation ("true" or "false") of the boolean
      argument. *)

  val bool_of_ustring : ustring -> bool
  (** Expression [bool_of_ustring s] returns ["true"] if [s] has value [true] or
      [false] if [s] has value ["false"]. Raises
      [Invalid_argument "bool_of_ustring"] if the string is neither ["true"]
      nor ["false"]. *)

  val ustring_of_int : int -> ustring
  (** Returns the string representation of an integer in decimal. *)

  val int_of_ustring : ustring -> int
  (** Expression [int_of_ustring s] converts string [s] to an integer value.
      By default, the string is assumed to be encoded in decimal form, e.g.
      [1342] or [-3212]. If the string starts with [0x] or [0X] it is interpreted
      as hexadecimal. If it starts with [0o] or [0O] it is treated as octal and
      if starting with [0b] or [0B] as binary. If the string has not a valid
      representation or if its size exceeds the range of type [int], exception
      [Failure "int_of_ustring"] is raised. *)

  val ustring_of_float : float -> ustring
  (** Returns the string representation of a floating-point number. *)

  val float_of_ustring : ustring -> float
  (** Converts the ustring representation of a floating-point number, e.g.,
      [123.21], [-0.1231], or [3.212e-12] to a floating-point value. Raises
      [Failure "float_of_ustring"] if the string do not represent a
      valid floating-point number. *)

  val uprint_char : uchar -> unit
  (** Prints a uchar to the standard output. Converts to UTF-8 encoding. *)

  val uprint_string : ustring -> unit
  (** Prints a ustring to the standard output. Converts to UTF-8 encoding *)

  val uprint_int : int -> unit
  (** Prints an integer i decimal form to the standard output.
      Same as pervasives function print_int *)

  val uprint_float : float -> unit
  (** Prints a floating-point number in decimal form to the standard output.
      Same as pervasives function print_float *)

  val uprint_endline : ustring -> unit
  (** Prints a ustring to the standard output, followed by a
      newline character and flush of the standard output.
      Converts to UTF-8 encoding. *)

  val uprint_newline : unit -> unit
  (** Prints a new line and flushes the standard output.
      Same as pervasives function print_newline *)


  val list2ustring : int list -> ustring

  val ustring2list : ustring -> int list

  (** {6 Other functions} *)

  val uprint_bool : bool -> unit
  (** Prints the string representation of an boolean to the standard output. *)

end
(** Sub module {!Ustring.Op} is containing Unicode versions of several functions
    available in the [Pervasives] module, as well as operators and functions
    for simple string creation and manipulation (for example string concatenation
    operator [^.], ustring equality operator [=.] and string creation [us"string"]).
    Use it by opening the op module [open Ustring.Op] Do not open module [Ustring]
    directly, since there is a risk for name conflicts.
*)

type t = Op.ustring
(** Alias for the type [Op.ustring] *)

type ustring = Op.ustring
(** Alias for the type [Op.ustring] *)

type encoding =
  | Ascii   (** Standard ASCII (values 0-127) *)
  | Latin1  (** Latin-1 encoding. Supports most European languages. *)
  | Utf8    (** UTF-8 encoding. Full Unicode encoding, where each character
               is represented by 1-4 bytes. *)
  | Utf16le (** Not yet supported *)
  | Utf16be (** Not yet supported *)
  | Utf32le (** Not yet supported *)
  | Utf32be (** Not yet supported *)
  | Auto    (** Not a specific encoding, but a method for how encoded data
                is interpreted. If the input data have a
                byte order mark (BOM) in the beginning of the sequence, the
                encoding type stated in the BOM will be used.
		If no BOM is available, ASCII will initially be assumed to be
		the encoding type. Then, when a byte sequence appear that is
		not ASCII (value 0-127), a choice is made for the remaining
		encoding type: If the sequence represents a legal UTF-8 encoded
		character, the rest of the input will be treated as UTF-8
                encoded.
		If it is not an UTF encoded character, Latin-1 will be assumed
		for the rest of the data sequence. Any later illegal decoding
		will then be reported as an error. *)



(** {6 Module String's functions} *)

(** The following section implements the Unicode version of the
    functions available in standard library module [String]. *)

val length : ustring -> int
(** [Ustring.length s] returns the number of characters of [s]. *)

val get : ustring -> int -> uchar
(** [Ustring.get s n] returns character number [n] in ustring [s].
    Raises [Invalid_argument "Ustring.get"] if out of range. *)

val set : ustring -> int -> uchar -> unit
(** [Ustring.set s n c] modifies ustring [s] in place by replacing uchar at
    index [n] by uchar [c]. Raises [Invalid_argument "Ustring.get"] if out of
    range. *)

val create : int -> ustring
(** Function [Ustring.create n] returns a new fresh ustring with length [n]
    characters. Raises [Invalid_argument "Ustring.create"] if [n < 0] or
    [n > Sys.max_array_length]. *)

val make : int -> uchar -> ustring
(** Function [Ustring.make n c] returns a new fresh ustring of length [n], filled
    with character [c]. Raises [Invalid_argument "Ustring.make"] if [n < 0] or
    [n > Sys.max_array_length]. *)

val copy : ustring -> ustring
(** Returns a fresh copy of the string, i.e., there will be no more
    sharing *)

val sub : ustring -> int -> int -> ustring
(** Function [Ustring.sub s start len] returns a new ustring with length
    [len], consisting of a sub-string of [s], which starts at index
    position [start] and has length [len]. Raises exception
    [Invalid_argument "Ustring.sub"] if [start] and [len] does not
    give a valid sub-string. *)

val concat : ustring -> ustring list -> ustring
(** [Ustring.concat sep sl] returns a ustring where the list of ustrings
    [sl] are concatenated, were separator string [sep] is inserted between
    each list element. The function always return a new fresh string.
    If performance is critical, use function fast_concat *)

val rindex : ustring -> uchar -> int
(** [Ustring.rindex s c] returns the index of the last occurrence of
    character [c] in ustring [s]. Raises [Not_found] if [c] does not
    occur in [s]. *)

val rindex_from : ustring -> int -> uchar -> int
(** [Ustring.rindex_from s i c] returns the index of the last occurrence of
    character [c] in ustring [s] before index position [i+1]. Note that
    function calls [Ustring.rindex s] and
    [Ustring.rindex_from s (Ustring.length s - 1) c] are equivalent.
    Raises [Not_found] if [c] does not occur in [s]. Raises
    [Invalid_argument "Ustring.rindex_from"] if [i+1] is an illegal
    index in ustring [s].*)

(** {6 Additional string functions} *)

val append : ustring -> ustring -> ustring
(** Append/concatenation of two strings. This function is equivalent to
    infix operator [^..]. Please see module {!Ustring.Op} for more details about the
    operator. Note that this function is always creating a new fresh string
    after append. For performance demanding application, function
    [fast_append] or operator [^.] are recommended instead. *)

val fast_append : ustring -> ustring -> ustring
(** Fast append/concatenation of two strings. Compared to function [append] and
    standard string concatenation operator [^], function [fast_append] do not
    allocate new memory or create a new fresh string. Instead,
    the concatenation is internally stored as a tree, making
    the operation constant time. When the string is later used by some function
    in module [Ustring], the internal tree representation will be automatically
    collapsed to a plain string. Note that in contrary to [append], this
    function do not create a fresh new string directly. Hence, if the sub strings
    are shared and modified in place, this string will also be updated. To
    make sure that the result string is unique, call function [copy].
    This function is equivalent to infix operator [^.] Please see module
    {!Ustring.Op} for more details about the operator.
*)

val fast_concat : ustring -> ustring list -> ustring
(** Same as function [concat] with the difference that it is not returning
    a fresh string. Function [fast_concat] is instead using [fast_append]
    for string concatenation. *)

val count : ustring -> uchar -> int
(** [Ustring.count s c] returns the number of occurrences of character [c]
    in ustring [s]. *)

val trim_left : ustring -> ustring
(** Returns a new ustring where white space (e.g. space, newline and tab)
    is removed from the beginning of the input ustring. *)

val trim_right : ustring -> ustring
(** Returns a new ustring where white space (e.g. space, newline and tab)
    is removed from the end of the input ustring. *)

val trim : ustring -> ustring
(** Returns a new ustring where white space (e.g. space, newline and tab)
    is removed from the beginning and end of the input ustring. *)

val empty : unit -> ustring
(** Returns an empty ustring *)

val split : ustring -> ustring -> ustring list
(** [split s c] splits string [s] at points where characters in [c] appears.
    For instance, if string ["This is a string"] is split using the space
    character [" "], then list [\["This";"is";"a";"string"\]] is returned.*)

val starts_with : ustring -> ustring -> bool
(** [starts_with w s] returns true if string [s] starts with [w]. *)

val ends_with : ustring -> ustring -> bool
(** [ends_with w s] returns true if string [s] ends with [w]. For instance,
    if [s="file/"] and [w="/"], then [(ends_with w s)] is true. *)

val unix2dos : string -> string
(** Function [Ustring.unix2dos s] returns a string where newline characters in
    string [s] are converted to the DOS and Windows standard. The ustring
    module handles all strings internally using line feed (LF) code 0x0A, which
    is standard in Unix-like systems (e.g., GNU/Linux, Mac OS X, and FreeBSD).
    All input functions (e.g., [from_utf8()] or [from_latin1()]) automatically
    converts to this format. Hence, when ustrings are encoded using e.g.
    LATIN-1 or UTF-8, they will only contain the LF charcter for new line.
    However, for example Windows, DOS, OS/2 and Symbian OS are using
    the sequence of Carriage return (CR) 0x0D and LF 0x0A. This function
    converts from unix-style to this format. *)

val string2hex : string -> ustring
(** Function [Ustring.string2hex s] returns a comma separated list of hex
    values for the bytes in string [s]. For example, from input string ["an_"]
    a ustring ["61,6e,5f"] is returned. *)

val convert_escaped_chars : ustring -> ustring
(** Converts escaped characters. Raises
      [Invalid_argument "convert_escaped_chars"] if the string contains
    illegal escape sequences. *)

val read_file : ?encode_type:encoding -> string -> ustring
(** Function [Ustring.read_file fn] returns a ustring of the whole contents
    of a file with file name [fn]. By default, the encoding type is [Auto]
    (see type [encoding] for details). The input can also be forced to be
    assumed to be another encoding type. For example, expression
    [Ustring.read_file ~encode_type:Ustring.Utf8 fn] creates
    an ustring that will assume that the input file is encoded using UTF-8.
    If there is a decoding error exception [Decode_error enc pos] is raised.
    Argument [enc] is the encoding type
    and [pos] is number of bytes read from the file when the decoding error
    occurred. Raises [Sys_error] if there where problems opening or reading
    from the file.*)

val write_file : ?encode_type:encoding -> string -> ustring -> unit
(** Function [Ustring.write_file fn s] writes unicode string [s] to a
    a file named [fn]. The default character encoding is UTF-8. *)

val read_from_channel : ?encode_type:encoding -> in_channel ->
                        (int -> ustring)
(** Function [Ustring.read_from_channel ic] returns a function which
    can read from the in_channel. The returned function has one argument stating
    the number of Unicode characters that should be read from the stream.
    It returns an ustring with the read characters. The length of the
    returned ustring is approximately the requested number of characters,
    i.e., the function can do a partial read. If the returned ustring has
    length zero, the end of the character stream has been reached. If there is
    a decoding error exception [Decode_error enc pos] is raised. Argument
    [enc] is the encoding type and [pos] is number of bytes read from the
    file when the decoding error occurred. Note that this function should
    only be called once to get the read function [int -> ustring] and no
    other function is allowed to read from this channel at the same time.*)


(** {6 Encoding} *)


exception Decode_error of (encoding * int)
(** Exception raised when a decode error occurrs. First parameter represents
    the encoding method used when the error occurred and the second parameter
    is the position in the stream/string/channel. *)

val from_latin1 : string -> ustring
(** Creates an ustring from a string that is
    assumed to be encoded with Latin-1. *)

val from_latin1_char : char -> ustring
(** Creates an ustring from a Latin-1 encoded char *)

val from_utf8 : string -> ustring
(** Creates an ustring from a string that is assumed to be
    encoded using UTF-8. Raises exception [Invalid_argument "Ustring.from_utf8"]
    if the input string has not a valid UTF-8 encoding. The input string
    must not have a byte order mark (BOM). *)

val from_uchars : uchar array -> ustring
(** Converts an array of uchars to an ustring. Raises exception
    [Invalid_argument "Ustring.from_uchars"] if uchar values are illegal
    (must be in range 0x0-0x1FFFFF). *)

val latin1_to_uchar : char -> uchar
(** Converts a Latin-1 encoded char to an uchar *)

val to_latin1 : ustring -> string
(** Creates a new string encoded using Latin-1. Raises
    [Invalid_argument "Ustring.to_latin1"] if the characters are not within
    the ASCII and Latin-1 character set (values 0-255). *)

val to_utf8 : ustring -> string
(** Returns an UTF-8 encoded string. An UTF-8 string consist of a sequence of
    bytes where each Unicode character is encoded into 1 to 4 bytes. ASCII
    characters are always encoded into 1 byte. *)

val to_uchars : ustring -> uchar array
(** Returns an array of uchars. *)


val validate_utf8_string : string -> int -> int
(** Expression [Ustring.validate_utf8_string s n] checks if the first [n] characters
    of string [s] have valid UTF-8 encoding. If the input is valid, but not all data
    is available (e.g. at the end, only 2 bytes are available for a character
    that needs 3 bytes), the number of characters that represent
    whole characters are return. Raises exception
    [Decode_error enc pos] if the string has not a valid
    UTF-8 encoding. Argument [enc] is the encoding type and [pos] is the position
    in string [s] of the decode error. *)


(** {6 Lexing} *)

(** The [Ustring] module is especially designed for simple support of
    Unicode lexing and parsing. The below functions are defined for this
    purpose. *)

val lexing_from_channel : ?encode_type:encoding -> in_channel -> Lexing.lexbuf
(** Creates a new [Lexing.lexbuf] on a given input channel. Expression
    [Ustring.lexing_from_channel inchan] returns a lexer buffer that reads
    from input channel [inchan]. By default, the encoding type is [Auto]
    (see type [encoding] for details). The input can also be forced to be
    assumed to be another encoding type. For example, expression
    [Ustring.lexing_from_channel ~encode_type:Ustring.Utf8 inchan] creates
    a lexbuf that will assume that the input data is encoded using UTF-8.
    The stream of characters that are returned to the lexical analyzer is
    always UTF-8, regardless of the input encoding. Hence, this function
    is a simple and safe way to do lexical analysis of arbitrary encoded
    text data. If there is an encoding error of the data read from
    [inchan], Raises exception [Decode_error enc pos] if there is a decoding
    error of the data read from  [inchan]. Argument [enc] is the encoding type
    and [pos] is number of bytes read from [inchan] when the decoding error
    occurred. *)


val lexing_from_ustring :  ustring -> Lexing.lexbuf
(** Creates a new [Lexing.lexbuf] that reads from a ustring. The stream of
    characters that are returned to the lexical analyzer is
    always UTF-8. *)

(** {6 Comparison and Standard Collections} *)

val equal: t -> t -> bool
(** Safe structural equality comparison function for ustrings.
    For easy usage, use the equivalent operator [=.] which is defined in
    module {!Ustring.Op}. *)

val not_equal: t -> t -> bool
(** Safe structural inequality comparison function for ustrings.
    For easy usage, use the equivalent operator [<>.] which is defined in
    module {!Ustring.Op}. *)

val compare: t -> t -> int
(** Comparison function for ustrings. Uses the same specification as
    [Pervasives.compare]. Since both type [t] and function [compare] is
    implemented, module [UString] can be passed directly to functors such
    as [Set.Make] and [Map.Make]. For example, to create a map the uses
    ustrings as the key, use the following source code line:

    [module USMap = Map.Make (Ustring)] *)

val hash : t -> int
(** Implements a safe hash function for ustrings. Since type [t] and
    functions [hash] and [equal] are implemented, module [UString] can
    be passed directly to functor Hashtbl.Make, making it simple to
    use ustrings as keys in a hash table. For example, to create a
    hash table that uses ustrings as keys, use the following source
    code line:

    [module USHash = Hashtbl.Make(Ustring)] *)
