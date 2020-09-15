
(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
*)

open Ustring.Op
open Msg
open Ast
open Pprint
open Printf

(* This function determines how to print program output.
   It's used to redirect standard output of a program,
   for instance by the Jupyter kernel *)
let program_output = ref uprint_string

(* Extract the arguments when running boot, and the arguments of the actual program.
   -- is used to separate the program arguments. For instance,
     mi myprog.mc --debug-parse -- foo --something
   results in two arrays:
    argv_boot: ["mi","myprog.mc","--debug-parse"]
    argv_prog: ["mi","foo","--something"] *)
let (argv_boot,argv_prog) =
  let (n,_) = Sys.argv |>
      (Array.fold_left (fun (n,b) x -> if x = "--" || b then (n,true) else (n+1,b)) (0,false)) in
  (Array.sub Sys.argv 0 n,
   Array.append (Array.sub Sys.argv 0 1)
     (try Array.sub Sys.argv (n+1) ((Array.length Sys.argv)-n-1) with _ -> [||]))

(* Mapping between named builtin functions (intrinsics) and the
   correspond constants *)
let builtin =
  let f c = TmConst(NoInfo,c) in
  ([("addi",f(Caddi(None)));("subi",f(Csubi(None)));("muli",f(Cmuli(None)));
   ("divi",f(Cdivi(None)));("modi",f(Cmodi(None)));("negi",f(Cnegi));
   ("lti",f(Clti(None)));("leqi",f(Cleqi(None)));("gti",f(Cgti(None)));("geqi",f(Cgeqi(None)));
   ("eqi",f(Ceqi(None)));("neqi",f(Cneqi(None)));
   ("slli",f(Cslli(None)));("srli",f(Csrli(None)));("srai",f(Csrai(None)));
   ("arity",f(Carity));
   ("addf",f(Caddf(None)));("subf",f(Csubf(None)));("mulf",f(Cmulf(None)));
   ("divf",f(Cdivf(None)));("negf",f(Cnegf));
   ("ltf",f(Cltf(None)));("leqf",f(Cleqf(None)));("gtf",f(Cgtf(None)));("geqf",f(Cgeqf(None)));
   ("eqf",f(Ceqf(None)));("neqf",f(Cneqf(None)));
   ("exp",f(Cexp));
   ("floorfi", f(Cfloorfi)); ("ceilfi", f(Cceilfi)); ("roundfi", f(Croundfi));
   ("int2float", f(CInt2float)); ("string2float", f(CString2float));
   ("char2int",f(CChar2int));("int2char",f(CInt2char));
   ("makeSeq",f(CmakeSeq(None))); ("length",f(Clength));("concat",f(Cconcat(None)));
   ("get",f(Cget(None)));("set",f(Cset(None,None)));
   ("cons",f(Ccons(None)));("snoc",f(Csnoc(None)));
   ("splitAt",f(CsplitAt(None)));("reverse",f(Creverse));
   ("print",f(Cprint));("dprint",f(Cdprint));
   ("readLine",f(CreadLine));("readBytesAsString",f(CreadBytesAsString));
   ("argv",TmSeq(NoInfo,argv_prog
                        |> Mseq.of_array
                        |> Mseq.map (fun s ->
                               TmSeq(NoInfo,s
                                            |> us
                                            |> Mseq.of_ustring
                                            |> Mseq.map (fun x->
                                                   TmConst(NoInfo,CChar(x)))))));
   ("readFile",f(CreadFile)); ("writeFile",f(CwriteFile(None)));
   ("fileExists", f(CfileExists)); ("deleteFile", f(CdeleteFile));
   ("error",f(Cerror));
   ("exit",f(Cexit));
   ("eqs", f(Ceqs(None))); ("gensym", f(Cgensym)); ("sym2hash", f(CSym2hash));
   ("randIntU", f(CrandIntU(None))); ("randSetSeed", f(CrandSetSeed));
   ("wallTimeMs",f(CwallTimeMs)); ("sleepMs",f(CsleepMs));
  ]
  (* Append external functions TODO: Should not be part of core language *)
  @ Ext.externals
  (* Append python intrinsics *)
  @ Pyffi.externals)
  |> List.map (fun (x,t) -> (x,gensym(),t))

(* Mapping name to symbol *)
let builtin_name2sym = List.map (fun (x,s,_) -> (IdVar(usid x),s)) builtin

(* Mapping sym to term *)
let builtin_sym2term = List.map (fun (_,s,t) -> (s,t)) builtin


(* Returns the number of expected arguments of a constant *)
let arity = function
  (* MCore intrinsic: Boolean constant and operations *)
  | CBool(_)    -> 0
  (* MCore intrinsic: Integer constant and operations *)
  | CInt(_)     -> 0
  | Caddi(None) -> 2  | Caddi(Some(_)) -> 1
  | Csubi(None) -> 2  | Csubi(Some(_)) -> 1
  | Cmuli(None) -> 2  | Cmuli(Some(_)) -> 1
  | Cdivi(None) -> 2  | Cdivi(Some(_)) -> 1
  | Cmodi(None) -> 2  | Cmodi(Some(_)) -> 1
  | Cnegi       -> 1
  | Clti(None)  -> 2  | Clti(Some(_))  -> 1
  | Cleqi(None) -> 2  | Cleqi(Some(_)) -> 1
  | Cgti(None)  -> 2  | Cgti(Some(_))  -> 1
  | Cgeqi(None) -> 2  | Cgeqi(Some(_)) -> 1
  | Ceqi(None)  -> 2  | Ceqi(Some(_))  -> 1
  | Cneqi(None) -> 2  | Cneqi(Some(_)) -> 1
  | Cslli(None) -> 2  | Cslli(Some(_)) -> 1
  | Csrli(None) -> 2  | Csrli(Some(_)) -> 1
  | Csrai(None) -> 2  | Csrai(Some(_)) -> 1
  | Carity      -> 1
  (* MCore intrinsic: Floating-point number constant and operations *)
  | CFloat(_)   -> 0
  | Caddf(None) -> 2  | Caddf(Some(_)) -> 1
  | Csubf(None) -> 2  | Csubf(Some(_)) -> 1
  | Cmulf(None) -> 2  | Cmulf(Some(_)) -> 1
  | Cdivf(None) -> 2  | Cdivf(Some(_)) -> 1
  | Cnegf       -> 1
  | Cltf(None)  -> 2  | Cltf(Some(_))  -> 1
  | Cleqf(None) -> 2  | Cleqf(Some(_)) -> 1
  | Cgtf(None)  -> 2  | Cgtf(Some(_))  -> 1
  | Cgeqf(None) -> 2  | Cgeqf(Some(_)) -> 1
  | Ceqf(None)  -> 2  | Ceqf(Some(_))  -> 1
  | Cneqf(None) -> 2  | Cneqf(Some(_)) -> 1
  | Cexp        -> 1
  | Cfloorfi    -> 1
  | Cceilfi     -> 1
  | Croundfi    -> 1
  | CInt2float  -> 1
  | CString2float -> 1
  (* MCore intrinsic: characters *)
  | CChar(_)    -> 0
  | CChar2int   -> 1
  | CInt2char   -> 1
  (* MCore intrinsic: sequences *)
  | CmakeSeq(None)    -> 2 | CmakeSeq(Some(_)) -> 1
  | Clength           -> 1
  | Cconcat(None)     -> 2 | Cconcat(Some(_)) -> 1
  | Cget(None)        -> 2 | Cget(Some(_)) -> 1
  | Cset(None,None)   -> 3 | Cset(Some(_),None) -> 2 | Cset(_,Some(_)) -> 1
  | Ccons(None)       -> 2 | Ccons(Some(_)) -> 1
  | Csnoc(None)       -> 2 | Csnoc(Some(_)) -> 1
  | CsplitAt(None)    -> 2 | CsplitAt(Some(_)) -> 1
  | Creverse          -> 1
  (* MCore intrinsic: elapsed time *)
  | CwallTimeMs       -> 1
  | CsleepMs          -> 1
  (* MCore debug and I/O intrinsics *)
  | Cprint             -> 1
  | Cdprint            -> 1
  | CreadLine          -> 1
  | CreadBytesAsString -> 1
  | CreadFile          -> 1
  | CwriteFile(None)   -> 2 | CwriteFile(Some(_)) -> 1
  | CfileExists        -> 1
  | CdeleteFile        -> 1
  | Cerror             -> 1
  | Cexit              -> 1
  (* MCore symbols *)
  | CSymb(_)      -> 0
  | Cgensym       -> 1
  | Ceqs(None)    -> 2
  | Ceqs(Some(_)) -> 1
  | CSym2hash      -> 1
  (* Python intrinsics *)
  | CPy v -> Pyffi.arity v
  (* External functions TODO: Should not be part of core language *)
  | CExt v            -> Ext.arity v
  (* MCore intrinsic: random numbers *)
  | CrandIntU(None)    -> 2
  | CrandIntU(Some(_)) -> 1
  | CrandSetSeed       -> 1


(* API for generating unique symbol ids *)
let symid = ref 0
let gen_symid _ =
  symid := !symid + 1;
  !symid

(* Random number generation *)
let rand_is_seeded = ref false
let rand_set_seed seed =
  Random.init seed;
  rand_is_seeded := true

let rand_int_u lower upper =
  if !rand_is_seeded then () else Random.self_init ();
  lower + Random.int (upper - lower)

let fail_constapp f v fi = raise_error fi ("Incorrect application. function: "
                                         ^ Ustring.to_utf8
                                           (ustring_of_const f)
                                         ^ " value: "
                                         ^ Ustring.to_utf8
                                           (ustring_of_tm v))

(* Get current time stamp *)
let get_wall_time_ms _ =
  Unix.gettimeofday () *. 1000.

(* Sleep a number of ms *)
let sleep_ms ms =
  Thread.delay ((float_of_int ms) /. 1000.)

(* Evaluates a constant application. This is the standard delta function
   delta(c,v) with the exception that it returns an expression and not
   a value. This is why the returned value is evaluated in the eval() function.
   The reason for this is that if-expressions return expressions
   and not values. *)
let delta eval env fi c v  =
    let index_out_of_bounds_in_seq_msg = "Out of bounds access in sequence" in
    let fail_constapp = fail_constapp c v in
    match c,v with
    (* MCore boolean intrinsics *)
    | CBool(_),_ -> fail_constapp fi

    (* MCore integer intrinsics *)
    | CInt(_),_ -> fail_constapp fi

    | Caddi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Caddi(Some(v)))
    | Caddi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 + v2))
    | Caddi(None),_ | Caddi(Some(_)),_  -> fail_constapp fi

    | Csubi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Csubi(Some(v)))
    | Csubi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 - v2))
    | Csubi(None),_ | Csubi(Some(_)),_  -> fail_constapp fi

    | Cmuli(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cmuli(Some(v)))
    | Cmuli(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 * v2))
    | Cmuli(None),_ | Cmuli(Some(_)),_  -> fail_constapp fi

    | Cdivi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cdivi(Some(v)))
    | Cdivi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 / v2))
    | Cdivi(None),_ | Cdivi(Some(_)),_  -> fail_constapp fi

    | Cmodi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cmodi(Some(v)))
    | Cmodi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 mod v2))
    | Cmodi(None),_ | Cmodi(Some(_)),_  -> fail_constapp fi

    | Cnegi,TmConst(fi,CInt(v)) -> TmConst(fi,CInt((-1)*v))
    | Cnegi,_ -> fail_constapp fi

    | Clti(None),TmConst(fi,CInt(v)) -> TmConst(fi,Clti(Some(v)))
    | Clti(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 < v2))
    | Clti(None),_ | Clti(Some(_)),_  -> fail_constapp fi

    | Cleqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cleqi(Some(v)))
    | Cleqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 <= v2))
    | Cleqi(None),_ | Cleqi(Some(_)),_  -> fail_constapp fi

    | Cgti(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cgti(Some(v)))
    | Cgti(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 > v2))
    | Cgti(None),_ | Cgti(Some(_)),_  -> fail_constapp fi

    | Cgeqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cgeqi(Some(v)))
    | Cgeqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 >= v2))
    | Cgeqi(None),_ | Cgeqi(Some(_)),_  -> fail_constapp fi

    | Ceqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Ceqi(Some(v)))
    | Ceqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 = v2))
    | Ceqi(None),_ | Ceqi(Some(_)),_  -> fail_constapp fi

    | Cneqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cneqi(Some(v)))
    | Cneqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 <> v2))
    | Cneqi(None),_ | Cneqi(Some(_)),_  -> fail_constapp fi

    | Cslli(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cslli(Some(v)))
    | Cslli(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 lsl v2))
    | Cslli(None),_ | Cslli(Some(_)),_  -> fail_constapp fi

    | Csrli(None),TmConst(fi,CInt(v)) -> TmConst(fi,Csrli(Some(v)))
    | Csrli(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 lsr v2))
    | Csrli(None),_ | Csrli(Some(_)),_  -> fail_constapp fi

    | Csrai(None),TmConst(fi,CInt(v)) -> TmConst(fi,Csrai(Some(v)))
    | Csrai(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 asr v2))
    | Csrai(None),_ | Csrai(Some(_)),_  -> fail_constapp fi

    | Carity,TmConst(fi,c) -> TmConst(fi,CInt(arity c))
    | Carity,_ -> fail_constapp fi

    (* MCore intrinsic: Floating-point number constant and operations *)
    | CFloat(_),_ -> fail_constapp fi

    | Caddf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Caddf(Some(v)))
    | Caddf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 +. v2))
    | Caddf(None),_ | Caddf(Some(_)),_  -> fail_constapp fi

    | Csubf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Csubf(Some(v)))
    | Csubf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 -. v2))
    | Csubf(None),_ | Csubf(Some(_)),_  -> fail_constapp fi

    | Cmulf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cmulf(Some(v)))
    | Cmulf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 *. v2))
    | Cmulf(None),_ | Cmulf(Some(_)),_  -> fail_constapp fi

    | Cdivf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cdivf(Some(v)))
    | Cdivf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 /. v2))
    | Cdivf(None),_ | Cdivf(Some(_)),_  -> fail_constapp fi

    | Cnegf,TmConst(fi,CFloat(v)) -> TmConst(fi,CFloat((-1.0)*.v))
    | Cnegf,_ -> fail_constapp fi

    | Cltf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cltf(Some(v)))
    | Cltf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CBool(v1 < v2))
    | Cltf(None),_ | Cltf(Some(_)),_  -> fail_constapp fi

    | Cleqf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cleqf(Some(v)))
    | Cleqf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CBool(v1 <= v2))
    | Cleqf(None),_ | Cleqf(Some(_)),_  -> fail_constapp fi

    | Cgtf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cgtf(Some(v)))
    | Cgtf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CBool(v1 > v2))
    | Cgtf(None),_ | Cgtf(Some(_)),_  -> fail_constapp fi

    | Cgeqf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cgeqf(Some(v)))
    | Cgeqf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CBool(v1 >= v2))
    | Cgeqf(None),_ | Cgeqf(Some(_)),_  -> fail_constapp fi

    | Ceqf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Ceqf(Some(v)))
    | Ceqf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CBool(v1 = v2))
    | Ceqf(None),_ | Ceqf(Some(_)),_  -> fail_constapp fi

    | Cneqf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cneqf(Some(v)))
    | Cneqf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CBool(v1 <> v2))
    | Cneqf(None),_ | Cneqf(Some(_)),_  -> fail_constapp fi
    | CString2float,TmSeq(fi,s) ->
        let to_char = function
          | TmConst(_, CChar(c)) -> c
          | _ -> fail_constapp fi
        in
        let f = s
                |> Mseq.map to_char |> Mseq.to_array
                |> Ustring.from_uchars |> Ustring.to_utf8
        in
        TmConst(fi, CFloat(Float.of_string f))
    | CString2float,_ -> fail_constapp fi

    | Cexp,TmConst(fi,CFloat(v)) -> TmConst(fi,CFloat(exp(v)))
    | Cexp,_ -> fail_constapp fi

    | Cfloorfi,TmConst(fi,CFloat(v)) -> TmConst(fi,CInt(Float.floor v |> int_of_float))
    | Cfloorfi,_ -> fail_constapp fi

    | Cceilfi,TmConst(fi,CFloat(v)) -> TmConst(fi,CInt(Float.ceil v |> int_of_float))
    | Cceilfi,_ -> fail_constapp fi

    | Croundfi,TmConst(fi,CFloat(v)) -> TmConst(fi,CInt(Float.round v |> int_of_float))
    | Croundfi,_ -> fail_constapp fi

    | CInt2float,TmConst(fi,CInt(v)) -> TmConst(fi,CFloat(float_of_int v))
    | CInt2float,_ -> fail_constapp fi

    (* MCore intrinsic: characters *)
    | CChar(_),_ -> fail_constapp fi

    | CChar2int,TmConst(fi,CChar(v)) -> TmConst(fi,CInt(v))
    | CChar2int,_ -> fail_constapp fi

    | CInt2char,TmConst(fi,CInt(v)) -> TmConst(fi,CChar(v))
    | CInt2char,_ -> fail_constapp fi

    (* MCore intrinsic: sequences *)
    | CmakeSeq(None),TmConst(fi,CInt(v)) -> TmConst(fi,CmakeSeq(Some(v)))
    | CmakeSeq(Some(v1)),t -> TmSeq(tm_info t,Mseq.make v1 (fun _ -> t))
    | CmakeSeq(None),_ -> fail_constapp fi

    | Clength,TmSeq(fi,s) -> TmConst(fi,CInt(Mseq.length s))
    | Clength,_ -> fail_constapp fi

    | Cconcat(None),TmSeq(fi,s1) -> TmConst(fi,Cconcat(Some(s1)))
    | Cconcat(Some(s1)),TmSeq(fi,s2) ->
       TmSeq(fi,Mseq.concat s1 s2)
    | Cconcat(None),_ | Cconcat(Some(_)),_  -> fail_constapp fi

    | Cget(None),TmSeq(fi,s) -> TmConst(fi,Cget(Some(s)))
    | Cget(Some(s)),TmConst(_,CInt(n)) ->
       (try Mseq.get s n with _ -> raise_error fi index_out_of_bounds_in_seq_msg)
    | Cget(None),_ | Cget(Some(_)),_  -> fail_constapp fi


    | Cset(None,None),TmSeq(_,s) -> TmConst(fi,Cset(Some(s),None))
    | Cset(Some(s),None),TmConst(_,CInt(n)) -> TmConst(fi,Cset(Some(s),Some(n)))
    | Cset(Some(s),Some(n)),t ->
       let s = try Mseq.set s n t
               with _ -> raise_error fi index_out_of_bounds_in_seq_msg
       in TmSeq(fi,s)
    | Cset(_,_),_ -> fail_constapp fi


    | Ccons(None),t -> TmConst(tm_info t,Ccons(Some(t)))
    | Ccons(Some(t)),TmSeq(fi,s) -> TmSeq(fi,Mseq.cons t s)
    | Ccons(Some(_)),_  -> fail_constapp fi

    | Csnoc(None),TmSeq(_,s) -> TmConst(fi,Csnoc(Some(s)))
    | Csnoc(Some(s)),t -> TmSeq(fi,Mseq.snoc s t)
    | Csnoc(_),_ -> fail_constapp fi

    | CsplitAt(None),TmSeq(fi,s) -> TmConst(fi,CsplitAt(Some(s)))
    | CsplitAt(Some(s)),TmConst(_,CInt(n)) ->
       let t = (try Mseq.split_at s n
                with _ -> raise_error fi index_out_of_bounds_in_seq_msg)
       in tuple2record fi [TmSeq(fi,fst t);TmSeq(fi,snd t)]
    | CsplitAt(None),_ | CsplitAt(Some(_)),_  -> fail_constapp fi

    | Creverse,TmSeq(fi,s) -> TmSeq(fi,Mseq.reverse s)
    | Creverse,_ -> fail_constapp fi

    (* MCore intrinsic: random numbers *)
    | CrandIntU(None), TmConst(fi, CInt(v)) -> TmConst(fi, CrandIntU(Some(v)))
    | CrandIntU(Some(v1)), TmConst(fi, CInt(v2)) ->
       if v1 >= v2 then
         raise_error fi "Lower bound to randInt must be smaller than upper bound"
       else TmConst(fi, CInt(rand_int_u v1 v2))
    | CrandIntU(_),_ -> fail_constapp fi

    | CrandSetSeed,TmConst(fi,CInt(v)) -> rand_set_seed v; tmUnit
    | CrandSetSeed,_ -> fail_constapp fi

    (* MCore intrinsic: time *)
    | CwallTimeMs, TmRecord(fi,x) when Record.is_empty x -> TmConst(fi, CFloat(get_wall_time_ms ()))
    | CwallTimeMs, _ -> fail_constapp fi

    | CsleepMs, TmConst(fi, CInt(v)) -> sleep_ms v ; tmUnit
    | CsleepMs, _ -> fail_constapp fi

    (* MCore debug and stdio intrinsics *)
    | Cprint, TmSeq(fi,lst) ->
      !program_output (tmseq2ustring fi lst); tmUnit
    | Cprint, _ -> raise_error fi "The argument to print must be a string"

    | Cdprint, t ->
      !program_output (ustring_of_tm t); tmUnit

    | CreadLine, TmRecord(_, r) when r = Record.empty ->
      let line = try read_line () with End_of_file -> "" in
      TmSeq(fi, line |> Ustring.from_utf8 |> ustring2tmseq fi)
    | CreadLine,_ -> fail_constapp fi

    | CreadBytesAsString, TmConst(_, CInt(v)) ->
      if v < 0 then
        raise_error fi "The argument to readBytesAsString must be a positive integer"
      else
        let str = try BatIO.nread BatIO.stdin v with BatIO.No_more_input -> "" in
        let ustr =
          try Ustring.from_utf8 str
          with Invalid_argument _ -> raise_error fi "Received invalid UTF-8"
        in
        tuple2record fi
          [ TmSeq(fi, ustring2tmseq fi ustr)
          ; TmConst(fi,CInt(String.length str))
          ]
    | CreadBytesAsString,_ -> fail_constapp fi

    | CreadFile,TmSeq(fi,lst) ->
       TmSeq(fi,Ustring.read_file (Ustring.to_utf8 (tmseq2ustring fi lst))
                       |> (ustring2tmseq fi))
    | CreadFile,_ -> fail_constapp fi

    | CwriteFile(None),TmSeq(fi,l) -> TmConst(fi,CwriteFile(Some(tmseq2ustring fi l)))
    | CwriteFile(Some(fname)),TmSeq(fi,lst) ->
        Ustring.write_file (Ustring.to_utf8 fname) (tmseq2ustring fi lst); tmUnit
    | CwriteFile(None),_ | CwriteFile(Some(_)),_  -> fail_constapp fi

    | CfileExists,TmSeq(fi,lst) ->
        TmConst(fi,CBool(Sys.file_exists (Ustring.to_utf8 (tmseq2ustring fi lst))))
    | CfileExists,_ -> fail_constapp fi

    | CdeleteFile,TmSeq(fi,lst) ->
        Sys.remove (Ustring.to_utf8 (tmseq2ustring fi lst)); tmUnit
    | CdeleteFile,_ -> fail_constapp fi

    | Cerror, TmSeq(fiseq,lst) -> tmseq2ustring fiseq lst |> Ustring.to_utf8 |> raise_error fi
    | Cerror,_ -> fail_constapp fi
    | Cexit, TmConst(_,CInt(x)) -> exit x
    | Cexit,_ -> fail_constapp fi
    | CSymb(_),_ -> fail_constapp fi
    | Cgensym, TmRecord(fi,x) when Record.is_empty x -> TmConst(fi, CSymb(gen_symid()))
    | Cgensym,_ -> fail_constapp fi
    | Ceqs(None), TmConst(fi,CSymb(id)) -> TmConst(fi, Ceqs(Some(id)))
    | Ceqs(Some(id)), TmConst(fi,CSymb(id')) -> TmConst(fi, CBool(id == id'))
    | Ceqs(_),_ -> fail_constapp fi
    | CSym2hash, TmConst(fi,CSymb(id)) -> TmConst(fi, CInt(id))
    | CSym2hash,_ -> fail_constapp fi

    | CPy v, t -> Pyffi.delta eval env fi v t

    | CExt v, t -> Ext.delta eval env fi v t


(* Debug function used in the eval function *)
let debug_eval env t =
  if !enable_debug_eval_tm  || !enable_debug_eval_env then (
    printf "-- eval step -- \n";
    let env_str = if !enable_debug_eval_env then
        us"Environment:\n" ^. (ustring_of_env ~margin:80 env) ^. us"\n" else us"" in
    let tm_str = if !enable_debug_eval_tm then
        us"Term:\n" ^. (ustring_of_tm ~margin:80 t) ^. us"\n" else us"" in
    uprint_endline (env_str ^. tm_str))
  else ()

(* Print out error message when a unit test fails *)
let unittest_failed fi t1 t2=
  uprint_endline
    (match fi with
    | Info(_,l1,_,_,_) ->
      us"\n ** Unit test FAILED on line " ^.
      us(string_of_int l1)
      ^.  us" **\n    LHS: " ^. (ustring_of_tm t1)
      ^.  us"\n    RHS: "    ^. (ustring_of_tm t2)
    | NoInfo -> us"Unit test FAILED ")


(* Check if two value terms are equal *)
let rec val_equal v1 v2 =
  match v1,v2 with
  | TmSeq(_,s1), TmSeq(_,s2) -> Mseq.equal val_equal s1 s2
  | TmRecord(_,r1), TmRecord(_,r2) -> Record.equal (fun t1 t2 -> val_equal t1 t2) r1 r2
  | TmConst(_,c1),TmConst(_,c2) -> c1 = c2
  | TmConapp(_,_,sym1,v1),TmConapp(_,_,sym2,v2) -> sym1 = sym2 && val_equal v1 v2
  | _ -> false

let findsym fi id env =
  try List.assoc id env
  with Not_found ->
    let (x,kindstr) = match id with
      | IdVar(x)   -> (x,"variable")
      | IdCon(x)   -> (x,"constructor")
      | IdType(x)  -> (x,"identifier")
      | IdLabel(x) -> (x,"label")
    in raise_error fi ("Unknown " ^ kindstr ^ " '" ^ string_of_sid x ^ "'")

(* Add symbol associations between lambdas, patterns, and variables. The function also
   constructs TmConapp terms from the combination of variables and function applications.  *)
let rec symbolize (env : (ident * sym) list) (t : tm) =
  (* add_name is only called in sPat and it reuses previously generated symbols.
   * This is imperative for or-patterns, since both branches should give the same symbols,
   * e.g., [a] | [a, _] should give the same symbol to both "a"s.
   * However, this also has an effect on what happens when the same name is bound multiple times
   * in a pattern in other cases. In particular, this means that, e.g., the pattern
   * [a, a] assigns the same symbol to both "a"s, which may or may not be desirable. Which
   * introduced binding gets used then depends on what try_match does for the pattern. *)
  let add_name (x: ident) (patEnv: (ident * int) list) =
    match List.assoc_opt x patEnv with
    | Some s -> (patEnv, s)
    | None -> let s = gensym() in ((x,s)::patEnv, s) in
  let rec s_pat_sequence patEnv pats =
    Mseq.fold_right
      (fun p (patEnv, ps) -> let (patEnv, p) = sPat patEnv p in (patEnv, Mseq.cons p ps))
      pats
      (patEnv, Mseq.empty)
  and sPat (patEnv : (ident * int) list) = function
    | PatNamed(fi,NameStr(x,_)) -> let (patEnv, s) = add_name (IdVar(sid_of_ustring x)) patEnv
                                   in (patEnv, PatNamed(fi,NameStr(x,s)))
    | PatNamed(_,NameWildcard) as pat -> (patEnv, pat)
    | PatSeqTot(fi, pats) ->
       let (patEnv, pats) = s_pat_sequence patEnv pats
       in (patEnv, PatSeqTot(fi, pats))
    | PatSeqEdg(fi, l, x, r) ->
       let (patEnv, l) = s_pat_sequence patEnv l in
       let (patEnv, x) = match x with
         | NameWildcard -> (patEnv, NameWildcard)
         | NameStr(x, _) ->
            let (patEnv, s) = add_name (IdVar (sid_of_ustring x)) patEnv
            in (patEnv, NameStr(x, s)) in
       let (patEnv, r) = s_pat_sequence patEnv r
       in (patEnv, PatSeqEdg(fi, l, x, r))
    | PatRecord(fi, pats) ->
       let patEnv = ref patEnv in
       let pats = Record.map (fun p -> let (patEnv', p) = sPat !patEnv p in patEnv := patEnv'; p) pats
       in (!patEnv, PatRecord(fi, pats))
    | PatCon(fi,x,_,p) ->
       let s = findsym fi (IdCon(sid_of_ustring x)) env in
       let (patEnv, p) = sPat patEnv p
       in (patEnv,PatCon(fi,x,s,p))
    | PatInt _ as p -> (patEnv,p)
    | PatChar _ as p -> (patEnv,p)
    | PatBool _ as p -> (patEnv,p)
    | PatAnd(fi, l, r) ->
       let (patEnv, l) = sPat patEnv l in
       let (patEnv, r) = sPat patEnv r
       in (patEnv, PatAnd(fi, l, r))
    | PatOr(fi, l, r) ->
       let (patEnv, l) = sPat patEnv l in
       let (patEnv, r) = sPat patEnv r
       in (patEnv, PatOr(fi, l, r))
    | PatNot(fi, p) ->
       let (_, p) = sPat patEnv p in
        (* NOTE(vipa): new names in a not-pattern do not matter since they will
         * never bind (it should probably be an error to bind a name inside a
         * not-pattern, but we're not doing that kind of static checks yet.
         * Note that we still need to run symbolize though, constructors must
         * refer to the right symbol. *)
       (patEnv, PatNot(fi, p))
  in
  match t with
  | TmVar(fi,x,_) -> TmVar(fi,x,findsym fi (IdVar(sid_of_ustring x)) env)
  | TmLam(fi,x,_,ty,t1) -> let s = gensym() in TmLam(fi,x,s,ty,symbolize ((IdVar(sid_of_ustring x),s)::env) t1)
  | TmClos(_,_,_,_,_,_) -> failwith "Closures should not be available."
  | TmLet(fi,x,_,t1,t2) -> let s = gensym() in TmLet(fi,x,s,symbolize env t1,symbolize ((IdVar(sid_of_ustring x),s)::env) t2)
  | TmRecLets(fi,lst,tm) ->
     let env2 = List.fold_left (fun env (_,x,_,_) -> let s = gensym() in (IdVar(sid_of_ustring x),s)::env) env lst in
     TmRecLets(fi,List.map (fun (fi,x,_,t) -> (fi,x,findsym fi (IdVar(sid_of_ustring x)) env2, symbolize env2 t))
       lst, symbolize env2 tm)
  | TmApp(fi,t1,t2) -> TmApp(fi,symbolize env t1,symbolize env t2)
  | TmConst(_,_) -> t
  | TmFix(_) -> t
  | TmSeq(fi,tms) -> TmSeq(fi,Mseq.map (symbolize env) tms)
  | TmRecord(fi,r) -> TmRecord(fi,Record.map (symbolize env) r)
  | TmRecordUpdate(fi,t1,l,t2) -> TmRecordUpdate(fi,symbolize env t1,l,symbolize env t2)
  | TmCondef(fi,x,_,ty,t) -> let s = gensym() in TmCondef(fi,x,s,ty,symbolize ((IdCon(sid_of_ustring x),s)::env) t)
  | TmConapp(fi,x,_,t) -> TmConapp(fi,x,findsym fi (IdCon(sid_of_ustring x)) env,symbolize env t)
  | TmMatch(fi,t1,p,t2,t3) ->
     let (matchedEnv, p) = sPat [] p in
     TmMatch(fi,symbolize env t1,p,symbolize (matchedEnv @ env) t2,symbolize env t3)
  | TmUse(fi,l,t) -> TmUse(fi,l,symbolize env t)
  | TmUtest(fi,t1,t2,tnext)
    -> TmUtest(fi,symbolize env t1,symbolize env t2,symbolize env tnext)
  | TmNever(_) -> t

(* Same as symbolize, but records all toplevel definitions and returns them
 along with the symbolized term *)
let rec symbolize_toplevel (env : (ident * sym) list) = function
  | TmLet(fi,x,_,t1,t2) ->
    let s = gensym() in
    let (new_env, new_t2) = symbolize_toplevel ((IdVar(sid_of_ustring x),s)::env) t2 in
    (new_env, TmLet(fi,x,s,symbolize env t1,new_t2))
  | TmRecLets(fi,lst,tm) ->
    let env2 = List.fold_left (fun env (_,x,_,_) -> let s = gensym() in (IdVar(sid_of_ustring x),s)::env) env lst in
    let (new_env, new_tm) = symbolize_toplevel env2 tm in
    (new_env, TmRecLets(fi,List.map (fun (fi,x,_,t) -> (fi,x,findsym fi (IdVar(sid_of_ustring x)) env2, symbolize env2 t))
       lst, new_tm))
  | TmCondef(fi,x,_,ty,t) ->
    let s = gensym() in
    let (new_env, new_t2) = symbolize_toplevel ((IdCon(sid_of_ustring x),s)::env) t in
    (new_env, TmCondef(fi,x,s,ty,new_t2))
  | t -> (env, symbolize env t)

let rec try_match env value pat =
  let go v p env = Option.bind env (fun env -> try_match env v p) in
  let split_nth_or_double_empty n s =
    if Mseq.length s == 0 then (Mseq.empty, Mseq.empty)
    else Mseq.split_at s n
  in
  let bind fi n tms env =
    match n with
    | NameStr(_,s) -> Option.bind env (fun env -> Some((s,TmSeq(fi,tms))::env))
    | NameWildcard -> Option.bind env (fun env -> Some(env))
  in
  match pat with
  | PatNamed(_,NameStr(_,s)) -> Some((s,value)::env)
  | PatNamed(_,NameWildcard)-> Some(env)
  | PatSeqTot(_, pats) ->
     let npats = Mseq.length pats in
     (match value with
      | TmSeq(_, vs) when npats = Mseq.length vs ->
         Mseq.fold_right2 go vs pats (Some env)
      | _ -> None)
  | PatSeqEdg(_, l, x, r) ->
     let npre = Mseq.length l in
     let npost = Mseq.length r in
     (match value with
      | TmSeq(fi, vs) when npre + npost <= Mseq.length vs ->
         let (pre, vs) = split_nth_or_double_empty npre vs in
         let (vs, post) = split_nth_or_double_empty (Mseq.length vs - npost) vs
         in Mseq.fold_right2 go post r (Some env)
            |> bind fi x vs
            |> Mseq.fold_right2 go pre l
      | _ -> None)
  | PatRecord(_, pats) ->
     (match value with
      | TmRecord(_, vs) ->
         let merge_f _ v p = match v, p with
           | None, None -> None
           | Some _, None -> None
           | Some v, Some p -> Some (go v p)
           | None, Some _ -> Some (fun _ -> None)
         in Record.merge merge_f vs pats
            |> (fun merged -> Record.fold (fun _ f env -> f env) merged (Some env))
      | _ -> None)
  | PatCon(_,_,s1,p) ->
     (match value with
      | TmConapp(_,_,s2,v) when s1 = s2 -> try_match env v p
      | _ -> None)
  | PatInt(_, i) ->
     (match value with
      | TmConst(_,CInt i2) when i = i2 -> Some env
      | _ -> None)
  | PatChar(_, c) ->
     (match value with
      | TmConst(_,CChar c2) when c = c2 -> Some env
      | _ -> None)
  | PatBool(_, b) ->
     (match value with
      | TmConst(_,CBool b2) when b = b2 -> Some env
      | _ -> None)
  | PatAnd(_, l, r) -> go value r (Some env) |> go value l
  | PatOr(_, l, r) ->
     (match try_match env value l with
      | Some env -> Some env
      | None -> try_match env value r)
  | PatNot(_, p) ->
     (match try_match env value p with
      | Some _ -> None
      | None -> Some env)


(* Main evaluation loop of a term. Evaluates using big-step semantics *)
let rec eval (env : (sym * tm) list) (t : tm) =
  debug_eval env t;
  match t with
  (* Variables using symbol bindings. Need to evaluate because fix point. *)
  | TmVar(_,_,s) -> eval env (List.assoc s env)
  (* Lambda and closure conversions *)
  | TmLam(fi,x,s,ty,t1) -> TmClos(fi,x,s,ty,t1,lazy env)
  | TmClos(_,_,_,_,_,_) -> t
  (* Let *)
  | TmLet(_,_,s,t1,t2) -> eval ((s,eval env t1)::env) t2
  (* Recursive lets *)
  | TmRecLets(_,lst,t2) ->
     let rec env' = lazy
       (let wraplambda = function
          | TmLam(fi,x,s,ty,t1) -> TmClos(fi,x,s,ty,t1,env')
          | tm -> raise_error (tm_info tm) "Right-hand side of recursive let must be a lambda"
        in List.fold_left (fun env (_, _, s, rhs) -> (s, wraplambda rhs) :: env) env lst)
     in eval (Lazy.force env') (t2)
  (* Application *)
  | TmApp(fiapp,t1,t2) ->
      (match eval env t1 with
       (* Closure application *)
       | TmClos(_,_,s,_,t3,env2) -> eval ((s,eval env t2)::Lazy.force env2) t3
       (* Constant application using the delta function *)
       | TmConst(_,c) -> delta eval env fiapp c (eval env t2)
       (* Fix *)
       | TmFix(_) ->
         (match eval env t2 with
         | TmClos(fi,_,s,_,t3,env2) as tt -> eval ((s,TmApp(fi,TmFix(fi),tt))::Lazy.force env2) t3
         | _ -> raise_error (tm_info t1) "Incorrect CFix")
       | f -> raise_error fiapp ("Incorrect application. This is not a function: "
                                 ^ Ustring.to_utf8
                                   (ustring_of_tm f)))
  (* Constant and fix *)
  | TmConst(_,_) | TmFix(_) -> t
  (* Sequences *)
  | TmSeq(fi,tms) -> TmSeq(fi,Mseq.map (eval env) tms)
  (* Records *)
  | TmRecord(fi,tms) -> TmRecord(fi,Record.map (eval env) tms)
  | TmRecordUpdate(fi,t1,l,t2) ->
     (match eval env t1 with
      | TmRecord(fi,r) ->
         if Record.mem l r
         then TmRecord(fi, Record.add l (eval env t2) r)
         else raise_error fi ("No label '" ^ Ustring.to_utf8 l ^
                                        "' in record " ^ Ustring.to_utf8
                                (ustring_of_tm (TmRecord(fi,r))))
      | v ->
         raise_error fi ("Cannot update the term. The term is not a record: "
                         ^ Ustring.to_utf8 (ustring_of_tm v)))
  (* Data constructors and match *)
  | TmCondef(_,_,_,_,t) -> eval env t
  | TmConapp(fi,x,s,t) -> TmConapp(fi,x,s,eval env t)
  | TmMatch(_,t1,p,t2,t3) ->
     (match try_match env (eval env t1) p with
      | Some env -> eval env t2
      | None -> eval env t3)
  | TmUse(fi,_,_) -> raise_error fi "A 'use' of a language was not desugared"
  (* Unit testing *)
  | TmUtest(fi,t1,t2,tnext) ->
    if !utest then begin
      let (v1,v2) = ((eval env t1),(eval env t2)) in
        if val_equal v1 v2 then
         (printf "."; utest_ok := !utest_ok + 1)
       else (
        unittest_failed fi v1 v2;
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
     end;
    eval env tnext
  | TmNever(fi) -> raise_error fi "Reached a never term, which should be impossible in a well-typed program."

(* Same as eval, but records all toplevel definitions and returns them along
  with the evaluated result *)
let rec eval_toplevel (env : (sym * tm) list) = function
  | TmLet(_,_,s,t1,t2) -> eval_toplevel ((s,eval env t1)::env) t2
  | TmRecLets(_,lst,t2) ->
     let rec env' = lazy
       (let wraplambda = function
          | TmLam(fi,x,s,ty,t1) -> TmClos(fi,x,s,ty,t1,env')
          | tm -> raise_error (tm_info tm) "Right-hand side of recursive let must be a lambda"
        in List.fold_left (fun env (_, _, s, rhs) -> (s, wraplambda rhs) :: env) env lst)
     in eval_toplevel (Lazy.force env') t2
  | TmCondef(_,_,_,_,t) -> eval_toplevel env t
  | t -> (env, eval env t)
