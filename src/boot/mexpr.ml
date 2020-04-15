
(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
*)

open Ustring.Op
open Msg
open Ast
open Pprint
open Printf

(* Mapping between named builtin functions (intrinsics) and the
   correspond constants *)
let builtin =
  let f c = TmConst(NoInfo,c) in
  [("unit",f(Cunit));
   ("not",f(Cnot));("and",f(Cand(None)));("or",f(Cor(None)));
   ("addi",f(Caddi(None)));("subi",f(Csubi(None)));("muli",f(Cmuli(None)));
   ("divi",f(Cdivi(None)));("modi",f(Cmodi(None)));("negi",f(Cnegi));
   ("lti",f(Clti(None)));("leqi",f(Cleqi(None)));("gti",f(Cgti(None)));("geqi",f(Cgeqi(None)));
   ("eqi",f(Ceqi(None)));("neqi",f(Cneqi(None)));
   ("slli",f(Cslli(None)));("srli",f(Csrli(None)));("srai",f(Csrai(None)));
   ("arity",f(Carity));
   ("addf",f(Caddf(None)));("subf",f(Csubf(None)));("mulf",f(Cmulf(None)));
   ("divf",f(Cdivf(None)));("negf",f(Cnegf));
   ("ltf",f(Cltf(None)));("leqf",f(Cleqf(None)));("gtf",f(Cgtf(None)));("geqf",f(Cgeqf(None)));
   ("eqf",f(Ceqf(None)));("neqf",f(Cneqf(None)));
   ("floorfi", f(Cfloorfi)); ("ceilfi", f(Cceilfi)); ("roundfi", f(Croundfi));
   ("int2float", f(CInt2float)); ("string2float", f(CString2float));
   ("char2int",f(CChar2int));("int2char",f(CInt2char));
   ("makeSeq",f(CmakeSeq(None))); ("length",f(Clength));("concat",f(Cconcat(None)));
   ("get",f(Cget(None)));("set",f(Cset(None,None)));
   ("cons",f(Ccons(None)));("snoc",f(Csnoc(None)));
   ("splitAt",f(CsplitAt(None)));("reverse",f(Creverse));
   ("print",f(Cprint));("dprint",f(Cdprint));
   ("argv",TmSeq(NoInfo,Sys.argv
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
   ("debugShow", f(CdebugShow));
   ("eqs", f(Ceqs(None))); ("gensym", f(Cgensym))
  ]
  (* Append external functions TODO: Should not be part of core language *)
  @ Ext.externals

(* Returns the number of expected arguments of a constant *)
let arity = function
  (* MCore intrinsic: no operation *)
  | Cunit       -> 0
  (* MCore intrinsic: Boolean constant and operations *)
  | CBool(_)    -> 0
  | Cnot        -> 1
  | Cand(None)  -> 2  | Cand(Some(_))  -> 1
  | Cor(None)   -> 2  | Cor(Some(_))   -> 1
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
  (* MCore intrinsic: records *)
  | CRecord(_)        -> 0
  (* MCore debug and I/O intrinsics *)
  | Cprint            -> 1
  | Cdprint           -> 1
  | CreadFile         -> 1
  | CwriteFile(None)  -> 2 | CwriteFile(Some(_)) -> 1
  | CfileExists       -> 1
  | CdeleteFile       -> 1
  | Cerror            -> 1
  | CdebugShow        -> 1
  (* MCore symbols *)
  | CSymb(_)      -> 0
  | Cgensym      -> 1
  | Ceqs(None)    -> 2
  | Ceqs(Some(_)) -> 1
  (* External functions TODO: Should not be bart of core language *)
  | CExt v            -> Ext.arity v


(* API for generating unique symbol ids *)
let symid = ref 0
let gen_symid _ =
  symid := !symid + 1;
  !symid

let fail_constapp f v fi = raise_error fi ("Incorrect application. function: "
                                         ^ Ustring.to_utf8
                                           (ustring_of_const f)
                                         ^ " value: "
                                         ^ Ustring.to_utf8
                                           (ustring_of_tm v))

(* Evaluates a constant application. This is the standard delta function
   delta(c,v) with the exception that it returns an expression and not
   a value. This is why the returned value is evaluated in the eval() function.
   The reason for this is that if-expressions return expressions
   and not values. *)
let delta eval env fi c v  =
    let index_out_of_bounds_in_seq_msg = "Out of bounds access in sequence" in
    let fail_constapp = fail_constapp c v in
    match c,v with
    (* MCore intrinsic: unit - no operation *)
    | Cunit,_ -> fail_constapp fi
    (* MCore boolean intrinsics *)
    | CBool(_),_ -> fail_constapp fi

    | Cnot,TmConst(fi,CBool(v)) -> TmConst(fi,CBool(not v))
    | Cnot,_ -> fail_constapp fi

    | Cand(None),TmConst(fi,CBool(v)) -> TmConst(fi,Cand(Some(v)))
    | Cand(Some(v1)),TmConst(fi,CBool(v2)) -> TmConst(fi,CBool(v1 && v2))
    | Cand(None),_ | Cand(Some(_)),_  -> fail_constapp fi

    | Cor(None),TmConst(fi,CBool(v)) -> TmConst(fi,Cor(Some(v)))
    | Cor(Some(v1)),TmConst(fi,CBool(v2)) -> TmConst(fi,CBool(v1 || v2))
    | Cor(None),_ | Cor(Some(_)),_  -> fail_constapp fi

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
       in TmTuple(fi,[TmSeq(fi,fst t);TmSeq(fi,snd t)])
    | CsplitAt(None),_ | CsplitAt(Some(_)),_  -> fail_constapp fi

    | Creverse,TmSeq(fi,s) -> TmSeq(fi,Mseq.reverse s)
    | Creverse,_ -> fail_constapp fi

    (* MCore intrinsic: records *)
    | CRecord(_),_ -> fail_constapp fi

    (* MCore debug and stdio intrinsics *)
    | Cprint, TmSeq(fi,lst) ->
       uprint_string (tmseq2ustring fi lst); TmConst(NoInfo,Cunit)
    | Cprint, _ -> raise_error fi "The argument to print must be a string"

    | Cdprint, t ->
      uprint_string (ustring_of_tm t);
      TmConst(NoInfo,Cunit)

    | CreadFile,TmSeq(fi,lst) ->
       TmSeq(fi,Ustring.read_file (Ustring.to_utf8 (tmseq2ustring fi lst))
                       |> (ustring2tmseq fi))
    | CreadFile,_ -> fail_constapp fi

    | CwriteFile(None),TmSeq(fi,l) -> TmConst(fi,CwriteFile(Some(tmseq2ustring fi l)))
    | CwriteFile(Some(fname)),TmSeq(fi,lst) ->
        Ustring.write_file (Ustring.to_utf8 fname) (tmseq2ustring fi lst); TmConst(NoInfo,Cunit)
    | CwriteFile(None),_ | CwriteFile(Some(_)),_  -> fail_constapp fi

    | CfileExists,TmSeq(fi,lst) ->
        TmConst(fi,CBool(Sys.file_exists (Ustring.to_utf8 (tmseq2ustring fi lst))))
    | CfileExists,_ -> fail_constapp fi

    | CdeleteFile,TmSeq(fi,lst) ->
        Sys.remove (Ustring.to_utf8 (tmseq2ustring fi lst)); TmConst(NoInfo,Cunit)
    | CdeleteFile,_ -> fail_constapp fi

    | Cerror, TmSeq(fiseq,lst) ->
       (let prefix = match fi with
                     | Info(filename,l1,_,_,_) ->
                       filename ^. us":" ^. (ustring_of_int l1) ^. us": "
                     | NoInfo -> us""
        in uprint_endline (prefix ^. us"ERROR: " ^. (tmseq2ustring fiseq lst)); exit 1)
    | Cerror,_ -> fail_constapp fi
    | CdebugShow,t ->
       uprint_endline ((us"EXPR: ") ^. (ustring_of_tm t));
       TmConst(NoInfo,Cunit)

    | CSymb(_),_ -> fail_constapp fi
    | Cgensym, TmConst(fi, Cunit) -> TmConst(fi, CSymb(gen_symid()))
    | Cgensym,_ -> fail_constapp fi
    | Ceqs(None), TmConst(fi,CSymb(id)) -> TmConst(fi, Ceqs(Some(id)))
    | Ceqs(Some(id)), TmConst(fi,CSymb(id')) -> TmConst(fi, CBool(id == id'))
    | Ceqs(_),_ -> fail_constapp fi

    | CExt v, t -> Ext.delta eval env fi v t


(* Debug function used in the eval function *)
let debug_eval env t =
  if enable_debug_eval then
    (printf "\n-- eval -- \n";
     uprint_endline (ustring_of_tm t);
     if enable_debug_eval_env then
        uprint_endline (ustring_of_env env))
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
  | TmConst(_,CRecord(r1)), TmConst(_,CRecord(r2)) ->
     Record.equal val_equal r1 r2
  | TmConst(_,c1),TmConst(_,c2) -> c1 = c2
  | TmTuple(_,tms1),TmTuple(_,tms2) ->
     List.length tms1 = List.length tms2 &&
     List.for_all (fun (x,y) -> val_equal x y) (List.combine tms1 tms2)
  | TmConsym(_,_,sym1,None),TmConsym(_,_,sym2,None) ->sym1 = sym2
  | TmConsym(_,_,sym1,Some(v1)),TmConsym(_,_,sym2,Some(v2)) -> sym1 = sym2 && val_equal v1 v2
  | _ -> false


(* Convert a term into de Bruijn indices. *)
let rec debruijn env t =
  let rec find fi env n x =
    (match env with
     | VarTm(y)::ee -> if y =. x then n else find fi ee (n+1) x
     | [] -> raise_error fi ("Unknown variable '" ^ Ustring.to_utf8 x ^ "'")) in
  let rec dbPat env = function
    | PatNamed(_,NameStr(x)) as pat -> (VarTm(x)::env, pat)
    | PatNamed(_,NameWildcard) as pat -> (env, pat)
    | PatSeq(fi,ps,seqMP) ->
       let go p (env,ps) = let (env,p) = dbPat env p in (env,Mseq.cons p ps) in
       let (env,ps) = Mseq.fold_right go ps (env,Mseq.empty) in
       let env = (match seqMP with
       | SeqMatchPrefix(NameStr(x)) | SeqMatchPostfix(NameStr(x)) -> VarTm(x)::env
       | SeqMatchPrefix(NameWildcard) | SeqMatchPostfix(NameWildcard) | SeqMatchTotal -> env) in
       (env,PatSeq(fi,ps,seqMP))
    | PatTuple(fi,ps) -> (* NOTE: this causes patterns to introduce names right-to-left, which will cause errors if a later pattern binds a name that is seen as a constructor in a pattern to the left *)
       let go p (env,ps) = let (env,p) = dbPat env p in (env,p::ps) in
       let (env,ps) = List.fold_right go ps (env,[])
       in (env,PatTuple(fi,ps))
    | PatCon(fi,cx,_,p) ->
       let cxId = find fi env 0 cx in
       let (env, p) = dbPat env p
       in (env,PatCon(fi,cx,cxId,p))
    | PatInt _ as p -> (env,p)
    | PatChar _ as p -> (env,p)
    | PatBool _ as p -> (env,p)
    | PatUnit _ as p -> (env,p)
  in
  match t with
  | TmVar(fi,x,_) -> TmVar(fi,x,find fi env 0 x)
  | TmLam(fi,x,ty,t1) -> TmLam(fi,x,ty,debruijn (VarTm(x)::env) t1)
  | TmClos(_,_,_,_,_) -> failwith "Closures should not be available."
  | TmLet(fi,x,t1,t2) -> TmLet(fi,x,debruijn env t1,debruijn (VarTm(x)::env) t2)
  | TmRecLets(fi,lst,tm) ->
     let env2 = List.fold_left (fun env (_,x,_) -> VarTm(x)::env) env lst in
     TmRecLets(fi,List.map (fun (fi,s,t) -> (fi,s, debruijn env2 t)) lst, debruijn env2 tm)
  | TmApp(fi,t1,t2) -> TmApp(fi,debruijn env t1,debruijn env t2)
  | TmConst(_,_) -> t
  | TmFix(_) -> t
  | TmSeq(fi,tms) -> TmSeq(fi,Mseq.map (debruijn env) tms)
  | TmTuple(fi,tms) -> TmTuple(fi,List.map (debruijn env) tms)
  | TmRecord(fi, r) -> TmRecord(fi,List.map (function (l, t) -> (l, debruijn env t)) r)
  | TmProj(fi,t,l) -> TmProj(fi,debruijn env t,l)
  | TmRecordUpdate(fi,t1,l,t2) -> TmRecordUpdate(fi,debruijn env t1,l,debruijn env t2)
  | TmCondef(fi,x,ty,t) -> TmCondef(fi,x,ty,debruijn (VarTm(x)::env) t)
  | TmConsym(fi,x,sym,tmop) ->
     TmConsym(fi,x,sym,match tmop with | None -> None | Some(t) -> Some(debruijn env t))
  | TmMatch(fi,t1,p,t2,t3) ->
     let (matchedEnv, p) = dbPat env p in
     TmMatch(fi,debruijn env t1,p,debruijn matchedEnv t2,debruijn env t3)
  | TmUse(fi,l,t) -> TmUse(fi,l,debruijn env t)
  | TmUtest(fi,t1,t2,tnext)
     -> TmUtest(fi,debruijn env t1,debruijn env t2,debruijn env tnext)


let rec tryMatch env value pat =
  let go v p env = Option.bind env (fun env -> tryMatch env v p) in
  let splitNthOrDoubleEmpty n s =
    if Mseq.length s == 0 then (Mseq.empty, Mseq.empty)
    else Mseq.split_at s n
  in
  let bind fi tms env =
    Option.bind env (fun env -> Some(TmSeq(fi,tms)::env))
  in
  match pat with
  | PatNamed(_,NameStr(_)) -> Some(value::env)
  | PatNamed(_,NameWildcard)-> Some(env)
  | PatSeq(_,pats,seqMP) ->
     let npats = Mseq.length pats in
     (match value,seqMP with
      | TmSeq(fi,vs),SeqMatchPrefix(_) when npats <= Mseq.length vs ->
         let (pre,post) = vs |> splitNthOrDoubleEmpty npats in
         Mseq.fold_right2 go pre pats (Some env) |> bind fi post
      | TmSeq(fi,vs),SeqMatchPostfix(_) when npats <= Mseq.length vs ->
         let (pre,post) =
           vs |> splitNthOrDoubleEmpty (Mseq.length vs - npats)
         in
         Mseq.fold_right2 go post pats (Some env) |> bind fi pre
      | TmSeq(_,vs),SeqMatchTotal when npats == Mseq.length vs ->
         Mseq.fold_right2 go vs pats (Some env)
      | _ -> None)
  | PatTuple(_,pats) ->
    (match value with
      | TmTuple(_,vs) when List.length pats = List.length vs ->
         List.fold_right2 go vs pats (Some env)
      | _ -> None)
  | PatCon(_,_,cxId,p) ->
     (match value, List.nth env cxId with
      | TmConsym(_,_,sym1,Some v), TmConsym(_,_,sym2,_)
           when sym1 = sym2 -> tryMatch env v p
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
  | PatUnit _ ->
     (match value with
      | TmConst(_, Cunit) -> Some env
      | _ -> None)


(* Main evaluation loop of a term. Evaluates using big-step semantics *)
let rec eval env t =
  debug_eval env t;
  match t with
  (* Variables using debruijn indices. Need to evaluate because fix point. *)
  | TmVar(_,_,n) -> eval env (List.nth env n)
  (* Lambda and closure conversions *)
  | TmLam(fi,x,ty,t1) -> TmClos(fi,x,ty,t1,lazy env)
  | TmClos(_,_,_,_,_) -> t
  (* Let *)
  | TmLet(_,_,t1,t2) -> eval ((eval env t1)::env) t2
  (* Recursive lets *)
  | TmRecLets(_,lst,t2) ->
     let rec env' = lazy
       (let wraplambda = function
          | TmLam(fi,x,ty,t1) -> TmClos(fi,x,ty,t1,env')
          | tm -> raise_error (tm_info tm) "Right-hand side of recursive let must be a lambda"
        in List.fold_left (fun env (_, _, rhs) -> wraplambda rhs :: env) env lst)
     in eval (Lazy.force env') (t2)
  (* Application *)
  | TmApp(fiapp,t1,t2) ->
      (match eval env t1 with
       (* Closure application *)
       | TmClos(_,_,_,t3,env2) -> eval ((eval env t2)::Lazy.force env2) t3
       (* Constant application using the delta function *)
       | TmConst(_,c) -> delta eval env fiapp c (eval env t2)
       (* Constructor application *)
       | TmConsym(fi,x,sym,None) -> TmConsym(fi,x,sym,Some(eval env t2))
       | TmConsym(_,x,_,Some(_)) ->
          raise_error fiapp ("Cannot apply constructor '" ^ Ustring.to_utf8 x ^
                               "' more than once")
       (* Fix *)
       | TmFix(_) ->
         (match eval env t2 with
         | TmClos(fi,_,_,t3,env2) as tt -> eval ((TmApp(fi,TmFix(fi),tt))::Lazy.force env2) t3
         | _ -> raise_error (tm_info t1) "Incorrect CFix")
       | f -> raise_error fiapp ("Incorrect application. This is not a function: "
                                 ^ Ustring.to_utf8
                                   (ustring_of_tm f)))
  (* Constant and fix *)
  | TmConst(_,_) | TmFix(_) -> t
  (* Sequences *)
  | TmSeq(fi,tms) -> TmSeq(fi,Mseq.map (eval env) tms)
  (* Records *)
  | TmRecord(fi,r) ->
     let add_mapping m = function
       | (l, t) -> Record.add l (eval env t) m
    in
     TmConst(fi,CRecord(List.fold_left add_mapping Record.empty r))
  | TmProj(fi,t,l) ->
     (match l with
      | LabIdx i ->
         (match eval env t with
          | TmTuple(fi, tms) ->
             (try List.nth tms i
              with _ -> raise_error fi "Tuple projection is out of bounds.")
          | v ->
             raise_error fi ("Cannot project from term. The term is not a tuple: "
                             ^ Ustring.to_utf8 (ustring_of_tm v)))
      | LabStr s ->
         (match eval env t with
          | TmConst(fi, CRecord(r)) ->
             (try Record.find s r
              with _ -> raise_error fi ("No label '" ^ Ustring.to_utf8 s ^
                                        "' in record " ^ Ustring.to_utf8
                                          (ustring_of_const
                                             (CRecord(r)))))
          | v ->
             raise_error fi ("Cannot project from term. The term is not a record: "
                             ^ Ustring.to_utf8
                               (ustring_of_tm v))))
  | TmRecordUpdate(fi,t1,l,t2) ->
     (match eval env t1 with
      | TmConst(fi, CRecord(r)) ->
         if Record.mem l r
         then TmConst(fi, CRecord(Record.add l (eval env t2) r))
         else raise_error fi ("No label '" ^ Ustring.to_utf8 l ^
                                        "' in record " ^ Ustring.to_utf8
                                (ustring_of_const (CRecord r)))
      | v ->
         raise_error fi ("Cannot update the term. The term is not a record: "
                         ^ Ustring.to_utf8 (ustring_of_tm v)))
  (* Tuples *)
  | TmTuple(fi,tms) -> TmTuple(fi,List.map (eval env) tms)
  (* Data constructors and match *)
  | TmCondef(fi,x,_,t) -> eval ((gencon fi x)::env) t
  | TmConsym(_,_,_,_) as tm -> tm
  | TmMatch(_,t1,p,t2,t3) ->
     (match tryMatch env (eval env t1) p with
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
