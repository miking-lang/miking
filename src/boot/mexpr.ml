
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
  [("unit",Cunit);
   ("not",Cnot);("and",Cand(None));("or",Cor(None));
   ("addi",Caddi(None));("subi",Csubi(None));("muli",Cmuli(None));
   ("divi",Cdivi(None));("modi",Cmodi(None));("negi",Cnegi);
   ("lti",Clti(None));("leqi",Cleqi(None));("gti",Cgti(None));("geqi",Cgeqi(None));
   ("eqi",Ceqi(None));("neqi",Cneqi(None));
   ("slli",Cslli(None));("srli",Csrli(None));("srai",Csrai(None));
   ("arity",Carity);
   ("addf",Caddf(None));("subf",Csubf(None));("mulf",Cmulf(None));
   ("divf",Cdivf(None));("negf",Cnegf);
   ("ltf",Cltf(None));("leqf",Cleqf(None));("gtf",Cgtf(None));("geqf",Cgeqf(None));
   ("eqf",Ceqf(None));("neqf",Cneqf(None));
   ("floorfi", Cfloorfi); ("ceilfi", Cceilfi); ("roundfi", Croundfi);
   ("int2float", CInt2float); ("string2float", CString2float);
   ("char2int",CChar2int);("int2char",CInt2char);
   ("makeseq",Cmakeseq(None)); ("length",Clength);("concat",Cconcat(None));
   ("nth",Cnth(None)); ("cons",Ccons(None));
   ("slice",Cslice(None,None)); ("reverse",Creverse);
   ("print",Cprint);("dprint",Cdprint);
   ("argv",CSeq(Sys.argv |> Array.to_list |>
                  List.map (fun s ->
                      TmConst(NoInfo,CSeq(s |> us |> ustring2list |>
                                            List.map (fun x->TmConst(NoInfo,CChar(x))))))));
   ("readFile",CreadFile); ("writeFile",CwriteFile(None));
   ("fileExists", CfileExists); ("deleteFile", CdeleteFile);
   ("error",Cerror);
   ("debugShow", CdebugShow)
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
  | CSeq(_)           -> 0
  | Cmakeseq(None)    -> 2 | Cmakeseq(Some(_)) -> 1
  | Clength           -> 1
  | Cconcat(None)     -> 2 | Cconcat(Some(_)) -> 1
  | Cnth(None)        -> 2 | Cnth(Some(_)) -> 1
  | Ccons(None)       -> 2 | Ccons(Some(_)) -> 1
  | Cslice(None,None) -> 3 | Cslice(Some(_),None) -> 2 | Cslice(_,Some(_)) -> 1
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
  (* External functions TODO: Should not be bart of core language *)
  | CExt v            -> Ext.arity v


let fail_constapp f v fi = raise_error fi ("Incorrect application. function: "
                                         ^ Ustring.to_utf8 (pprint_const f)
                                         ^ " value: "
                                         ^ Ustring.to_utf8 (pprintME v))


(* Evaluates a constant application. This is the standard delta function
   delta(c,v) with the exception that it returns an expression and not
   a value. This is why the returned value is evaluated in the eval() function.
   The reason for this is that if-expressions return expressions
   and not values. *)
let delta fi c v  =
    let fail_constapp = fail_constapp c v in
    match c,v with
    (* MCore intrinsic: unit - no operation *)
    | Cunit,t -> fail_constapp (tm_info t)
    (* MCore boolean intrinsics *)
    | CBool(_),t -> fail_constapp (tm_info t)

    | Cnot,TmConst(fi,CBool(v)) -> TmConst(fi,CBool(not v))
    | Cnot,t -> fail_constapp (tm_info t)

    | Cand(None),TmConst(fi,CBool(v)) -> TmConst(fi,Cand(Some(v)))
    | Cand(Some(v1)),TmConst(fi,CBool(v2)) -> TmConst(fi,CBool(v1 && v2))
    | Cand(None),t | Cand(Some(_)),t  -> fail_constapp (tm_info t)

    | Cor(None),TmConst(fi,CBool(v)) -> TmConst(fi,Cor(Some(v)))
    | Cor(Some(v1)),TmConst(fi,CBool(v2)) -> TmConst(fi,CBool(v1 || v2))
    | Cor(None),t | Cor(Some(_)),t  -> fail_constapp (tm_info t)

    (* MCore integer intrinsics *)
    | CInt(_),t -> fail_constapp (tm_info t)

    | Caddi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Caddi(Some(v)))
    | Caddi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 + v2))
    | Caddi(None),t | Caddi(Some(_)),t  -> fail_constapp (tm_info t)

    | Csubi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Csubi(Some(v)))
    | Csubi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 - v2))
    | Csubi(None),t | Csubi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cmuli(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cmuli(Some(v)))
    | Cmuli(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 * v2))
    | Cmuli(None),t | Cmuli(Some(_)),t  -> fail_constapp (tm_info t)

    | Cdivi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cdivi(Some(v)))
    | Cdivi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 / v2))
    | Cdivi(None),t | Cdivi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cmodi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cmodi(Some(v)))
    | Cmodi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 mod v2))
    | Cmodi(None),t | Cmodi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cnegi,TmConst(fi,CInt(v)) -> TmConst(fi,CInt((-1)*v))
    | Cnegi,t -> fail_constapp (tm_info t)

    | Clti(None),TmConst(fi,CInt(v)) -> TmConst(fi,Clti(Some(v)))
    | Clti(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 < v2))
    | Clti(None),t | Clti(Some(_)),t  -> fail_constapp (tm_info t)

    | Cleqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cleqi(Some(v)))
    | Cleqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 <= v2))
    | Cleqi(None),t | Cleqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cgti(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cgti(Some(v)))
    | Cgti(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 > v2))
    | Cgti(None),t | Cgti(Some(_)),t  -> fail_constapp (tm_info t)

    | Cgeqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cgeqi(Some(v)))
    | Cgeqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 >= v2))
    | Cgeqi(None),t | Cgeqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Ceqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Ceqi(Some(v)))
    | Ceqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 = v2))
    | Ceqi(None),t | Ceqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cneqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cneqi(Some(v)))
    | Cneqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 <> v2))
    | Cneqi(None),t | Cneqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cslli(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cslli(Some(v)))
    | Cslli(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 lsl v2))
    | Cslli(None),t | Cslli(Some(_)),t  -> fail_constapp (tm_info t)

    | Csrli(None),TmConst(fi,CInt(v)) -> TmConst(fi,Csrli(Some(v)))
    | Csrli(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 lsr v2))
    | Csrli(None),t | Csrli(Some(_)),t  -> fail_constapp (tm_info t)

    | Csrai(None),TmConst(fi,CInt(v)) -> TmConst(fi,Csrai(Some(v)))
    | Csrai(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 asr v2))
    | Csrai(None),t | Csrai(Some(_)),t  -> fail_constapp (tm_info t)

    | Carity,TmConst(fi,c) -> TmConst(fi,CInt(arity c))
    | Carity,t -> fail_constapp (tm_info t)

    (* MCore intrinsic: Floating-point number constant and operations *)
    | CFloat(_),t -> fail_constapp (tm_info t)

    | Caddf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Caddf(Some(v)))
    | Caddf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 +. v2))
    | Caddf(None),t | Caddf(Some(_)),t  -> fail_constapp (tm_info t)

    | Csubf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Csubf(Some(v)))
    | Csubf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 -. v2))
    | Csubf(None),t | Csubf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cmulf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cmulf(Some(v)))
    | Cmulf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 *. v2))
    | Cmulf(None),t | Cmulf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cdivf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cdivf(Some(v)))
    | Cdivf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 /. v2))
    | Cdivf(None),t | Cdivf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cnegf,TmConst(fi,CFloat(v)) -> TmConst(fi,CFloat((-1.0)*.v))
    | Cnegf,t -> fail_constapp (tm_info t)

    | Cltf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cltf(Some(v)))
    | Cltf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CBool(v1 < v2))
    | Cltf(None),t | Cltf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cleqf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cleqf(Some(v)))
    | Cleqf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CBool(v1 <= v2))
    | Cleqf(None),t | Cleqf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cgtf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cgtf(Some(v)))
    | Cgtf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CBool(v1 > v2))
    | Cgtf(None),t | Cgtf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cgeqf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cgeqf(Some(v)))
    | Cgeqf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CBool(v1 >= v2))
    | Cgeqf(None),t | Cgeqf(Some(_)),t  -> fail_constapp (tm_info t)

    | Ceqf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Ceqf(Some(v)))
    | Ceqf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CBool(v1 = v2))
    | Ceqf(None),t | Ceqf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cneqf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cneqf(Some(v)))
    | Cneqf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CBool(v1 <> v2))
    | Cneqf(None),t | Cneqf(Some(_)),t  -> fail_constapp (tm_info t)
    | CString2float,TmConst(fi,CSeq(s)) ->
        let to_char = function
          | TmConst(_, CChar(c)) -> c
          | _ -> fail_constapp fi
        in
        let f = Ustring.to_utf8(Ustring.from_uchars(
                Array.of_list(List.map to_char s)))
        in
        TmConst(fi, CFloat(Float.of_string f))
    | CString2float,t -> fail_constapp (tm_info t)

    | Cfloorfi,TmConst(fi,CFloat(v)) -> TmConst(fi,CInt(Float.floor v |> int_of_float))
    | Cfloorfi,t -> fail_constapp (tm_info t)

    | Cceilfi,TmConst(fi,CFloat(v)) -> TmConst(fi,CInt(Float.ceil v |> int_of_float))
    | Cceilfi,t -> fail_constapp (tm_info t)

    | Croundfi,TmConst(fi,CFloat(v)) -> TmConst(fi,CInt(Float.round v |> int_of_float))
    | Croundfi,t -> fail_constapp (tm_info t)

    | CInt2float,TmConst(fi,CInt(v)) -> TmConst(fi,CFloat(float_of_int v))
    | CInt2float,t -> fail_constapp (tm_info t)

    (* MCore intrinsic: characters *)
    | CChar(_),t -> fail_constapp (tm_info t)

    | CChar2int,TmConst(fi,CChar(v)) -> TmConst(fi,CInt(v))
    | CChar2int,t -> fail_constapp (tm_info t)

    | CInt2char,TmConst(fi,CInt(v)) -> TmConst(fi,CChar(v))
    | CInt2char,t -> fail_constapp (tm_info t)

    (* MCore intrinsic: sequences *)
    | CSeq(_),t -> fail_constapp (tm_info t)

    | Cmakeseq(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cmakeseq(Some(v)))
    | Cmakeseq(Some(v1)),t -> TmConst(tm_info t,CSeq(List.init v1 (fun _ -> t)))
    | Cmakeseq(None),t -> fail_constapp (tm_info t)

    | Clength,TmConst(fi,CSeq(lst)) -> TmConst(fi,CInt(List.length lst))
    | Clength,t -> fail_constapp (tm_info t)

    | Cconcat(None),TmConst(fi,CSeq(lst1)) -> TmConst(fi,Cconcat(Some(lst1)))
    | Cconcat(Some(lst1)),TmConst(fi,CSeq(lst2)) ->
       TmConst(fi,CSeq(List.append lst1 lst2))
    | Cconcat(None),t | Cconcat(Some(_)),t  -> fail_constapp (tm_info t)

    | Cnth(None),TmConst(fi,CSeq(lst)) -> TmConst(fi,Cnth(Some(lst)))
    | Cnth(Some(lst)),TmConst(_,CInt(n)) ->
       (try List.nth lst n with _ -> raise_error fi "Out of bound access in sequence.")
    | Cnth(None),t | Cnth(Some(_)),t  -> fail_constapp (tm_info t)

    | Ccons(None),t -> TmConst(tm_info t,Ccons(Some(t)))
    | Ccons(Some(t)),TmConst(fi,CSeq(lst)) -> TmConst(fi,CSeq(t::lst))
    | Ccons(Some(_)),t  -> fail_constapp (tm_info t)

    | Cslice(None,None),TmConst(fi,CSeq(lst)) -> TmConst(fi,Cslice(Some(lst),None))
    | Cslice(Some(lst),None),TmConst(fi,CInt(s)) -> TmConst(fi,Cslice(Some(lst),Some(s)))
    | Cslice(Some(lst),Some(s)),TmConst(fi,CInt(l)) ->
       let slice s l lst =
         let rec slice' i = function
           | [] -> []
           | _ when i >= s + l -> []
           | x::xs when s <= i && i < s + l -> x::slice' (i + 1) xs
           | _::xs -> slice' (i+1) xs
         in
         slice' 0 lst
       in TmConst(fi, CSeq(slice s l lst))
    | Cslice(_,_),t -> fail_constapp (tm_info t)

    | Creverse,TmConst(fi,CSeq(lst)) -> TmConst(fi,CSeq(List.rev lst))
    | Creverse,t -> fail_constapp (tm_info t)

    (* MCore intrinsic: records *)
    | CRecord(_),t -> fail_constapp (tm_info t)

    (* MCore debug and stdio intrinsics *)
    | Cprint, TmConst(fi,CSeq(lst)) ->
       uprint_string (tmlist2ustring fi lst); TmConst(NoInfo,Cunit)
    | Cprint, t -> raise_error (tm_info t) "The argument to print must be a string"

    | Cdprint, t -> uprint_string (pprintME t); TmConst(NoInfo,Cunit)

    | CreadFile,TmConst(fi,CSeq(lst)) ->
       TmConst(fi,CSeq(Ustring.read_file (Ustring.to_utf8 (tmlist2ustring fi lst))
                       |> (ustring2tmlist fi)))
    | CreadFile,t -> fail_constapp (tm_info t)

    | CwriteFile(None),TmConst(fi,CSeq(l)) -> TmConst(fi,CwriteFile(Some(tmlist2ustring fi l)))
    | CwriteFile(Some(fname)),TmConst(fi,CSeq(lst)) ->
        Ustring.write_file (Ustring.to_utf8 fname) (tmlist2ustring fi lst); TmConst(NoInfo,Cunit)
    | CwriteFile(None),t | CwriteFile(Some(_)),t  -> fail_constapp (tm_info t)

    | CfileExists,TmConst(fi,CSeq(lst)) ->
        TmConst(fi,CBool(Sys.file_exists (Ustring.to_utf8 (tmlist2ustring fi lst))))
    | CfileExists,t -> fail_constapp (tm_info t)

    | CdeleteFile,TmConst(fi,CSeq(lst)) ->
        Sys.remove (Ustring.to_utf8 (tmlist2ustring fi lst)); TmConst(NoInfo,Cunit)
    | CdeleteFile,t -> fail_constapp (tm_info t)

    | Cerror, TmConst(fi,CSeq(lst)) ->
       (uprint_endline ((us"ERROR: ") ^. (tmlist2ustring fi lst)); exit 1)
    | Cerror,t -> fail_constapp (tm_info t)
    | CdebugShow,t ->
       uprint_endline ((us"EXPR: ") ^. (pprintME t)); TmConst(NoInfo,Cunit)

    | CExt v, t -> Ext.delta v t


(* Debug function used in the eval function *)
let debug_eval env t =
  if enable_debug_eval then
    (printf "\n-- eval -- \n";
     uprint_endline (pprintME t);
     if enable_debug_eval_env then
        uprint_endline (pprint_env env))
  else ()

(* Print out error message when a unit test fails *)
let unittest_failed fi t1 t2=
  uprint_endline
    (match fi with
    | Info(_,l1,_,_,_) -> us"\n ** Unit test FAILED on line " ^.
        us(string_of_int l1) ^. us" **\n    LHS: " ^. (pprintME t1) ^.
        us"\n    RHS: " ^. (pprintME t2)
    | NoInfo -> us"Unit test FAILED ")



(* Check if two value terms are equal *)
let rec val_equal v1 v2 =
  match v1,v2 with
  | TmConst(_,CSeq(lst1)), TmConst(_,CSeq(lst2)) -> (
     List.length lst1 = List.length lst2 &&
     List.for_all (fun (x,y) -> val_equal x y) (List.combine lst1 lst2))
  | TmConst(_,CRecord(r1)), TmConst(_,CRecord(r2)) ->
     Record.equal val_equal r1 r2
  | TmConst(_,c1),TmConst(_,c2) -> c1 = c2
  | TmTuple(_,tms1),TmTuple(_,tms2) ->
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
    | PatNamed(fi,x) -> (VarTm(x)::env, PatNamed(fi,x))
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
  | TmIf(fi,t1,t2,t3) -> TmIf(fi,debruijn env t1,debruijn env t2,debruijn env t3)
  | TmFix(_) -> t
  | TmSeq(fi,tms) -> TmSeq(fi,List.map (debruijn env) tms)
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

let rec tryMatch env value = function
  | PatNamed _ -> Some (value :: env)
  | PatTuple(_,pats) ->
     let go v p env = Option.bind (fun env -> tryMatch env v p) env in
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
  | TmVar(_,_,n) -> eval env  (List.nth env n)
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
       | TmConst(_,c) -> delta fiapp c (eval env t2)
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
                                 ^ Ustring.to_utf8 (pprintME f)))
  (* Constant and fix *)
  | TmConst(_,_) | TmFix(_) -> t
  (* If expression *)
  | TmIf(fi,t1,t2,t3) -> (
    match eval env t1 with
    | TmConst(_,CBool(true)) -> eval env t2
    | TmConst(_,CBool(false)) -> eval env t3
    | _ -> raise_error fi "The guard of the if expression is not a boolean value"
  )
  (* Sequences *)
  | TmSeq(fi,tms) -> TmConst(fi,CSeq(List.map (eval env) tms))
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
                             ^ Ustring.to_utf8 (pprintME v)))
      | LabStr s ->
         (match eval env t with
          | TmConst(fi, CRecord(r)) ->
             (try Record.find s r
              with _ -> raise_error fi ("No label '" ^ Ustring.to_utf8 s ^
                                        "' in record " ^ Ustring.to_utf8 (pprint_const (CRecord(r)))))
          | v ->
             raise_error fi ("Cannot project from term. The term is not a record: "
                             ^ Ustring.to_utf8 (pprintME v))))
  | TmRecordUpdate(fi,t1,l,t2) ->
     (match eval env t1 with
      | TmConst(fi, CRecord(r)) ->
         if Record.mem l r
         then TmConst(fi, CRecord(Record.add l (eval env t2) r))
         else raise_error fi ("No label '" ^ Ustring.to_utf8 l ^
                                        "' in record " ^ Ustring.to_utf8 (pprint_const (CRecord r)))
      | v ->
         raise_error fi ("Cannot update the term. The term is not a record: "
                         ^ Ustring.to_utf8 (pprintME v)))
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
