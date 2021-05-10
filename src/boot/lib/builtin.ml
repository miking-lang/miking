open Ast
open Intrinsics
open Ustring.Op

(* Extract the arguments when running boot, and the arguments of the actual program.
   -- is used to separate the program arguments. For instance,
     mi myprog.mc --debug-parse -- foo --something
   results in two arrays:
    argv_boot: ["mi","myprog.mc","--debug-parse"]
    argv_prog: ["mi","foo","--something"] *)
let argv_boot, argv_prog =
  let n, _ =
    Sys.argv
    |> Array.fold_left
         (fun (n, b) x -> if x = "--" || b then (n, true) else (n + 1, b))
         (0, false)
  in
  ( Array.sub Sys.argv 0 n
  , Array.append (Array.sub Sys.argv 0 1)
      ( try Array.sub Sys.argv (n + 1) (Array.length Sys.argv - n - 1)
        with _ -> [||] ) )

(* Mapping between named builtin functions (intrinsics) and the
   correspond constants *)
let builtin =
  let f c = TmConst (NoInfo, c) in
  (* MCore intrinsics: Integers *)
  [ ("addi", f (Caddi None))
  ; ("subi", f (Csubi None))
  ; ("muli", f (Cmuli None))
  ; ("divi", f (Cdivi None))
  ; ("modi", f (Cmodi None))
  ; ("negi", f Cnegi)
  ; ("lti", f (Clti None))
  ; ("leqi", f (Cleqi None))
  ; ("gti", f (Cgti None))
  ; ("geqi", f (Cgeqi None))
  ; ("eqi", f (Ceqi None))
  ; ("neqi", f (Cneqi None))
  ; ("slli", f (Cslli None))
  ; ("srli", f (Csrli None))
  ; ("srai", f (Csrai None))
  ; ("arity", f Carity) (* MCore intrinsics: Floating-point numbers *)
  ; ("addf", f (Caddf None))
  ; ("subf", f (Csubf None))
  ; ("mulf", f (Cmulf None))
  ; ("divf", f (Cdivf None))
  ; ("negf", f Cnegf)
  ; ("ltf", f (Cltf None))
  ; ("leqf", f (Cleqf None))
  ; ("gtf", f (Cgtf None))
  ; ("geqf", f (Cgeqf None))
  ; ("eqf", f (Ceqf None))
  ; ("neqf", f (Cneqf None))
  ; ("floorfi", f Cfloorfi)
  ; ("ceilfi", f Cceilfi)
  ; ("roundfi", f Croundfi)
  ; ("int2float", f Cint2float)
  ; ("string2float", f Cstring2float)
  ; ("float2string", f Cfloat2string) (* MCore intrinsics: Characters *)
  ; ("eqc", f (Ceqc None))
  ; ("char2int", f Cchar2int)
  ; ("int2char", f Cint2char) (* MCore intrinsics: Sequences *)
  ; ("create", f (Ccreate None))
  ; ("length", f Clength)
  ; ("concat", f (Cconcat None))
  ; ("get", f (Cget None))
  ; ("set", f (Cset (None, None)))
  ; ("cons", f (Ccons None))
  ; ("snoc", f (Csnoc None))
  ; ("splitAt", f (CsplitAt None))
  ; ("reverse", f Creverse)
  ; ("subsequence", f (Csubsequence (None, None)))
    (* MCore intrinsics: Random numbers *)
  ; ("randIntU", f (CrandIntU None))
  ; ("randSetSeed", f CrandSetSeed) (* MCore intrinsics: Time *)
  ; ("wallTimeMs", f CwallTimeMs)
  ; ("sleepMs", f CsleepMs) (* MCore intrinsics: Debug and I/O *)
  ; ("print", f Cprint)
  ; ("dprint", f Cdprint)
  ; ("readLine", f CreadLine)
  ; ("readBytesAsString", f CreadBytesAsString)
  ; ( "argv"
    , TmSeq
        ( NoInfo
        , argv_prog |> Mseq.Helpers.of_array
          |> Mseq.Helpers.map (fun s ->
                 TmSeq
                   ( NoInfo
                   , s |> us |> Mseq.Helpers.of_ustring
                     |> Mseq.Helpers.map (fun x -> TmConst (NoInfo, CChar x))
                   ) ) ) )
  ; ("readFile", f CreadFile)
  ; ("writeFile", f (CwriteFile None))
  ; ("fileExists", f CfileExists)
  ; ("deleteFile", f CdeleteFile)
  ; ("command", f Ccommand)
  ; ("error", f Cerror)
  ; ("exit", f Cexit) (* MCore intrinsics: Symbols *)
  ; ("eqsym", f (Ceqsym None))
  ; ("gensym", f Cgensym)
  ; ("sym2hash", f Csym2hash) (* MCore intrinsics: References *)
  ; ("ref", f Cref)
  ; ("deref", f CdeRef)
  ; ("modref", f (CmodRef None)) (* MCore intrinsics: Maps *)
  ; ("mapEmpty", f CmapEmpty)
  ; ("mapSize", f CmapSize)
  ; ("mapGetCmpFun", f CmapGetCmpFun)
  ; ("mapInsert", f (CmapInsert (None, None)))
  ; ("mapRemove", f (CmapRemove None))
  ; ("mapFindWithExn", f (CmapFindWithExn None))
  ; ("mapFindOrElse", f (CmapFindOrElse (None, None)))
  ; ("mapFindApplyOrElse", f (CmapFindApplyOrElse (None, None, None)))
  ; ("mapAny", f (CmapAny None))
  ; ("mapMem", f (CmapMem None))
  ; ("mapMap", f (CmapMap None))
  ; ("mapMapWithKey", f (CmapMapWithKey None))
  ; ("mapFoldWithKey", f (CmapFoldWithKey (None, None)))
  ; ("mapBindings", f CmapBindings)
  ; ("mapEq", f (CmapEq (None, None)))
  ; ("mapCmp", f (CmapCmp (None, None))) (* MCore intrinsics: Tensors *)
  ; ("tensorCreateCArrayInt", f (CtensorCreateCArrayInt None))
  ; ("tensorCreateCArrayFloat", f (CtensorCreateCArrayFloat None))
  ; ("tensorCreateDense", f (CtensorCreateDense None))
  ; ("tensorGetExn", f (CtensorGetExn None))
  ; ("tensorSetExn", f (CtensorSetExn (None, None)))
  ; ("tensorRank", f CtensorRank)
  ; ("tensorShape", f CtensorShape)
  ; ("tensorReshapeExn", f (CtensorReshapeExn None))
  ; ("tensorCopyExn", f (CtensorCopyExn None))
  ; ("tensorSliceExn", f (CtensorSliceExn None))
  ; ("tensorSubExn", f (CtensorSubExn (None, None)))
  ; ("tensorIteri", f (CtensorIteri None)) (* MCore intrinsics: Boot parser *)
  ; ("bootParserParseMExprString", f (CbootParserParseMExprString None))
  ; ("bootParserParseMCoreFile", f (CbootParserParseMCoreFile None))
  ; ("bootParserGetId", f CbootParserGetId)
  ; ("bootParserGetTerm", f (CbootParserGetTerm None))
  ; ("bootParserGetType", f (CbootParserGetType None))
  ; ("bootParserGetString", f (CbootParserGetString None))
  ; ("bootParserGetInt", f (CbootParserGetInt None))
  ; ("bootParserGetFloat", f (CbootParserGetFloat None))
  ; ("bootParserGetListLength", f (CbootParserGetListLength None))
  ; ("bootParserGetConst", f (CbootParserGetConst None))
  ; ("bootParserGetPat", f (CbootParserGetPat None))
  ; ("bootParserGetInfo", f (CbootParserGetInfo None)) ]
  (* Append multicore intrinsics *)
  @ Par.externals
  (* Append sundials intrinsics *)
  @ Sd.externals
  (* Append python intrinsics *)
  @ Pyffi.externals
  |> List.map (fun (x, t) -> (x, Symb.gensym (), t))

(* Mapping name to symbol *)
let builtin_name2sym = List.map (fun (x, s, _) -> (IdVar (usid x), s)) builtin

(* Mapping sym to term *)
let builtin_sym2term = List.map (fun (_, s, t) -> (s, t)) builtin
