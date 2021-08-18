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
  ; ("createList", f (CcreateList None))
  ; ("createRope", f (CcreateRope None))
  ; ("length", f Clength)
  ; ("concat", f (Cconcat None))
  ; ("get", f (Cget None))
  ; ("set", f (Cset (None, None)))
  ; ("cons", f (Ccons None))
  ; ("snoc", f (Csnoc None))
  ; ("splitAt", f (CsplitAt None))
  ; ("reverse", f Creverse)
  ; ("head", f Chead)
  ; ("tail", f Ctail)
  ; ("null", f Cnull)
  ; ("map", f (Cmap None))
  ; ("mapi", f (Cmapi None))
  ; ("iter", f (Citer None))
  ; ("iteri", f (Citeri None))
  ; ( "foldl"
    , let sym_foldl = Symb.gensym () in
      let sym_f = Symb.gensym () in
      let sym_acc = Symb.gensym () in
      let sym_seq = Symb.gensym () in
      TmRecLets
        ( NoInfo
        , [ ( NoInfo
            , Ustring.from_utf8 "foldl"
            , sym_foldl
            , TyUnknown NoInfo
            , TmLam
                ( NoInfo
                , Ustring.from_utf8 "f"
                , sym_f
                , TyUnknown NoInfo
                , TmLam
                    ( NoInfo
                    , Ustring.from_utf8 "acc"
                    , sym_acc
                    , TyUnknown NoInfo
                    , TmLam
                        ( NoInfo
                        , Ustring.from_utf8 "seq"
                        , sym_seq
                        , TyUnknown NoInfo
                        , TmMatch
                            ( NoInfo
                            , TmApp
                                ( NoInfo
                                , TmConst (NoInfo, Cnull)
                                , TmVar
                                    (NoInfo, Ustring.from_utf8 "seq", sym_seq)
                                )
                            , PatBool (NoInfo, true)
                            , TmVar (NoInfo, Ustring.from_utf8 "acc", sym_acc)
                            , TmApp
                                ( NoInfo
                                , TmApp
                                    ( NoInfo
                                    , TmApp
                                        ( NoInfo
                                        , TmVar
                                            ( NoInfo
                                            , Ustring.from_utf8 "foldl"
                                            , sym_foldl )
                                        , TmVar
                                            ( NoInfo
                                            , Ustring.from_utf8 "f"
                                            , sym_f ) )
                                    , TmApp
                                        ( NoInfo
                                        , TmApp
                                            ( NoInfo
                                            , TmVar
                                                ( NoInfo
                                                , Ustring.from_utf8 "f"
                                                , sym_f )
                                            , TmVar
                                                ( NoInfo
                                                , Ustring.from_utf8 "acc"
                                                , sym_acc ) )
                                        , TmApp
                                            ( NoInfo
                                            , TmConst (NoInfo, Chead)
                                            , TmVar
                                                ( NoInfo
                                                , Ustring.from_utf8 "seq"
                                                , sym_seq ) ) ) )
                                , TmApp
                                    ( NoInfo
                                    , TmConst (NoInfo, Ctail)
                                    , TmVar
                                        ( NoInfo
                                        , Ustring.from_utf8 "seq"
                                        , sym_seq ) ) ) ) ) ) ) ) ]
        , TmVar (NoInfo, Ustring.from_utf8 "foldl", sym_foldl) ) )
  ; ( "foldr"
    , let sym_foldr = Symb.gensym () in
      let sym_f = Symb.gensym () in
      let sym_acc = Symb.gensym () in
      let sym_seq = Symb.gensym () in
      TmRecLets
        ( NoInfo
        , [ ( NoInfo
            , Ustring.from_utf8 "foldr"
            , sym_foldr
            , TyUnknown NoInfo
            , TmLam
                ( NoInfo
                , Ustring.from_utf8 "f"
                , sym_f
                , TyUnknown NoInfo
                , TmLam
                    ( NoInfo
                    , Ustring.from_utf8 "acc"
                    , sym_acc
                    , TyUnknown NoInfo
                    , TmLam
                        ( NoInfo
                        , Ustring.from_utf8 "seq"
                        , sym_seq
                        , TyUnknown NoInfo
                        , TmMatch
                            ( NoInfo
                            , TmApp
                                ( NoInfo
                                , TmConst (NoInfo, Cnull)
                                , TmVar
                                    (NoInfo, Ustring.from_utf8 "seq", sym_seq)
                                )
                            , PatBool (NoInfo, true)
                            , TmVar (NoInfo, Ustring.from_utf8 "acc", sym_acc)
                            , TmApp
                                ( NoInfo
                                , TmApp
                                    ( NoInfo
                                    , TmVar
                                        (NoInfo, Ustring.from_utf8 "f", sym_f)
                                    , TmApp
                                        ( NoInfo
                                        , TmConst (NoInfo, Chead)
                                        , TmVar
                                            ( NoInfo
                                            , Ustring.from_utf8 "seq"
                                            , sym_seq ) ) )
                                , TmApp
                                    ( NoInfo
                                    , TmApp
                                        ( NoInfo
                                        , TmApp
                                            ( NoInfo
                                            , TmVar
                                                ( NoInfo
                                                , Ustring.from_utf8 "foldr"
                                                , sym_foldr )
                                            , TmVar
                                                ( NoInfo
                                                , Ustring.from_utf8 "f"
                                                , sym_f ) )
                                        , TmVar
                                            ( NoInfo
                                            , Ustring.from_utf8 "acc"
                                            , sym_acc ) )
                                    , TmApp
                                        ( NoInfo
                                        , TmConst (NoInfo, Ctail)
                                        , TmVar
                                            ( NoInfo
                                            , Ustring.from_utf8 "seq"
                                            , sym_seq ) ) ) ) ) ) ) ) ) ]
        , TmVar (NoInfo, Ustring.from_utf8 "foldr", sym_foldr) ) )
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
          |> Mseq.map (fun s ->
                 TmSeq
                   ( NoInfo
                   , s |> us |> Mseq.Helpers.of_ustring
                     |> Mseq.map (fun x -> TmConst (NoInfo, CChar x)) ) ) ) )
  ; ("readFile", f CreadFile)
  ; ("writeFile", f (CwriteFile None))
  ; ("fileExists", f CfileExists)
  ; ("deleteFile", f CdeleteFile)
  ; ("command", f Ccommand)
  ; ("error", f Cerror)
  ; ("exit", f Cexit)
  ; ("flushStdout", f CflushStdout) (* MCore intrinsics: Symbols *)
  ; ("eqsym", f (Ceqsym None))
  ; ("gensym", f Cgensym)
  ; ("sym2hash", f Csym2hash) (* MCore intrinsics: References *)
  ; ("constructorTag", f CconstructorTag)
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
  ; ("tensorCopy", f CtensorCopy)
  ; ("tensorTransposeExn", f (CtensorTransposeExn (None, None)))
  ; ("tensorSliceExn", f (CtensorSliceExn None))
  ; ("tensorSubExn", f (CtensorSubExn (None, None)))
  ; ("tensorIterSlice", f (CtensorIterSlice None))
  ; ("tensorEq", f (CtensorEq (None, None)))
  ; ("tensor2string", f (Ctensor2string None))
    (* MCore intrinsics: Boot parser *)
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
  (* Append python intrinsics *)
  @ Pyffi.externals
  |> List.map (fun (x, t) -> (x, Symb.gensym (), t))

(* Mapping name to symbol *)
let builtin_name2sym =
  List.fold_left
    (fun env (x, s, _) -> Symbolize.addsym (IdVar (usid x)) s env)
    Symbolize.empty_sym_env builtin

(* Mapping sym to term *)
let builtin_sym2term = List.map (fun (_, s, t) -> (s, t)) builtin
