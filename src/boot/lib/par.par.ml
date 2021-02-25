open Ast
open Parast
open Parpprint
open Msg
open Parimpl

let externals =
  let f p = TmConst (NoInfo, CPar p) in
  [ ("atomicMake", f ParatomicMake)
  ; ("atomicGet", f ParatomicGet)
  ; ("atomicCAS", f (ParatomicCAS (None, None)))
  ; ("atomicExchange", f (ParatomicExchange None))
  ; ("atomicFetchAndAdd", f (ParatomicFetchAndAdd None))
  ; ("threadID2int", f ParthreadID2int)
  ; ("threadSpawn", f ParthreadSpawn)
  ; ("threadJoin", f ParthreadJoin)
  ; ("threadGetID", f ParthreadGetID)
  ; ("threadSelf", f ParthreadSelf)
  ; ("threadWait", f ParthreadWait)
  ; ("threadNotify", f ParthreadNotify)
  ; ("threadCriticalSection", f ParthreadCriticalSection)
  ; ("threadCPURelax", f ParthreadCPURelax) ]

let arity = function
  | ParAtomicRef _ ->
      0
  | ParatomicMake ->
      1
  | ParatomicGet ->
      1
  | ParatomicCAS (None, None) ->
      3
  | ParatomicCAS (Some _, None) ->
      2
  | ParatomicCAS (_, Some _) ->
      1
  | ParatomicExchange None ->
      2
  | ParatomicExchange (Some _) ->
      1
  | ParatomicFetchAndAdd None ->
      2
  | ParatomicFetchAndAdd (Some _) ->
      1
  | ParThread _ ->
      0
  | ParThreadID _ ->
      0
  | ParthreadID2int ->
      1
  | ParthreadSpawn ->
      1
  | ParthreadJoin ->
      1
  | ParthreadGetID ->
      1
  | ParthreadSelf ->
      1
  | ParthreadWait ->
      1
  | ParthreadNotify ->
      1
  | ParthreadCriticalSection ->
      1
  | ParthreadCPURelax ->
      1

let fail_constapp f v fi =
  raise_error fi
    ( "Incorrect application. function: "
    ^ Ustring.to_utf8 (pprint f)
    ^ " value: "
    ^ Ustring.to_utf8 (Pprint.ustring_of_tm v) )

let delta eval env fi c v =
  let fail_constapp fi = fail_constapp c v fi in
  match (c, v) with
  | ParAtomicRef _, _ ->
      fail_constapp fi
  | ParatomicMake, TmConst (_, CInt i) ->
      TmConst (fi, CPar (ParAtomicRef (Atomic.Int (Atomic.Int.make i))))
  | ParatomicMake, v ->
      TmConst (fi, CPar (ParAtomicRef (Atomic.NoInt (Atomic.NoInt.make v))))
  | ParatomicGet, TmConst (_, CPar (ParAtomicRef (Int r))) ->
      TmConst (fi, CInt (Atomic.Int.get r))
  | ParatomicGet, TmConst (_, CPar (ParAtomicRef (NoInt r))) ->
      Atomic.NoInt.get r
  | ParatomicGet, _ ->
      fail_constapp fi
  | ParatomicCAS (None, None), TmConst (_, CPar (ParAtomicRef r)) ->
      TmConst (fi, CPar (ParatomicCAS (Some r, None)))
  | ParatomicCAS (Some r, None), v ->
      TmConst (fi, CPar (ParatomicCAS (Some r, Some v)))
  | ( ParatomicCAS (Some (Int r), Some (TmConst (_, CInt i1)))
    , TmConst (_, CInt i2) ) ->
      TmConst (fi, CBool (Atomic.Int.compare_and_set r i1 i2))
  | ParatomicCAS (Some (NoInt r), Some v1), v2 ->
      TmConst (fi, CBool (Atomic.NoInt.compare_and_set r v1 v2))
  | ParatomicCAS (_, _), _ ->
      fail_constapp fi
  | ParatomicExchange None, TmConst (_, CPar (ParAtomicRef r)) ->
      TmConst (fi, CPar (ParatomicExchange (Some r)))
  | ParatomicExchange (Some (Int r)), TmConst (_, CInt i) ->
      TmConst (fi, CInt (Atomic.Int.exchange r i))
  | ParatomicExchange (Some (NoInt r)), v ->
      Atomic.NoInt.exchange r v
  | ParatomicExchange _, _ ->
      fail_constapp fi
  | ParatomicFetchAndAdd _, TmConst (_, CPar (ParAtomicRef (Int r))) ->
      TmConst (fi, CPar (ParatomicFetchAndAdd (Some (Int r))))
  | ParatomicFetchAndAdd (Some (Int r)), TmConst (_, CInt i) ->
      TmConst (fi, CInt (Atomic.Int.fetch_and_add r i))
  | ParatomicFetchAndAdd _, _ ->
      fail_constapp fi
  | ParThread _, _ ->
      fail_constapp fi
  | ParThreadID _, _ ->
      fail_constapp fi
  | ParthreadID2int, TmConst (_, CPar (ParThreadID tid)) ->
      TmConst (fi, CInt (Thread.id_to_int tid))
  | ParthreadID2int, _ ->
      fail_constapp fi
  | ParthreadSpawn, f ->
      TmConst
        ( fi
        , CPar
            (ParThread
               (Thread.spawn (fun _ -> TmApp (fi, f, tmUnit) |> eval env))) )
  | ParthreadJoin, TmConst (_, CPar (ParThread p)) ->
      Thread.join p
  | ParthreadJoin, _ ->
      fail_constapp fi
  | ParthreadGetID, TmConst (_, CPar (ParThread p)) ->
      TmConst (fi, CPar (ParThreadID (Thread.id p)))
  | ParthreadGetID, _ ->
      fail_constapp fi
  | ParthreadSelf, TmRecord (_, x) when Record.is_empty x ->
      TmConst (fi, CPar (ParThreadID (Thread.self ())))
  | ParthreadSelf, _ ->
      fail_constapp fi
  | ParthreadWait, TmRecord (_, x) when Record.is_empty x ->
      Thread.wait () ; tmUnit
  | ParthreadWait, _ ->
      fail_constapp fi
  | ParthreadNotify, TmConst (_, CPar (ParThreadID tid)) ->
      Thread.notify tid ; tmUnit
  | ParthreadNotify, _ ->
      fail_constapp fi
  | ParthreadCriticalSection, f ->
      Thread.critical_section (fun _ -> TmApp (fi, f, tmUnit) |> eval env)
  | ParthreadCPURelax, TmRecord (_, x) when Record.is_empty x ->
      Thread.cpu_relax () ; tmUnit
  | ParthreadCPURelax, _ ->
      fail_constapp fi
