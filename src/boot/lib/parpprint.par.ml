open Ustring.Op
open Parast
open Printf
open Parimpl

let pprint = function
  | ParAtomicRef _ ->
      us "AtomicRef"
  | ParatomicMake ->
      us "atomicMake"
  | ParatomicGet ->
      us "atomicGet"
  | ParatomicSet _ ->
      us "atomicSet"
  | ParatomicCAS _ ->
      us "atomicCAS"
  | ParatomicExchange _ ->
      us "atomicExchange"
  | ParatomicFetchAndAdd _ ->
      us "fetchAndAdd"
  | ParThread p ->
      us (sprintf "Thread(%d)" (ParThread.id p |> ParThread.id_to_int))
  | ParThreadID tid ->
      us (sprintf "ThreadID(%d)" (ParThread.id_to_int tid))
  | ParthreadID2int ->
      us "threadID2int"
  | ParthreadSpawn ->
      us "threadSpawn"
  | ParthreadJoin ->
      us "threadJoin"
  | ParthreadGetID ->
      us "threadGetID"
  | ParthreadSelf ->
      us "threadSelf"
  | ParthreadWait ->
      us "threadWait"
  | ParthreadNotify ->
      us "threadNotify"
  | ParthreadCriticalSection ->
      us "threadCriticalSection"
  | ParthreadCPURelax ->
      us "threadCPURelax"
