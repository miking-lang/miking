open Parimpl

type 'a ext =
  | ParAtomicRef of 'a Atomic.t
  | ParatomicMake
  | ParatomicGet
  | ParatomicExchange of 'a Atomic.t option
  | ParatomicFetchAndAdd of 'a Atomic.t option
  | ParatomicCAS of 'a Atomic.t option * 'a option
  | ParThread of 'a Thread.t
  | ParThreadID of Thread.id
  | ParthreadID2int
  | ParthreadSpawn
  | ParthreadJoin
  | ParthreadGetID
  | ParthreadSelf
  | ParthreadWait
  | ParthreadNotify
  | ParthreadCriticalSection
  | ParthreadCPURelax
