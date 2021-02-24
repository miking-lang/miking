open Parimpl

type 'a ext =
  | ParAtomicRef of 'a A.t
  | ParatomicMake
  | ParatomicGet
  | ParatomicSet of 'a A.t option
  | ParatomicExchange of 'a A.t option
  | ParatomicFetchAndAdd of 'a A.t option
  | ParatomicCAS of 'a A.t option * 'a option
  | ParThread of 'a ParThread.t
  | ParThreadID of ParThread.id
  | ParthreadID2int
  | ParthreadSpawn
  | ParthreadJoin
  | ParthreadGetID
  | ParthreadSelf
  | ParthreadWait
  | ParthreadNotify
  | ParthreadCriticalSection
  | ParthreadCPURelax
