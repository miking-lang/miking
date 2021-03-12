-- Pretty printing of multicore language fragments.

include "mexpr/pprint.mc"
include "multicore/ast.mc"

lang AtomicPrettyPrint = AtomicAst
  sem getConstStringCode (indent : Int) =
  | CAtomicMake _ -> "atoomicMake"
  | CAtomicGet _ -> "atomicGet"
  | CAtomicExchange _ -> "atomicExchange"
  | CAtomicFetchAndAdd _ -> "atomicFetchAndAdd"
  | CAtomicCAS _ -> "atomicCAS"

end

lang ThreadPrettyPrint = ThreadAst
  sem getConstStringCode (indent : Int) =
  | CThreadSpawn _ -> "threadSpawn"
  | CThreadJoin _ -> "threadJoin"
  | CThreadGetID _ -> "threadGetID"
  | CThreadID2Int _ -> "threadID2Int"
  | CThreadSelf _ -> "threadSelf"
  | CThreadWait _ -> "threadWait"
  | CThreadNotify _ -> "threadNotify"
  | CThreadCriticalSection _ -> "threadCriticalSection"
  | CThreadCPURelax _ -> "threadCPURelax"
end

lang MExprParPrettyPrint = MExprPrettyPrint + AtomicPrettyPrint + ThreadPrettyPrint
