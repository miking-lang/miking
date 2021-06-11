
include "atomic.mc"
include "thread.mc"
include "option.mc"
include "string.mc"
include "common.mc"

-- Implements a FIFO queue with multiple senders and multiple receivers.
-- The channel has an infinite buffer, so a call to channelSend never blocks.

type Channel a = Aref [a]

let channelEmpty : Unit -> Channel a = lam.
  atomicMake []

recursive let channelSend : Channel a -> a -> Unit = lam chan. lam msg.
  let old = atomicGet chan in
  let new = snoc old msg in
  if atomicCAS chan old new then ()
  else threadCPURelax (); channelSend chan msg
end

recursive let channelSendMany : Channel a -> [a] -> Unit = lam chan. lam msgs.
  let old = atomicGet chan in
  let new = concat old msgs in
  if atomicCAS chan old new then ()
  else threadCPURelax (); channelSend chan msgs
end

recursive let channelRecv : Channel a -> a = lam chan.
  let contents = atomicGet chan in
  match contents with [] then threadCPURelax (); channelRecv chan
  else match contents with [msg] ++ new then
    if atomicCAS chan contents new then msg
    else threadCPURelax (); channelRecv chan
  else never
end

let channelRecvOpt : Channel a -> Option a = lam chan.
  match atomicGet chan with [] then None ()
  else Some (channelRecv chan)

mexpr

let c = channelEmpty () in

utest channelSend c 1 with () in
utest channelSend c 2 with () in
utest channelRecv c with 1 in
utest channelRecv c with 2 in

utest channelRecvOpt c with None () using optionEq eqi in
channelSend c 2;
utest channelRecvOpt c with Some 2 using optionEq eqi in

utest channelSendMany c [1,2,3] with () in
utest channelRecv c with 1 in
utest channelRecv c with 2 in
utest channelRecv c with 3 in

let debug = false in
let debugPrintLn = if debug then printLn else (lam x. x) in

let threads = map (lam.
  threadSpawn (lam.
    let id = int2string (threadSelf ()) in
    debugPrintLn (concat id " running");
    let res = channelRecv c in
    debugPrintLn (join [int2string (threadSelf ()), " got ", int2string res])))
  (make 10 ()) in

mapi (lam i. lam. channelSend c i) (make 10 ());

iter threadJoin threads;

()
