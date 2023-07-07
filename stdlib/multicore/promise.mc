include "thread-pool.mc"
include "cond.mc"

type Promise a =
  { mutex : Mutex
  , cond : Cond
  , value : Ref (Option a)
  }

let _wrapAndMk : all a. (() -> a) -> (() -> (), Promise a) = lam f.
  let prom = {mutex = mutexCreate (), cond = condCreate (), value = ref (None ())} in
  let f = lam.
    printError "pre _wrapAndMk f\n";
    flushStderr ();
    let res = f () in
    printError "pre-lock _wrapAndMk f\n";
    flushStderr ();
    mutexLock prom.mutex;
    printError "post-lock _wrapAndMk f\n";
    flushStderr ();
    modref prom.value (Some res);
    printError "pre-broadcast _wrapAndMk f\n";
    flushStderr ();
    condBroadcast prom.cond;
    printError "post-broadcast _wrapAndMk f\n";
    flushStderr ();
    mutexRelease prom.mutex in
  (f, prom)

let promiseMkThread : all a. (() -> a) -> (Thread (), Promise a) = lam f.
  match _wrapAndMk f with (f, prom) in
  (threadSpawn f, prom)

let promiseMkThread_ : all a. (() -> a) -> Promise a = lam f.
  match _wrapAndMk f with (f, prom) in
  threadSpawn f;
  prom

let promiseThreadPool : all a. (() -> a) -> ThreadPool () -> Promise a = lam f. lam pool.
  match _wrapAndMk f with (f, prom) in
  let _async = threadPoolAsync pool f in
  prom

let promiseForce : all a. Promise a -> a = lam prom.
  match deref prom.value with Some v then v else
  mutexLock prom.mutex;
  recursive let work = lam.
    match deref prom.value with Some v then mutexRelease prom.mutex; v else
    condWait prom.cond prom.mutex;
    work ()
  in work ()


-- Fake promises that don't actually suspend anything

type Promise a = { val : a }

let promiseMkThread_ : all a. (() -> a) -> Promise a = lam f. { val = f () }

let promiseForce : all a. Promise a -> a = lam x. x.val
