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
    let res = f () in
    mutexLock prom.mutex;
    modref prom.value (Some res);
    condBroadcast prom.cond;
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
