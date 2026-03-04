-- This file provides an abstraction for 'thunks', ref-cells intended
-- for lazy, potentially recursive, computation. Each initialized
-- thunk is either not yet computed, in which case it contains a
-- function to compute its value on demand, or done, in which case it
-- contains a ready value.
--
-- To add flexibility and potentially recursive definitions, thunks
-- start out uninitialized. Then a user may either set a function to
-- compute the value on-demand, or directly set the value. This
-- two-step initialization is to allow the on-demand function to
-- reference other thunks before we have initialized them.
--
-- The primary interface is `mkThunk`, which gives a record with four
-- functions:
-- * read, which reads the current value from the thunk, computing it
--   if necessary, and erroring if the value is uninitialized.
-- * lazy, which sets the function used to compute the thunk
--   on-demand. Note that it's allowed, and expected, to have one
--   function set multiple thunks, and thus use that same function in
--   `lazy` for those thunks.
-- * blackhole, which marks a thunk as "currently being computed",
--   which lets us catch cyclic references. The function given to
--   `lazy` should call this function first for all thunks it will
--   write to, if there's any potential of cyclic references.
-- * write, which writes a computed value to a thunk. Should be called
--   by the function given to `lazy` when its done computing its
--   values.
--
-- Additionally, there are two simple helpers:
-- * noThunk, which creates an empty, unwritable thunk. Used when you
--   need a value of type `Thunk a`, but won't ever use it.
-- * filledThunk, which creates an already set thunk.
--
-- Finally, there's a togglable debug mode. If the reference
-- `_shouldDebugThunks` is true, then each created thunk is recorded
-- for later inspection. Each call to `mkThunk` takes a string label
-- used only for this purpose. Calling `_doDebugThunks` will print all
-- recorded thunks and their current state.

include "common.mc"
include "lazy.mc"

type ThunkContent a
con TCUndefined : all a. () -> ThunkContent a
con TCLazy : all a. (() -> ()) -> ThunkContent a
con TCBlackhole : all a. () -> ThunkContent a
con TCDone : all a. a -> ThunkContent a

type Thunk a =
  { read : () -> a
  , lazy : (() -> ()) -> ()
  , blackhole : () -> ()
  , write : a -> ()
  }

type ThunkMeta =
  { blackhole : () -> ()
  , lazy : (() -> ()) -> ()
  }

let _shouldDebugThunks = ref false

let _debugThunks = ref []

let _clearDebugThunks = lam. modref _debugThunks []

let _doDebugThunks : () -> () = lam.
  if deref _shouldDebugThunks then
    printLn "\nDebug thunks:";
    for_ (deref _debugThunks) (lam f. f ())
  else ()

let mkThunk : all a. Lazy String -> Thunk a = lam label.
  let r = ref (TCUndefined ()) in
  let _debug = lam.
    let state = switch deref r
      case TCDone _ then "done"
      case TCBlackhole _ then "blackhole"
      case TCLazy _ then "lazy"
      case TCUndefined _ then "undefined"
      end in
    printLn (join [lazyForce label, " ", state]) in
  (if deref _shouldDebugThunks then
    modref _debugThunks (snoc (deref _debugThunks) _debug)
   else ());
  { read = lam.
    switch deref r
    case TCDone x then x
    case TCBlackhole _ then error "Cyclic reference in thunks"
    case TCLazy f then
      f ();
      match deref r with TCDone x
      then x
      else error "Lazy thunk failed to update when run"
    case TCUndefined _ then error "Reference to undefined thunk"
    end
  , blackhole = lam.
    match deref r with TCLazy _
    then modref r (TCBlackhole ())
    else error "Tried to blackhole a non-lazy thunk"
  , lazy = lam f.
    match deref r with TCUndefined _
    then modref r (TCLazy f)
    else error "Attempted to set the lazy function of a thunk that wasn't undefined"
  , write = lam a.
    match deref r with TCUndefined _ | TCBlackhole _
    then modref r (TCDone a)
    else error "Attempted to write to a thunk when it was neither undefined nor evaluating"
  }

let noThunk : all a. Thunk a =
  { read = lam. error "Called read on noThunk"
  , blackhole = lam. error "Called blackhole on noThunk"
  , lazy = lam. error "Called lazy on noThunk"
  , write = lam. error "Called write on noThunk"
  }

let filledThunk : all a. a -> Thunk a = lam val.
  { read = lam. val
  , blackhole = lam. error "Called blackhole on filledThunk"
  , lazy = lam. error "Called lazy on filledThunk"
  , write = lam. error "Called write on filledThunk"
  }
