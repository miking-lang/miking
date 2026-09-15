-- Small helper functions for namespace manipulation.
-- NOTE: This API is currently lightly used and could be refactored into the
-- util module if it grows or becomes more generally useful.

include "./util.mc"
include "string.mc"
include "basic-types.mc"
include "seq.mc"

type Namespace = String

let namespaceSplit : Namespace -> [Namespace] =
    lam namespace.
    strSplit "/" namespace

utest namespaceSplit "" with [""]
utest namespaceSplit "a" with ["a"]
utest namespaceSplit "a/b" with ["a", "b"]
utest namespaceSplit "x/y/z" with ["x", "y", "z"]

let namespaceRebuild : [Namespace] -> Namespace =
    lam namespaces.
    strJoin "/" namespaces

utest namespaceRebuild ["a"] with "a"
utest namespaceRebuild ["a","b"] with "a/b"
utest namespaceRebuild ["x","y","z"] with "x/y/z"

let namespaceSeparate : String -> Option { path: String, nesting: String } =
    lam namespace.
    let split = namespaceSplit namespace in
    match findi (strEndsWith ".mc") split with Some i then
        let path = subsequence split 0 (addi i 1) in
        let nesting = subsequence split (addi i 1) (length split) in
        Some { path = namespaceRebuild path, nesting = namespaceRebuild nesting }
    else
        None {}
    
utest namespaceSeparate "a/b/c.mc" with
  Some { path = "a/b/c.mc", nesting = "" }
utest namespaceSeparate "a/b/c.mc/d" with
  Some { path = "a/b/c.mc", nesting = "d" }
utest namespaceSeparate "a/b/c.mc/d/e" with
  Some { path = "a/b/c.mc", nesting = "d/e" }
utest namespaceSeparate "file.mc/x/y" with
  Some { path = "file.mc", nesting = "x/y" }
utest namespaceSeparate "module.mc" with
  Some { path = "module.mc", nesting = "" }
utest namespaceSeparate "/home/user/.local/lib/mcore/stdlib/bool.mc" with
  Some { path = "/home/user/.local/lib/mcore/stdlib/bool.mc", nesting = "" }
utest namespaceSeparate "a/b/c" with
  None {}

let namespaceAdd : Namespace -> String -> Namespace =
    lam namespace. lam last.
    join [namespace, "/", last]

let namespaceLast : Namespace -> Option String =
    lam namespace.
    match namespaceSplit namespace with ([_] ++ _) & s then
        Some (last s)
    else None {}

let namespaceGetSubNamespace : Namespace -> Namespace =
    lam namespace.
    let split = namespaceSplit namespace in
    match split with [] then namespace else
    let rev = reverse split in
    let split = tail rev in
    namespaceRebuild (reverse split)

let namespaceIsRoot : Namespace -> Bool =
    lam namespace.
    match namespaceSeparate namespace with None {} | Some { nesting = "" } then true else false
