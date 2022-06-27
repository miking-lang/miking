-- This file defines a function `indexGen` that constructs a map from all term
-- variable names in a program to unique integers from 0 to n-1, where n is the
-- total number of distinct variable names in the program. Currently, this is
-- mainly useful for constant-time tensor lookups in `cfa.mc`.

include "ast.mc"
include "boot-parser.mc"
include "map.mc"
include "option.mc"

lang Index = Ast

  type IndexMap = {
    name2int: Map Name Int,
    int2name: Tensor[Name]
  }

  type IndexAcc = {
    map: Map Name Int,
    nextIndex: Int
  }

  sem emptyAcc: () -> IndexAcc
  sem emptyAcc =
  | _ -> { map = mapEmpty nameCmp, nextIndex = 0 }

  sem addKey: Name -> IndexAcc -> IndexAcc
  sem addKey (name: Name) =
  | acc ->
    if mapMem name acc.map then acc
    else {{acc with map = mapInsert name acc.nextIndex acc.map }
               with nextIndex = addi 1 acc.nextIndex }

  -- Entry point
  sem indexGen: Expr -> IndexMap
  sem indexGen =
  | t ->
    let acc = indexGenH (emptyAcc ()) t in
    let name2int = acc.map in
    let int2name: Tensor[Name] =
      tensorCreateDense [acc.nextIndex] (lam. nameNoSym "t") in
    mapMapWithKey (lam n. lam i. tensorLinearSetExn int2name i n) name2int;
    {name2int = name2int, int2name = int2name}

  sem indexGenH: IndexAcc -> Expr -> IndexAcc
  sem indexGenH (acc: IndexAcc) =
  | t -> let acc = indexAdd acc t in sfold_Expr_Expr indexGenH acc t

  sem indexAdd: IndexAcc -> Expr -> IndexAcc
  sem indexAdd (acc: IndexAcc) =
  | t -> acc

end

-----------
-- TERMS --
-----------

lang VarIndex = Index + VarAst
  sem indexAdd (acc: IndexAcc) =
  | TmVar { ident = ident } -> addKey ident acc
end

lang LamIndex = Index + LamAst
  sem indexAdd (acc: IndexAcc) =
  | TmLam { ident = ident } -> addKey ident acc
end

lang LetIndex = Index + LetAst
  sem indexAdd (acc: IndexAcc) =
  | TmLet { ident = ident } -> addKey ident acc
end

lang RecLetsIndex = Index + RecLetsAst
  sem indexAdd (acc: IndexAcc) =
  | TmRecLets { bindings = bindings } ->
    foldl (lam acc: IndexAcc. lam b: RecLetBinding. addKey b.ident acc)
      acc bindings
end

lang ExtIndex = Index + ExtAst
  sem indexAdd (acc: IndexAcc) =
  | TmExt { ident = ident } -> addKey ident acc
end

lang TypeIndex = Index + TypeAst
  sem indexAdd (acc: IndexAcc) =
  | TmType { ident = ident } -> addKey ident acc
end

lang DataIndex = Index + DataAst
  sem indexAdd (acc: IndexAcc) =
  | TmConDef { ident = ident } -> addKey ident acc
  | TmConApp { ident = ident } -> addKey ident acc
end

lang MatchIndex = Index + MatchAst
  sem indexAdd (acc: IndexAcc) =
  | TmMatch { pat = pat } -> patIndexAdd acc pat

  sem patIndexAdd: IndexAcc -> Pat -> IndexAcc
  sem patIndexAdd (acc: IndexAcc) =
  | p -> sfold_Pat_Pat patIndexAdd acc p
end

--------------
-- PATTERNS --
--------------

lang NamedPatIndex = Index + NamedPat
  sem patIndexAdd (acc: IndexAcc) =
  | PatNamed { ident = PName name } -> addKey name acc
end

--------------------------
-- MEXPR INDEX FRAGMENT --
--------------------------

lang MExprIndex =
  Index + VarIndex + LamIndex + LetIndex + RecLetsIndex + ExtIndex + DataIndex +
  TypeIndex + MatchIndex + NamedPatIndex
end

-----------
-- TESTS --
-----------

lang Test = MExprIndex + BootParser
end

mexpr
use Test in

let test: String -> IndexMap = lam s.
  let t = parseMExprStringKeywords [] s in
  indexGen t
in

let eqTest: IndexMap -> [(String,Int)] -> Bool = lam i1. lam i2.
  let name2int: Map Name Int = mapFromSeq nameCmp
    (map (lam e. (nameNoSym e.0, e.1)) i2) in
  let int2name: Tensor[Name] =
    tensorCreateDense [mapSize name2int] (lam. nameNoSym "t") in
  iter (lam e. tensorSetExn int2name [e.1] (nameNoSym e.0)) i2;
  and (mapEq eqi i1.name2int name2int) (tensorEq nameEq i1.int2name int2name)
in

utest test "let x = 1 in ()" with [
  ("x", 0)
] using eqTest in

utest test "let x = lam y. let z = 1 in () in ()" with [
  ("x", 0),
  ("y", 1),
  ("z", 2)
] using eqTest in

utest test "
  recursive
    let f = lam x. let xv = 1 in ()
    let g = lam y. let yv = 2 in ()
  in ()
------------------------" with [
  ("f", 0),
  ("g", 1),
  ("x", 2),
  ("xv", 3),
  ("y", 4),
  ("yv", 5)
] using eqTest in

utest test "
  external x : Int -> Int in
  ()
------------------------" with [
  ("x", 0)
] using eqTest in

utest test "
  match 1 with x in
  ()
------------------------" with [
  ("x", 0)
] using eqTest in

utest test "
  match 1 with _ in
  ()
------------------------" with []
using eqTest in

utest test "
  let x = addi 1 2 in
  let f = lam y. addi 1 y in
  let sum1 = addf 1.0 1.0 in
  let sum2 = f x 1.0 in
  let res = addf sum1 sum2 in
  res
------------------------" with [
  ("x", 0),
  ("f", 1),
  ("y", 2),
  ("sum1", 3),
  ("sum2", 4),
  ("res", 5)
] using eqTest in

utest test "
  type T in
  con C: (a -> a) -> T in
  C ()
------------------------" with [
  ("T", 0),
  ("C", 1)
] using eqTest in

()
