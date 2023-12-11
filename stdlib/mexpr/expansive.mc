-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Functions for determining whether a term is non-expansive.

include "ast.mc"
include "ast-builder.mc"

lang NonExpansive = Ast
  -- We define non-expansive and "guarded" non-expansive terms,
  -- following the FreezeML paper (see type-check.mc).  Non-expansive
  -- terms are syntactic values and terms where no subterm contains a
  -- function application.  "Guarded" non-expansive terms additionally
  -- have no frozen variable in tail position, i.e., the type is
  -- guaranteed to have no leading quantifiers.
  type Guarded = Bool

  sem nonExpansive : Guarded -> Expr -> Bool
  sem nonExpansive (guarded : Guarded) =
  | t ->
    sfold_Expr_Expr (lam v. lam tm.
      if v then nonExpansive false tm else false) true t
end

lang VarNonExpansive = NonExpansive + VarAst
  sem nonExpansive (guarded : Guarded) =
  | TmVar t -> not (and guarded t.frozen)
end

lang AppNonExpansive = NonExpansive + AppAst
  sem nonExpansive (guarded : Guarded) =
  | TmApp t -> false
end

lang LamNonExpansive = NonExpansive + LamAst
  sem nonExpansive (guarded : Guarded) =
  | TmLam t -> true
end

lang LetNonExpansive = NonExpansive + LetAst
  sem nonExpansive (guarded : Guarded) =
  | TmLet t ->
    if nonExpansive false t.body then nonExpansive guarded t.inexpr
    else false
end

lang RecLetsNonExpansive = NonExpansive + RecLetsAst
  sem nonExpansive (guarded : Guarded) =
  | TmRecLets t ->
    if forAll (lam b. nonExpansive false b.body) t.bindings
    then nonExpansive guarded t.inexpr
    else false
end

lang TypeNonExpansive = NonExpansive + TypeAst
  sem nonExpansive (guarded : Guarded) =
  | TmType t -> nonExpansive guarded t.inexpr
end

lang DataNonExpansive = NonExpansive + DataAst
  sem nonExpansive (guarded : Guarded) =
  | TmConDef t -> nonExpansive guarded t.inexpr
end

lang MatchNonExpansive = NonExpansive + MatchAst
  sem nonExpansive (guarded : Guarded) =
  | TmMatch t ->
    if nonExpansive false t.target then
      if nonExpansive guarded t.thn then
        nonExpansive guarded t.els
      else false
    else false
end

lang UtestNonExpansive = NonExpansive + UtestAst
  sem nonExpansive (guarded : Guarded) =
  | TmUtest t -> nonExpansive guarded t.next
end

lang ExtNonExpansive = NonExpansive + ExtAst
  sem nonExpansive (guarded : Guarded) =
  | TmExt t -> nonExpansive guarded t.inexpr
end

lang MExprNonExpansive =
  MExprAst + NonExpansive +
  VarNonExpansive + AppNonExpansive + LamNonExpansive + LetNonExpansive + RecLetsNonExpansive +
  TypeNonExpansive + DataNonExpansive + MatchNonExpansive + UtestNonExpansive + ExtNonExpansive
end

mexpr

use MExprNonExpansive in

-- Variables
utest nonExpansive false (var_ "a") with true in
utest nonExpansive true (var_ "a") with true in

utest nonExpansive false (freeze_ (var_ "a")) with true in
utest nonExpansive true (freeze_ (var_ "a")) with false in

-- Constants
utest nonExpansive true (int_ 0) with true in

-- Application
utest nonExpansive false (app_ (var_ "a") (var_ "b")) with false in

-- Lambda
utest nonExpansive true (ulam_ "x" (app_ (var_ "x") (var_ "b"))) with true in

-- Let
utest nonExpansive false (bind_ (ulet_ "f" (ulam_ "x" (var_ "x")))
                            (freeze_ (var_ "f"))) with true in
utest nonExpansive true (bind_ (ulet_ "f" (ulam_ "x" (var_ "x")))
                           (freeze_ (var_ "f"))) with false in
utest nonExpansive false (bind_ (ulet_ "f" (app_ (var_ "y") (var_ "x")))
                            (var_ "f")) with false in

-- Record
utest nonExpansive true (utuple_ [freeze_ (var_ "x"), int_ 0]) with true in
utest nonExpansive false (utuple_ [app_ (var_ "y") (var_ "x"), int_ 0]) with false in

-- Utest
utest nonExpansive true (utest_ (app_ (var_ "y") (var_ "x"))
                           (int_ 0) (int_ 0)) with true in

()
