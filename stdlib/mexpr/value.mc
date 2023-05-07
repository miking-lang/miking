-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Functions for determining whether a term is a syntactic value.

include "ast.mc"
include "ast-builder.mc"

-- We define values and "guarded" values, following the FreezeML
-- paper (see type-check.mc).  Value terms are syntactic values and
-- terms where no subterm contains a function application.
-- "Guarded" values are value terms which have no frozen variable in
-- tail position, i.e., whose type is guaranteed to have no leading
-- quantifiers.
type Guarded
con Val  : () -> Guarded
con GVal : () -> Guarded

lang IsValue = Ast
  sem isValue : Guarded -> Expr -> Bool
  sem isValue (guarded : Guarded) =
  | t ->
    sfold_Expr_Expr (lam v. lam tm.
      if v then isValue (Val ()) tm else false) true t
end

lang VarIsValue = VarAst
  sem isValue (guarded : Guarded) =
  | TmVar t ->
    switch guarded
    case Val () then true
    case GVal () then not t.frozen
    end
end

lang AppIsValue = AppAst
  sem isValue (guarded : Guarded) =
  | TmApp t -> false
end

lang LamIsValue = LamAst
  sem isValue (guarded : Guarded) =
  | TmLam t -> true
end

lang LetIsValue = LetAst
  sem isValue (guarded : Guarded) =
  | TmLet t ->
    if isValue (Val ()) t.body then isValue guarded t.inexpr
    else false
end

lang RecLetsIsValue = RecLetsAst
  sem isValue (guarded : Guarded) =
  | TmRecLets t ->
    if forAll (lam b. isValue (Val ()) b.body) t.bindings then isValue guarded t.inexpr
    else false
end

lang TypeIsValue = TypeAst
  sem isValue (guarded : Guarded) =
  | TmType t -> isValue guarded t.inexpr
end

lang DataIsValue = DataAst
  sem isValue (guarded : Guarded) =
  | TmConDef t -> isValue guarded t.inexpr
end

lang MatchIsValue = MatchAst
  sem isValue (guarded : Guarded) =
  | TmMatch t ->
    if isValue (Val ()) t.target then
      if isValue guarded t.thn then isValue guarded t.els
      else false
    else false
end

lang UtestIsValue = UtestAst
  sem isValue (guarded : Guarded) =
  | TmUtest t -> isValue guarded t.next
end

lang ExtIsValue = ExtAst
  sem isValue (guarded : Guarded) =
  | TmExt t -> isValue guarded t.inexpr
end

lang MExprIsValue =
  MExprAst + IsValue +
  VarIsValue + AppIsValue + LamIsValue + LetIsValue + RecLetsIsValue +
  TypeIsValue + DataIsValue + MatchIsValue + UtestIsValue + ExtIsValue
end

mexpr

use MExprIsValue in

-- Variables
utest isValue (Val ()) (var_ "a") with true in
utest isValue (GVal ()) (var_ "a") with true in

utest isValue (Val ()) (freeze_ (var_ "a")) with true in
utest isValue (GVal ()) (freeze_ (var_ "a")) with false in

-- Constants
utest isValue (GVal ()) (int_ 0) with true in

-- Application
utest isValue (Val ()) (app_ (var_ "a") (var_ "b")) with false in

-- Lambda
utest isValue (GVal ()) (ulam_ "x" (app_ (var_ "x") (var_ "b"))) with true in

-- Let
utest isValue (Val ()) (bind_ (ulet_ "f" (ulam_ "x" (var_ "x")))
                          (freeze_ (var_ "f"))) with true in
utest isValue (GVal ()) (bind_ (ulet_ "f" (ulam_ "x" (var_ "x")))
                          (freeze_ (var_ "f"))) with false in
utest isValue (Val ()) (bind_ (ulet_ "f" (app_ (var_ "y") (var_ "x")))
                          (var_ "f")) with false in

-- Record
utest isValue (GVal ()) (utuple_ [freeze_ (var_ "x"), int_ 0]) with true in
utest isValue (Val ()) (utuple_ [app_ (var_ "y") (var_ "x"), int_ 0]) with false in

-- Utest
utest isValue (GVal ()) (utest_ (app_ (var_ "y") (var_ "x"))
                           (int_ 0) (int_ 0)) with true in

()
