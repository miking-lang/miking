-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Transforms an MExpr expression where sequence literals (TmSeq) are replaced
-- by a call to hcreate.

include "ast.mc"
include "pprint.mc"
include "ast-builder.mc"
include "common.mc"
include "utesttrans.mc"

-- TODO: don't recurse in utest?
lang SeqTransformer = SeqAst + VarAst + AppAst + UnknownTypeAst
  sem seqTransform =
  | t ->
    let name =
      match findName "hcreate" t with Some name then name
      else nameSym "hcreateDef"
    in _seqTransform name t

  -- TODO: recurse
  sem _seqTransform (hcreate : Name) =
  | TmSeq {tms = tms, info = info} ->
    TmApp
      { lhs = TmApp { lhs = TmVar {ident = hcreate, ty = tyunknown_, info = info}
                    , rhs = int_ (length tms)
                    , ty = tyunknown_
                    , info = info
                    }
      , rhs =
        let i = nameSym "i" in
        nulam_ i (get_ (seq_ (map (_seqTransform hcreate) tms)) (nvar_ i))
      , ty = tyunknown_
      , info = info
      }
  | t -> smap_Expr_Expr (_seqTransform hcreate) t
end

lang TestLang = MExprAst + SeqTransformer + MExprPrettyPrint

mexpr

use TestLang in

let ast = seq_ [int_ 1, int_ 2, int_ 3] in

let ast = seqTransform ast in

printLn (expr2str ast);

()
