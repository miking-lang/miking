include "mexpr/ast.mc"
include "mexpr/const-types.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"
include "mexpr/type-annot.mc"
include "mexpr/rewrite/utils.mc"

lang MExprRewrite = MExprAst + MExprEq + MExprConstType
  sem rewriteTerm =
  -- cons e seq -> concat [e] seq
  | TmApp ({lhs = TmApp ({lhs = TmConst ({val = CCons _} & cons),
                          rhs = arg1} & innerApp)} & t) ->
    let concat = TmConst {cons with val = CConcat ()} in
    let elemSeq = TmSeq {
      tms = [arg1],
      ty = TySeq {ty = ty arg1, info = infoTm arg1},
      info = infoTm arg1
    } in
    TmApp {t with lhs = TmApp {{innerApp with lhs = concat}
                                         with rhs = rewriteTerm elemSeq}}
  -- snoc seq e -> concat seq [e]
  | TmApp ({lhs = TmApp ({lhs = TmConst ({val = CSnoc _} & snoc)} & innerApp),
            rhs = arg2} & t) ->
    let concat = TmConst {snoc with val = CConcat ()} in
    let elemSeq = TmSeq {
      tms = [arg2],
      ty = TySeq {ty = ty arg2, info = infoTm arg2},
      info = infoTm arg2
    } in
    TmApp {{t with lhs = TmApp {innerApp with lhs = concat}}
              with rhs = rewriteTerm elemSeq}
  -- match s with [h] ++ t then e1 else match s with [] then e2 else e3 ->
  -- match s with [] then e2 else match s with [h] ++ t then e1 else e3
  | TmMatch ({pat = (PatSeqEdge {prefix = [PatNamed {ident = PName _}],
                                 middle = PName _, postfix = []}) & pat1,
              thn = e1,
              els = TmMatch ({pat = (PatSeqTot {pats = []} & pat2),
                              thn = e2} & innerMatch)} & outerMatch) ->
    if eqExpr innerMatch.target outerMatch.target then
      rewriteTerm
        (TmMatch {{{outerMatch with pat = pat2}
                               with thn = e2}
                               with els = TmMatch {{innerMatch with pat = pat1}
                                                               with thn = e1}})
    else
      TmMatch outerMatch
  -- match s with [h] ++ t then e1 else e2 ->
  -- match s with [] then e2 else match s with [h] ++ t then e1 else never
  -- where e2 != match _ and e2 != never
  | TmMatch ({pat = PatSeqEdge {prefix = [PatNamed {ident = PName _}],
                                middle = PName _, postfix = [],
                                info = patInfo},
              els = !(TmMatch _ | TmNever _)} & t) ->
    let newThn = TmMatch {t with els = TmNever {ty = TyUnknown {info = t.info},
                                                info = t.info}} in
    rewriteTerm
      (TmMatch {{{t with pat = PatSeqTot {pats = [], info = patInfo}}
                   with thn = t.els}
                   with els = newThn})
  -- match s with [] then e1 else match s with [h] ++ t then e2 else never ->
  -- if null s then e1 else
  --   let h = head s in
  --   let t = tail s in
  --   e2
  | TmMatch ({pat = PatSeqTot {pats = []},
              target = t1,
              els = TmMatch {pat = PatSeqEdge {prefix = [PatNamed {ident = PName h}],
                                               middle = PName t, postfix = []},
                             target = t2,
                             thn = innerThn, els = TmNever _}} & matchTm) ->
    let makeConstTerm = lam const : Const. lam info.
      TmConst {val = const, ty = tyWithInfo info (tyConst const),
               info = info}
    in
    if eqExpr t1 t2 then
      let nullApp = TmApp {lhs = makeConstTerm (CNull ()) matchTm.info,
                           rhs = t1,
                           ty = TyBool {info = matchTm.info},
                           info = matchTm.info} in
      let boolPat = PatBool {val = true, info = matchTm.info} in
      let elemTy =
        match ty t1 with TySeq {ty = elemTy} then
          elemTy
        else TyUnknown {info = infoTy (ty t1)} in
      let nameMap = mapFromSeq nameCmp [
        (h, lam info. TmApp {
          lhs = makeConstTerm (CHead ()) info,
          rhs = t1, ty = elemTy, info = info}),
        (t, lam info. TmApp {
          lhs = makeConstTerm (CTail ()) info,
          rhs = t1, ty = ty t1, info = info})] in
      let innerThn = substituteVariables innerThn nameMap in
      TmMatch {{{{matchTm with target = rewriteTerm nullApp}
                          with pat = boolPat}
                          with thn = rewriteTerm matchTm.thn}
                          with els = rewriteTerm innerThn}
    else TmMatch matchTm
  | t -> smap_Expr_Expr rewriteTerm t
end

lang TestLang = MExprRewrite + MExprTypeAnnot + MExprEq + MExprPrettyPrint

mexpr

use TestLang in

let t1 = cons_ (int_ 0) (seq_ []) in
let t2 = concat_ (seq_ [int_ 0]) (seq_ []) in
utest rewriteTerm t1 with t2 using eqExpr in

let t1 = snoc_ (seq_ []) (int_ 0) in
let t2 = concat_ (seq_ []) (seq_ [int_ 0]) in
utest rewriteTerm t1 with t2 using eqExpr in

let s = nameSym "s" in
let h = nameSym "h" in
let t = nameSym "t" in
let outerExprBefore =
  cons_ (app_ (var_ "f") (nvar_ h))
        (appf2_ (var_ "map") (var_ "f") (nvar_ t)) in
let outerExprAfter =
  concat_ (seq_ [app_ (var_ "f") (head_ (nvar_ s))])
          (appf2_ (var_ "map") (var_ "f") (tail_ (nvar_ s))) in
let innerExpr = seq_ [] in
let t1 =
  match_ (nvar_ s)
    (pseqedgen_ [npvar_ h] t [])
    outerExprBefore
    (match_ (nvar_ s)
      (pseqtot_ [])
      innerExpr
      never_) in
let t2 =
  if_ (null_ (nvar_ s))
    innerExpr
    outerExprAfter in
utest rewriteTerm t1 with t2 using eqExpr in

()
