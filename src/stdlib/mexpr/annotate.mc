include "../annotate.mc"
include "ast.mc"

lang AnnotateSources = Annotator
  sem annotateAndReadSources : [(Info, Annotation)] -> Output
  sem annotateAndReadSources = | annots ->
    let annots = _collectAnnots annots in
    let sources = mapFoldWithKey
      (lam acc. lam fileSid. lam.
        let filename = sidToString fileSid in
        -- TODO(vipa, 2022-05-17): This is technically a race condition, the
        -- file could be removed in-between the check and the read, but
        -- there's no better way to handle it atm.
        if fileExists filename then
          snoc acc (fileSid, readFile filename)
        else
          acc)
      []
      annots in
    _annotateSources sources annots

  sem annotateSources : Map String String -> [(Info, Annotation)] -> Output
  sem annotateSources sources = | annots ->
    let sources = mapFoldWithKey (lam acc. lam k. lam v. snoc acc (stringToSid k, v)) [] sources in
    let annots = _collectAnnots annots in
    _annotateSources sources annots

  sem _annotateSources : [(SID, String)] -> Map SID [(InfoRecord, Annotation)] -> Output
  sem _annotateSources sources = | annots ->
    -- NOTE(vipa, 2022-10-07): This sorts ranges after ranges that
    -- fully contain them, i.e., it's kind of an ordering by subset
    let annotCmp = lam a. lam b.
      let a = a.0 in
      let b = b.0 in
      let res = subi a.row1 b.row1 in
      if neqi res 0 then res else
      let res = subi a.col1 b.col1 in
      if neqi res 0 then res else
      let res = subi b.row2 a.row2 in
      if neqi res 0 then res else
      subi b.col2 a.col2
    in
    let res =
      foldl
        (lam acc. lam pair.
          match pair with (filename, src) in
          let doc =
            match mapLookup filename annots with Some annots then
              let annots =
                if gti (length annots) 20000 then
                  printError (join ["WARNING: too many annotations for file '", sidToString filename, "', skipping all of them\n"]);
                  flushStderr ();
                  []
                else annots in
              -- NOTE(vipa, 2023-06-19): annotations are frequently
              -- already mostly sorted, in which case quickSort (which
              -- is the default sort) is quadratic with the chosen
              -- partitioning scheme
              let annots = mergeSort annotCmp annots in
              let pos = initPos "" in
              let st =
                { stack = [{endPos = (addi (length src) 1, 0), res = "", annot = ""}]
                , annots = annots
                , pos = (pos.row, pos.col)
                } in
              _annotateSource src st
            else src
          in concat acc (document (sidToString filename) doc))
        ""
        sources
    in finalize res

  sem _collectAnnots : [(Info, Annotation)] -> Map SID [(InfoRecord, Annotation)]
  sem _collectAnnots = | annots ->
    foldl
      (lam acc. lam annot.
        match annot with (Info x, annot) then
          let sid = stringToSid x.filename in
          mapInsertWith concat sid [(x, annot)] acc
        else acc)
      (mapEmpty subi)
      annots

  type InfoRecord = {filename: String, row1: Int, col1: Int, row2: Int, col2: Int}
  type Pos = (Int, Int)
  type StackItem = {endPos : Pos, res : Output, annot : Annotation}
  type State =
    { stack : [StackItem]
    , annots : [(InfoRecord, Annotation)]
    , pos : Pos
    }
  sem _annotateSource : String -> State -> Output
  sem _annotateSource input = | st ->
    let leqPos = lam a. lam b.
      if eqi a.0 b.0
      then leqi a.1 b.1
      else lti a.0 b.0 in
    match input with [] then _popAll st.stack else
    match st.stack with stack ++ [top] in
    if leqPos top.endPos st.pos then
      -- We've reached the end of the current tag, reduce
      match stack with stack ++ [newTop] in
      let res = concat newTop.res (annotate top.annot top.res) in
      _annotateSource input {st with stack = snoc stack {newTop with res = res}}
    else
      match
        match st.annots with [(info, annot)] ++ annots then
          if leqPos (info.row1, info.col1) st.pos then
            let item = {endPos = (info.row2, info.col2), res = "", annot = annot} in
            Some {st with stack = snoc st.stack item, annots = annots}
          else None ()
        else None ()
      with Some st then
        -- We've determined that we're opening a new tag
        _annotateSource input st
      else
        -- We're not opening a new tag, shift a character
        match input with [c] ++ input in
        let top = {top with res = concat top.res (escapeContent [c])} in
        let st = {st with pos = _advancePos st.pos c, stack = snoc stack top} in
        _annotateSource input st

  sem _popAll : [StackItem] -> Output
  sem _popAll =
  | [] -> error "Impossible"
  | [item] -> item.res
  | stack ++ [top, item] ->
    _popAll (snoc stack {top with res = concat top.res item.res})

  sem _advancePos : Pos -> Char -> Pos
  sem _advancePos pos =
  | '\n' -> (addi pos.0 1, 0)
  | _ -> (pos.0, addi pos.1 1)
end

lang AnnotateMExprBase = AnnotateSources + Ast
  sem exprAnnot : Expr -> Option Annotation
  sem patAnnot : Pat -> Option Annotation
  sem typeAnnot : Type -> Option Annotation

  sem annotateMExpr : Expr -> Output
  sem annotateMExpr = | tm ->
    let annots = _exprAnnots tm in
    annotateAndReadSources annots

  sem _exprAnnots : Expr -> [(Info, Annotation)]
  sem _exprAnnots = | tm ->
    let res = match exprAnnot tm with Some annot
      then [(infoTm tm, annot)]
      else [] in
    let res = sfold_Expr_Expr (lam acc. lam e. concat acc (_exprAnnots e)) res tm in
    let res = sfold_Expr_Type (lam acc. lam t. concat acc (_typeAnnots t)) res tm in
    let res = sfold_Expr_Pat (lam acc. lam p. concat acc (_patAnnots p)) res tm in
    res

  sem _patAnnots : Pat -> [(Info, Annotation)]
  sem _patAnnots = | pat ->
    let res = match patAnnot pat with Some annot
      then [(infoPat pat, annot)]
      else [] in
    let res = sfold_Pat_Expr (lam acc. lam e. concat acc (_exprAnnots e)) res pat in
    let res = sfold_Pat_Type (lam acc. lam t. concat acc (_typeAnnots t)) res pat in
    let res = sfold_Pat_Pat (lam acc. lam p. concat acc (_patAnnots p)) res pat in
    res

  sem _typeAnnots : Type -> [(Info, Annotation)]
  sem _typeAnnots = | ty ->
    let res = match typeAnnot ty with Some annot
      then [(infoTy ty, annot)]
      else [] in
    let res = sfold_Type_Type (lam acc. lam t. concat acc (_typeAnnots t)) res ty in
    res
end
