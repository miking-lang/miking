include "seq.mc"
include "parser/ll1.mc"
include "parser/breakable.mc"
include "mexpr/info.mc"
include "name.mc"
include "basic-types.mc"
include "option.mc"
include "parser/lexer.mc"
include "common.mc"
lang SelfhostBaseAst
  syn SHExpr =
  syn SHRegex =
  syn SHDecl =
  syn SHFile =
  sem smapAccumL_SHFile_SHFile : all a. (a -> SHFile -> (a, SHFile)) -> a -> SHFile -> (a, SHFile)
sem smapAccumL_SHFile_SHFile f acc =
  | x ->
    (acc, x)
  sem smap_SHFile_SHFile : (SHFile -> SHFile) -> SHFile -> SHFile
sem smap_SHFile_SHFile f =
  | x ->
    (smapAccumL_SHFile_SHFile (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHFile_SHFile : all a. (a -> SHFile -> a) -> a -> SHFile -> a
sem sfold_SHFile_SHFile f acc =
  | x ->
    (smapAccumL_SHFile_SHFile (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHFile_SHDecl : all a. (a -> SHDecl -> (a, SHDecl)) -> a -> SHFile -> (a, SHFile)
sem smapAccumL_SHFile_SHDecl f acc =
  | x ->
    (acc, x)
  sem smap_SHFile_SHDecl : (SHDecl -> SHDecl) -> SHFile -> SHFile
sem smap_SHFile_SHDecl f =
  | x ->
    (smapAccumL_SHFile_SHDecl (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHFile_SHDecl : all a. (a -> SHDecl -> a) -> a -> SHFile -> a
sem sfold_SHFile_SHDecl f acc =
  | x ->
    (smapAccumL_SHFile_SHDecl (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHFile_SHRegex : all a. (a -> SHRegex -> (a, SHRegex)) -> a -> SHFile -> (a, SHFile)
sem smapAccumL_SHFile_SHRegex f acc =
  | x ->
    (acc, x)
  sem smap_SHFile_SHRegex : (SHRegex -> SHRegex) -> SHFile -> SHFile
sem smap_SHFile_SHRegex f =
  | x ->
    (smapAccumL_SHFile_SHRegex (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHFile_SHRegex : all a. (a -> SHRegex -> a) -> a -> SHFile -> a
sem sfold_SHFile_SHRegex f acc =
  | x ->
    (smapAccumL_SHFile_SHRegex (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHFile_SHExpr : all a. (a -> SHExpr -> (a, SHExpr)) -> a -> SHFile -> (a, SHFile)
sem smapAccumL_SHFile_SHExpr f acc =
  | x ->
    (acc, x)
  sem smap_SHFile_SHExpr : (SHExpr -> SHExpr) -> SHFile -> SHFile
sem smap_SHFile_SHExpr f =
  | x ->
    (smapAccumL_SHFile_SHExpr (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHFile_SHExpr : all a. (a -> SHExpr -> a) -> a -> SHFile -> a
sem sfold_SHFile_SHExpr f acc =
  | x ->
    (smapAccumL_SHFile_SHExpr (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHDecl_SHFile : all a. (a -> SHFile -> (a, SHFile)) -> a -> SHDecl -> (a, SHDecl)
sem smapAccumL_SHDecl_SHFile f acc =
  | x ->
    (acc, x)
  sem smap_SHDecl_SHFile : (SHFile -> SHFile) -> SHDecl -> SHDecl
sem smap_SHDecl_SHFile f =
  | x ->
    (smapAccumL_SHDecl_SHFile (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHDecl_SHFile : all a. (a -> SHFile -> a) -> a -> SHDecl -> a
sem sfold_SHDecl_SHFile f acc =
  | x ->
    (smapAccumL_SHDecl_SHFile (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHDecl_SHDecl : all a. (a -> SHDecl -> (a, SHDecl)) -> a -> SHDecl -> (a, SHDecl)
sem smapAccumL_SHDecl_SHDecl f acc =
  | x ->
    (acc, x)
  sem smap_SHDecl_SHDecl : (SHDecl -> SHDecl) -> SHDecl -> SHDecl
sem smap_SHDecl_SHDecl f =
  | x ->
    (smapAccumL_SHDecl_SHDecl (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHDecl_SHDecl : all a. (a -> SHDecl -> a) -> a -> SHDecl -> a
sem sfold_SHDecl_SHDecl f acc =
  | x ->
    (smapAccumL_SHDecl_SHDecl (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHDecl_SHRegex : all a. (a -> SHRegex -> (a, SHRegex)) -> a -> SHDecl -> (a, SHDecl)
sem smapAccumL_SHDecl_SHRegex f acc =
  | x ->
    (acc, x)
  sem smap_SHDecl_SHRegex : (SHRegex -> SHRegex) -> SHDecl -> SHDecl
sem smap_SHDecl_SHRegex f =
  | x ->
    (smapAccumL_SHDecl_SHRegex (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHDecl_SHRegex : all a. (a -> SHRegex -> a) -> a -> SHDecl -> a
sem sfold_SHDecl_SHRegex f acc =
  | x ->
    (smapAccumL_SHDecl_SHRegex (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHDecl_SHExpr : all a. (a -> SHExpr -> (a, SHExpr)) -> a -> SHDecl -> (a, SHDecl)
sem smapAccumL_SHDecl_SHExpr f acc =
  | x ->
    (acc, x)
  sem smap_SHDecl_SHExpr : (SHExpr -> SHExpr) -> SHDecl -> SHDecl
sem smap_SHDecl_SHExpr f =
  | x ->
    (smapAccumL_SHDecl_SHExpr (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHDecl_SHExpr : all a. (a -> SHExpr -> a) -> a -> SHDecl -> a
sem sfold_SHDecl_SHExpr f acc =
  | x ->
    (smapAccumL_SHDecl_SHExpr (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHRegex_SHFile : all a. (a -> SHFile -> (a, SHFile)) -> a -> SHRegex -> (a, SHRegex)
sem smapAccumL_SHRegex_SHFile f acc =
  | x ->
    (acc, x)
  sem smap_SHRegex_SHFile : (SHFile -> SHFile) -> SHRegex -> SHRegex
sem smap_SHRegex_SHFile f =
  | x ->
    (smapAccumL_SHRegex_SHFile (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHRegex_SHFile : all a. (a -> SHFile -> a) -> a -> SHRegex -> a
sem sfold_SHRegex_SHFile f acc =
  | x ->
    (smapAccumL_SHRegex_SHFile (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHRegex_SHDecl : all a. (a -> SHDecl -> (a, SHDecl)) -> a -> SHRegex -> (a, SHRegex)
sem smapAccumL_SHRegex_SHDecl f acc =
  | x ->
    (acc, x)
  sem smap_SHRegex_SHDecl : (SHDecl -> SHDecl) -> SHRegex -> SHRegex
sem smap_SHRegex_SHDecl f =
  | x ->
    (smapAccumL_SHRegex_SHDecl (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHRegex_SHDecl : all a. (a -> SHDecl -> a) -> a -> SHRegex -> a
sem sfold_SHRegex_SHDecl f acc =
  | x ->
    (smapAccumL_SHRegex_SHDecl (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHRegex_SHRegex : all a. (a -> SHRegex -> (a, SHRegex)) -> a -> SHRegex -> (a, SHRegex)
sem smapAccumL_SHRegex_SHRegex f acc =
  | x ->
    (acc, x)
  sem smap_SHRegex_SHRegex : (SHRegex -> SHRegex) -> SHRegex -> SHRegex
sem smap_SHRegex_SHRegex f =
  | x ->
    (smapAccumL_SHRegex_SHRegex (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHRegex_SHRegex : all a. (a -> SHRegex -> a) -> a -> SHRegex -> a
sem sfold_SHRegex_SHRegex f acc =
  | x ->
    (smapAccumL_SHRegex_SHRegex (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHRegex_SHExpr : all a. (a -> SHExpr -> (a, SHExpr)) -> a -> SHRegex -> (a, SHRegex)
sem smapAccumL_SHRegex_SHExpr f acc =
  | x ->
    (acc, x)
  sem smap_SHRegex_SHExpr : (SHExpr -> SHExpr) -> SHRegex -> SHRegex
sem smap_SHRegex_SHExpr f =
  | x ->
    (smapAccumL_SHRegex_SHExpr (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHRegex_SHExpr : all a. (a -> SHExpr -> a) -> a -> SHRegex -> a
sem sfold_SHRegex_SHExpr f acc =
  | x ->
    (smapAccumL_SHRegex_SHExpr (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHExpr_SHFile : all a. (a -> SHFile -> (a, SHFile)) -> a -> SHExpr -> (a, SHExpr)
sem smapAccumL_SHExpr_SHFile f acc =
  | x ->
    (acc, x)
  sem smap_SHExpr_SHFile : (SHFile -> SHFile) -> SHExpr -> SHExpr
sem smap_SHExpr_SHFile f =
  | x ->
    (smapAccumL_SHExpr_SHFile (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHExpr_SHFile : all a. (a -> SHFile -> a) -> a -> SHExpr -> a
sem sfold_SHExpr_SHFile f acc =
  | x ->
    (smapAccumL_SHExpr_SHFile (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHExpr_SHDecl : all a. (a -> SHDecl -> (a, SHDecl)) -> a -> SHExpr -> (a, SHExpr)
sem smapAccumL_SHExpr_SHDecl f acc =
  | x ->
    (acc, x)
  sem smap_SHExpr_SHDecl : (SHDecl -> SHDecl) -> SHExpr -> SHExpr
sem smap_SHExpr_SHDecl f =
  | x ->
    (smapAccumL_SHExpr_SHDecl (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHExpr_SHDecl : all a. (a -> SHDecl -> a) -> a -> SHExpr -> a
sem sfold_SHExpr_SHDecl f acc =
  | x ->
    (smapAccumL_SHExpr_SHDecl (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHExpr_SHRegex : all a. (a -> SHRegex -> (a, SHRegex)) -> a -> SHExpr -> (a, SHExpr)
sem smapAccumL_SHExpr_SHRegex f acc =
  | x ->
    (acc, x)
  sem smap_SHExpr_SHRegex : (SHRegex -> SHRegex) -> SHExpr -> SHExpr
sem smap_SHExpr_SHRegex f =
  | x ->
    (smapAccumL_SHExpr_SHRegex (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHExpr_SHRegex : all a. (a -> SHRegex -> a) -> a -> SHExpr -> a
sem sfold_SHExpr_SHRegex f acc =
  | x ->
    (smapAccumL_SHExpr_SHRegex (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem smapAccumL_SHExpr_SHExpr : all a. (a -> SHExpr -> (a, SHExpr)) -> a -> SHExpr -> (a, SHExpr)
sem smapAccumL_SHExpr_SHExpr f acc =
  | x ->
    (acc, x)
  sem smap_SHExpr_SHExpr : (SHExpr -> SHExpr) -> SHExpr -> SHExpr
sem smap_SHExpr_SHExpr f =
  | x ->
    (smapAccumL_SHExpr_SHExpr (lam #var"".
          lam x.
            ({}, f x)) {} x).1
  sem sfold_SHExpr_SHExpr : all a. (a -> SHExpr -> a) -> a -> SHExpr -> a
sem sfold_SHExpr_SHExpr f acc =
  | x ->
    (smapAccumL_SHExpr_SHExpr (lam acc.
          lam x.
            (f acc x, x)) acc x).0
  sem get_SHFile_info : SHFile -> Info
sem get_SHFile_info =
  sem set_SHFile_info : Info -> SHFile -> SHFile
sem set_SHFile_info val =
  sem mapAccum_SHFile_info : all a. (a -> Info -> (a, Info)) -> a -> SHFile -> (a, SHFile)
sem mapAccum_SHFile_info f acc =
  | target ->
    match
      f acc (get_SHFile_info target)
    with
      (acc, val)
    in
    (acc, set_SHFile_info val target)
  sem map_SHFile_info : (Info -> Info) -> SHFile -> SHFile
sem map_SHFile_info f =
  | target ->
    set_SHFile_info (f (get_SHFile_info target)) target
  sem get_SHDecl_info : SHDecl -> Info
sem get_SHDecl_info =
  sem set_SHDecl_info : Info -> SHDecl -> SHDecl
sem set_SHDecl_info val =
  sem mapAccum_SHDecl_info : all a. (a -> Info -> (a, Info)) -> a -> SHDecl -> (a, SHDecl)
sem mapAccum_SHDecl_info f acc =
  | target ->
    match
      f acc (get_SHDecl_info target)
    with
      (acc, val)
    in
    (acc, set_SHDecl_info val target)
  sem map_SHDecl_info : (Info -> Info) -> SHDecl -> SHDecl
sem map_SHDecl_info f =
  | target ->
    set_SHDecl_info (f (get_SHDecl_info target)) target
  sem get_SHRegex_info : SHRegex -> Info
sem get_SHRegex_info =
  sem set_SHRegex_info : Info -> SHRegex -> SHRegex
sem set_SHRegex_info val =
  sem mapAccum_SHRegex_info : all a. (a -> Info -> (a, Info)) -> a -> SHRegex -> (a, SHRegex)
sem mapAccum_SHRegex_info f acc =
  | target ->
    match
      f acc (get_SHRegex_info target)
    with
      (acc, val)
    in
    (acc, set_SHRegex_info val target)
  sem map_SHRegex_info : (Info -> Info) -> SHRegex -> SHRegex
sem map_SHRegex_info f =
  | target ->
    set_SHRegex_info (f (get_SHRegex_info target)) target
  sem get_SHExpr_info : SHExpr -> Info
sem get_SHExpr_info =
  sem set_SHExpr_info : Info -> SHExpr -> SHExpr
sem set_SHExpr_info val =
  sem mapAccum_SHExpr_info : all a. (a -> Info -> (a, Info)) -> a -> SHExpr -> (a, SHExpr)
sem mapAccum_SHExpr_info f acc =
  | target ->
    match
      f acc (get_SHExpr_info target)
    with
      (acc, val)
    in
    (acc, set_SHExpr_info val target)
  sem map_SHExpr_info : (Info -> Info) -> SHExpr -> SHExpr
sem map_SHExpr_info f =
  | target ->
    set_SHExpr_info (f (get_SHExpr_info target)) target
end
lang LangSHFileAst =
  SelfhostBaseAst
  type LangSHFileRecord =
    {info: Info, name: {i: Info, v: String}, decls: [SHDecl]}
  syn SHFile +=
  | LangSHFile LangSHFileRecord
  sem smapAccumL_SHFile_SHDecl f acc +=
  | LangSHFile x ->
    match
      match
        let decls = x.decls in
        mapAccumL
          (lam acc1.
             lam x1: SHDecl.
               f acc1 x1)
          acc
          decls
      with
        (acc, decls)
      in
      (acc, { x with decls = decls })
    with
      (acc, x)
    in
    (acc, LangSHFile
        x)
  sem get_SHFile_info +=
  | LangSHFile target ->
    target.info
  sem set_SHFile_info val +=
  | LangSHFile target ->
    LangSHFile
      { target with info = val }
end
lang StartSHDeclAst =
  SelfhostBaseAst
  type StartSHDeclRecord =
    {info: Info, name: {i: Info, v: Name}}
  syn SHDecl +=
  | StartSHDecl StartSHDeclRecord
  sem get_SHDecl_info +=
  | StartSHDecl target ->
    target.info
  sem set_SHDecl_info val +=
  | StartSHDecl target ->
    StartSHDecl
      { target with info = val }
end
lang IncludeSHDeclAst =
  SelfhostBaseAst
  type IncludeSHDeclRecord =
    {info: Info, path: {i: Info, v: String}}
  syn SHDecl +=
  | IncludeSHDecl IncludeSHDeclRecord
  sem get_SHDecl_info +=
  | IncludeSHDecl target ->
    target.info
  sem set_SHDecl_info val +=
  | IncludeSHDecl target ->
    IncludeSHDecl
      { target with info = val }
end
lang TypeSHDeclAst =
  SelfhostBaseAst
  type TypeSHDeclRecord =
    {info: Info, name: {i: Info, v: Name}, properties: [{val: SHExpr, name: {i: Info, v: String}}]}
  syn SHDecl +=
  | TypeSHDecl TypeSHDeclRecord
  sem smapAccumL_SHDecl_SHExpr f acc +=
  | TypeSHDecl x ->
    match
      match
        let properties = x.properties in
        mapAccumL
          (lam acc1.
             lam x1: {val: SHExpr, name: {i: Info, v: String}}.
               match
                 let val1 = x1.val in
                 f acc1 val1
               with
                 (acc1, val1)
               in
               (acc1, { x1 with val = val1 }))
          acc
          properties
      with
        (acc, properties)
      in
      (acc, { x with properties = properties })
    with
      (acc, x)
    in
    (acc, TypeSHDecl
        x)
  sem get_SHDecl_info +=
  | TypeSHDecl target ->
    target.info
  sem set_SHDecl_info val +=
  | TypeSHDecl target ->
    TypeSHDecl
      { target with info = val }
end
lang TokenSHDeclAst =
  SelfhostBaseAst
  type TokenSHDeclRecord =
    {info: Info, name: Option {i: Info, v: Name}, properties: [{val: SHExpr, name: {i: Info, v: String}}]}
  syn SHDecl +=
  | TokenSHDecl TokenSHDeclRecord
  sem smapAccumL_SHDecl_SHExpr f acc +=
  | TokenSHDecl x ->
    match
      match
        let properties = x.properties in
        mapAccumL
          (lam acc1.
             lam x1: {val: SHExpr, name: {i: Info, v: String}}.
               match
                 let val1 = x1.val in
                 f acc1 val1
               with
                 (acc1, val1)
               in
               (acc1, { x1 with val = val1 }))
          acc
          properties
      with
        (acc, properties)
      in
      (acc, { x with properties = properties })
    with
      (acc, x)
    in
    (acc, TokenSHDecl
        x)
  sem get_SHDecl_info +=
  | TokenSHDecl target ->
    target.info
  sem set_SHDecl_info val +=
  | TokenSHDecl target ->
    TokenSHDecl
      { target with info = val }
end
lang PrecedenceTableSHDeclAst =
  SelfhostBaseAst
  type PrecedenceTableSHDeclRecord =
    {info: Info, levels: [{noeq: Option Info, operators: [{i: Info, v: Name}]}], exceptions: [{lefts: [{i: Info, v: Name}], rights: [{i: Info, v: Name}]}]}
  syn SHDecl +=
  | PrecedenceTableSHDecl PrecedenceTableSHDeclRecord
  sem get_SHDecl_info +=
  | PrecedenceTableSHDecl target ->
    target.info
  sem set_SHDecl_info val +=
  | PrecedenceTableSHDecl target ->
    PrecedenceTableSHDecl
      { target with info = val }
end
lang ProductionSHDeclAst =
  SelfhostBaseAst
  type ProductionSHDeclRecord =
    {nt: {i: Info, v: Name}, info: Info, kinf: Option Info, name: {i: Info, v: Name}, assoc: Option {i: Info, v: String}, kpref: Option Info, kprod: Option Info, regex: SHRegex, kpostf: Option Info}
  syn SHDecl +=
  | ProductionSHDecl ProductionSHDeclRecord
  sem smapAccumL_SHDecl_SHRegex f acc +=
  | ProductionSHDecl x ->
    match
      match
        let regex = x.regex in
        f acc regex
      with
        (acc, regex)
      in
      (acc, { x with regex = regex })
    with
      (acc, x)
    in
    (acc, ProductionSHDecl
        x)
  sem get_SHDecl_info +=
  | ProductionSHDecl target ->
    target.info
  sem set_SHDecl_info val +=
  | ProductionSHDecl target ->
    ProductionSHDecl
      { target with info = val }
end
lang RecordSHRegexAst =
  SelfhostBaseAst
  type RecordSHRegexRecord =
    {info: Info, regex: SHRegex}
  syn SHRegex +=
  | RecordSHRegex RecordSHRegexRecord
  sem smapAccumL_SHRegex_SHRegex f acc +=
  | RecordSHRegex x ->
    match
      match
        let regex = x.regex in
        f acc regex
      with
        (acc, regex)
      in
      (acc, { x with regex = regex })
    with
      (acc, x)
    in
    (acc, RecordSHRegex
        x)
  sem get_SHRegex_info +=
  | RecordSHRegex target ->
    target.info
  sem set_SHRegex_info val +=
  | RecordSHRegex target ->
    RecordSHRegex
      { target with info = val }
end
lang EmptySHRegexAst =
  SelfhostBaseAst
  type EmptySHRegexRecord =
    {info: Info}
  syn SHRegex +=
  | EmptySHRegex EmptySHRegexRecord
  sem get_SHRegex_info +=
  | EmptySHRegex target ->
    target.info
  sem set_SHRegex_info val +=
  | EmptySHRegex target ->
    EmptySHRegex
      { target with info = val }
end
lang LiteralSHRegexAst =
  SelfhostBaseAst
  type LiteralSHRegexRecord =
    {val: {i: Info, v: String}, info: Info}
  syn SHRegex +=
  | LiteralSHRegex LiteralSHRegexRecord
  sem get_SHRegex_info +=
  | LiteralSHRegex target ->
    target.info
  sem set_SHRegex_info val +=
  | LiteralSHRegex target ->
    LiteralSHRegex
      { target with info = val }
end
lang TokenSHRegexAst =
  SelfhostBaseAst
  type TokenSHRegexRecord =
    {arg: Option SHExpr, info: Info, name: {i: Info, v: Name}}
  syn SHRegex +=
  | TokenSHRegex TokenSHRegexRecord
  sem smapAccumL_SHRegex_SHExpr f acc +=
  | TokenSHRegex x ->
    match
      match
        let arg = x.arg in
        optionMapAccum
          (lam acc1.
             lam x1.
               f acc1 x1)
          acc
          arg
      with
        (acc, arg)
      in
      (acc, { x with arg = arg })
    with
      (acc, x)
    in
    (acc, TokenSHRegex
        x)
  sem get_SHRegex_info +=
  | TokenSHRegex target ->
    target.info
  sem set_SHRegex_info val +=
  | TokenSHRegex target ->
    TokenSHRegex
      { target with info = val }
end
lang RepeatPlusSHRegexAst =
  SelfhostBaseAst
  type RepeatPlusSHRegexRecord =
    {info: Info, left: SHRegex}
  syn SHRegex +=
  | RepeatPlusSHRegex RepeatPlusSHRegexRecord
  sem smapAccumL_SHRegex_SHRegex f acc +=
  | RepeatPlusSHRegex x ->
    match
      match
        let left = x.left in
        f acc left
      with
        (acc, left)
      in
      (acc, { x with left = left })
    with
      (acc, x)
    in
    (acc, RepeatPlusSHRegex
        x)
  sem get_SHRegex_info +=
  | RepeatPlusSHRegex target ->
    target.info
  sem set_SHRegex_info val +=
  | RepeatPlusSHRegex target ->
    RepeatPlusSHRegex
      { target with info = val }
end
lang RepeatStarSHRegexAst =
  SelfhostBaseAst
  type RepeatStarSHRegexRecord =
    {info: Info, left: SHRegex}
  syn SHRegex +=
  | RepeatStarSHRegex RepeatStarSHRegexRecord
  sem smapAccumL_SHRegex_SHRegex f acc +=
  | RepeatStarSHRegex x ->
    match
      match
        let left = x.left in
        f acc left
      with
        (acc, left)
      in
      (acc, { x with left = left })
    with
      (acc, x)
    in
    (acc, RepeatStarSHRegex
        x)
  sem get_SHRegex_info +=
  | RepeatStarSHRegex target ->
    target.info
  sem set_SHRegex_info val +=
  | RepeatStarSHRegex target ->
    RepeatStarSHRegex
      { target with info = val }
end
lang RepeatQuestionSHRegexAst =
  SelfhostBaseAst
  type RepeatQuestionSHRegexRecord =
    {info: Info, left: SHRegex}
  syn SHRegex +=
  | RepeatQuestionSHRegex RepeatQuestionSHRegexRecord
  sem smapAccumL_SHRegex_SHRegex f acc +=
  | RepeatQuestionSHRegex x ->
    match
      match
        let left = x.left in
        f acc left
      with
        (acc, left)
      in
      (acc, { x with left = left })
    with
      (acc, x)
    in
    (acc, RepeatQuestionSHRegex
        x)
  sem get_SHRegex_info +=
  | RepeatQuestionSHRegex target ->
    target.info
  sem set_SHRegex_info val +=
  | RepeatQuestionSHRegex target ->
    RepeatQuestionSHRegex
      { target with info = val }
end
lang NamedSHRegexAst =
  SelfhostBaseAst
  type NamedSHRegexRecord =
    {info: Info, name: {i: Info, v: String}, right: SHRegex}
  syn SHRegex +=
  | NamedSHRegex NamedSHRegexRecord
  sem smapAccumL_SHRegex_SHRegex f acc +=
  | NamedSHRegex x ->
    match
      match
        let right = x.right in
        f acc right
      with
        (acc, right)
      in
      (acc, { x with right = right })
    with
      (acc, x)
    in
    (acc, NamedSHRegex
        x)
  sem get_SHRegex_info +=
  | NamedSHRegex target ->
    target.info
  sem set_SHRegex_info val +=
  | NamedSHRegex target ->
    NamedSHRegex
      { target with info = val }
end
lang AlternativeSHRegexAst =
  SelfhostBaseAst
  type AlternativeSHRegexRecord =
    {info: Info, left: SHRegex, right: SHRegex}
  syn SHRegex +=
  | AlternativeSHRegex AlternativeSHRegexRecord
  sem smapAccumL_SHRegex_SHRegex f acc +=
  | AlternativeSHRegex x ->
    match
      match
        let left = x.left in
        f acc left
      with
        (acc, left)
      in
      match
          let right = x.right in
          f acc right
        with
          (acc, right)
        in
        (acc, { x with left = left, right = right })
    with
      (acc, x)
    in
    (acc, AlternativeSHRegex
        x)
  sem get_SHRegex_info +=
  | AlternativeSHRegex target ->
    target.info
  sem set_SHRegex_info val +=
  | AlternativeSHRegex target ->
    AlternativeSHRegex
      { target with info = val }
end
lang ConcatSHRegexAst =
  SelfhostBaseAst
  type ConcatSHRegexRecord =
    {info: Info, left: SHRegex, right: SHRegex}
  syn SHRegex +=
  | ConcatSHRegex ConcatSHRegexRecord
  sem smapAccumL_SHRegex_SHRegex f acc +=
  | ConcatSHRegex x ->
    match
      match
        let left = x.left in
        f acc left
      with
        (acc, left)
      in
      match
          let right = x.right in
          f acc right
        with
          (acc, right)
        in
        (acc, { x with left = left, right = right })
    with
      (acc, x)
    in
    (acc, ConcatSHRegex
        x)
  sem get_SHRegex_info +=
  | ConcatSHRegex target ->
    target.info
  sem set_SHRegex_info val +=
  | ConcatSHRegex target ->
    ConcatSHRegex
      { target with info = val }
end
lang AppSHExprAst =
  SelfhostBaseAst
  type AppSHExprRecord =
    {info: Info, left: SHExpr, right: SHExpr}
  syn SHExpr +=
  | AppSHExpr AppSHExprRecord
  sem smapAccumL_SHExpr_SHExpr f acc +=
  | AppSHExpr x ->
    match
      match
        let left = x.left in
        f acc left
      with
        (acc, left)
      in
      match
          let right = x.right in
          f acc right
        with
          (acc, right)
        in
        (acc, { x with left = left, right = right })
    with
      (acc, x)
    in
    (acc, AppSHExpr
        x)
  sem get_SHExpr_info +=
  | AppSHExpr target ->
    target.info
  sem set_SHExpr_info val +=
  | AppSHExpr target ->
    AppSHExpr
      { target with info = val }
end
lang ConSHExprAst =
  SelfhostBaseAst
  type ConSHExprRecord =
    {info: Info, name: {i: Info, v: Name}}
  syn SHExpr +=
  | ConSHExpr ConSHExprRecord
  sem get_SHExpr_info +=
  | ConSHExpr target ->
    target.info
  sem set_SHExpr_info val +=
  | ConSHExpr target ->
    ConSHExpr
      { target with info = val }
end
lang StringSHExprAst =
  SelfhostBaseAst
  type StringSHExprRecord =
    {val: {i: Info, v: String}, info: Info}
  syn SHExpr +=
  | StringSHExpr StringSHExprRecord
  sem get_SHExpr_info +=
  | StringSHExpr target ->
    target.info
  sem set_SHExpr_info val +=
  | StringSHExpr target ->
    StringSHExpr
      { target with info = val }
end
lang VariableSHExprAst =
  SelfhostBaseAst
  type VariableSHExprRecord =
    {info: Info, name: {i: Info, v: Name}}
  syn SHExpr +=
  | VariableSHExpr VariableSHExprRecord
  sem get_SHExpr_info +=
  | VariableSHExpr target ->
    target.info
  sem set_SHExpr_info val +=
  | VariableSHExpr target ->
    VariableSHExpr
      { target with info = val }
end
lang RecordSHExprAst =
  SelfhostBaseAst
  type RecordSHExprRecord =
    {info: Info, fields: [{val: SHExpr, name: {i: Info, v: String}}]}
  syn SHExpr +=
  | RecordSHExpr RecordSHExprRecord
  sem smapAccumL_SHExpr_SHExpr f acc +=
  | RecordSHExpr x ->
    match
      match
        let fields = x.fields in
        mapAccumL
          (lam acc1.
             lam x1: {val: SHExpr, name: {i: Info, v: String}}.
               match
                 let val1 = x1.val in
                 f acc1 val1
               with
                 (acc1, val1)
               in
               (acc1, { x1 with val = val1 }))
          acc
          fields
      with
        (acc, fields)
      in
      (acc, { x with fields = fields })
    with
      (acc, x)
    in
    (acc, RecordSHExpr
        x)
  sem get_SHExpr_info +=
  | RecordSHExpr target ->
    target.info
  sem set_SHExpr_info val +=
  | RecordSHExpr target ->
    RecordSHExpr
      { target with info = val }
end
lang BadSHFileAst =
  SelfhostBaseAst
  type BadSHFileRecord =
    {info: Info}
  syn SHFile +=
  | BadSHFile BadSHFileRecord
  sem get_SHFile_info +=
  | BadSHFile target ->
    target.info
  sem set_SHFile_info val +=
  | BadSHFile target ->
    BadSHFile
      { target with info = val }
end
lang BadSHDeclAst =
  SelfhostBaseAst
  type BadSHDeclRecord =
    {info: Info}
  syn SHDecl +=
  | BadSHDecl BadSHDeclRecord
  sem get_SHDecl_info +=
  | BadSHDecl target ->
    target.info
  sem set_SHDecl_info val +=
  | BadSHDecl target ->
    BadSHDecl
      { target with info = val }
end
lang BadSHRegexAst =
  SelfhostBaseAst
  type BadSHRegexRecord =
    {info: Info}
  syn SHRegex +=
  | BadSHRegex BadSHRegexRecord
  sem get_SHRegex_info +=
  | BadSHRegex target ->
    target.info
  sem set_SHRegex_info val +=
  | BadSHRegex target ->
    BadSHRegex
      { target with info = val }
end
lang BadSHExprAst =
  SelfhostBaseAst
  type BadSHExprRecord =
    {info: Info}
  syn SHExpr +=
  | BadSHExpr BadSHExprRecord
  sem get_SHExpr_info +=
  | BadSHExpr target ->
    target.info
  sem set_SHExpr_info val +=
  | BadSHExpr target ->
    BadSHExpr
      { target with info = val }
end
lang SelfhostAst =
  LangSHFileAst
  + StartSHDeclAst
  + IncludeSHDeclAst
  + TypeSHDeclAst
  + TokenSHDeclAst
  + PrecedenceTableSHDeclAst
  + ProductionSHDeclAst
  + RecordSHRegexAst
  + EmptySHRegexAst
  + LiteralSHRegexAst
  + TokenSHRegexAst
  + RepeatPlusSHRegexAst
  + RepeatStarSHRegexAst
  + RepeatQuestionSHRegexAst
  + NamedSHRegexAst
  + AlternativeSHRegexAst
  + ConcatSHRegexAst
  + AppSHExprAst
  + ConSHExprAst
  + StringSHExprAst
  + VariableSHExprAst
  + RecordSHExprAst
  + BadSHFileAst
  + BadSHDeclAst
  + BadSHRegexAst
  + BadSHExprAst
end
lang SHFileOpBase =
  SelfhostAst
  syn SHFileOp lstyle rstyle =
  sem topAllowed_SHFileOp : all lstyle. all rstyle. SHFileOp lstyle rstyle -> Bool
sem topAllowed_SHFileOp =
  | _ ->
    true
  sem leftAllowed_SHFileOp : all lstyle. all style. all rstyle. {child: SHFileOp lstyle rstyle, parent: SHFileOp LOpen style} -> Bool
sem leftAllowed_SHFileOp =
  | _ ->
    true
  sem rightAllowed_SHFileOp : all style. all lstyle. all rstyle. {child: SHFileOp lstyle rstyle, parent: SHFileOp style ROpen} -> Bool
sem rightAllowed_SHFileOp =
  | _ ->
    true
  sem groupingsAllowed_SHFileOp : all lstyle. all rstyle. (SHFileOp lstyle ROpen, SHFileOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_SHFileOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_SHFileOp : all lstyle. all rstyle. SHFileOp lstyle rstyle -> AllowedDirection
sem parenAllowed_SHFileOp =
  | _ ->
    GEither
      {}
  sem getInfo_SHFileOp : all lstyle. all rstyle. SHFileOp lstyle rstyle -> Info
sem getInfo_SHFileOp =
  sem getTerms_SHFileOp : all lstyle. all rstyle. SHFileOp lstyle rstyle -> [Info]
sem getTerms_SHFileOp =
  sem unsplit_SHFileOp : PermanentNode SHFileOp -> (Info, SHFile)
sem unsplit_SHFileOp =
end
lang SHDeclOpBase =
  SelfhostAst
  syn SHDeclOp lstyle rstyle =
  sem topAllowed_SHDeclOp : all lstyle. all rstyle. SHDeclOp lstyle rstyle -> Bool
sem topAllowed_SHDeclOp =
  | _ ->
    true
  sem leftAllowed_SHDeclOp : all lstyle. all style. all rstyle. {child: SHDeclOp lstyle rstyle, parent: SHDeclOp LOpen style} -> Bool
sem leftAllowed_SHDeclOp =
  | _ ->
    true
  sem rightAllowed_SHDeclOp : all style. all lstyle. all rstyle. {child: SHDeclOp lstyle rstyle, parent: SHDeclOp style ROpen} -> Bool
sem rightAllowed_SHDeclOp =
  | _ ->
    true
  sem groupingsAllowed_SHDeclOp : all lstyle. all rstyle. (SHDeclOp lstyle ROpen, SHDeclOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_SHDeclOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_SHDeclOp : all lstyle. all rstyle. SHDeclOp lstyle rstyle -> AllowedDirection
sem parenAllowed_SHDeclOp =
  | _ ->
    GEither
      {}
  sem getInfo_SHDeclOp : all lstyle. all rstyle. SHDeclOp lstyle rstyle -> Info
sem getInfo_SHDeclOp =
  sem getTerms_SHDeclOp : all lstyle. all rstyle. SHDeclOp lstyle rstyle -> [Info]
sem getTerms_SHDeclOp =
  sem unsplit_SHDeclOp : PermanentNode SHDeclOp -> (Info, SHDecl)
sem unsplit_SHDeclOp =
end
lang SHRegexOpBase =
  SelfhostAst
  syn SHRegexOp lstyle rstyle =
  sem topAllowed_SHRegexOp : all lstyle. all rstyle. SHRegexOp lstyle rstyle -> Bool
sem topAllowed_SHRegexOp =
  | _ ->
    true
  sem leftAllowed_SHRegexOp : all lstyle. all style. all rstyle. {child: SHRegexOp lstyle rstyle, parent: SHRegexOp LOpen style} -> Bool
sem leftAllowed_SHRegexOp =
  | _ ->
    true
  sem rightAllowed_SHRegexOp : all style. all lstyle. all rstyle. {child: SHRegexOp lstyle rstyle, parent: SHRegexOp style ROpen} -> Bool
sem rightAllowed_SHRegexOp =
  | _ ->
    true
  sem groupingsAllowed_SHRegexOp : all lstyle. all rstyle. (SHRegexOp lstyle ROpen, SHRegexOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_SHRegexOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_SHRegexOp : all lstyle. all rstyle. SHRegexOp lstyle rstyle -> AllowedDirection
sem parenAllowed_SHRegexOp =
  | _ ->
    GEither
      {}
  sem getInfo_SHRegexOp : all lstyle. all rstyle. SHRegexOp lstyle rstyle -> Info
sem getInfo_SHRegexOp =
  sem getTerms_SHRegexOp : all lstyle. all rstyle. SHRegexOp lstyle rstyle -> [Info]
sem getTerms_SHRegexOp =
  sem unsplit_SHRegexOp : PermanentNode SHRegexOp -> (Info, SHRegex)
sem unsplit_SHRegexOp =
end
lang SHExprOpBase =
  SelfhostAst
  syn SHExprOp lstyle rstyle =
  sem topAllowed_SHExprOp : all lstyle. all rstyle. SHExprOp lstyle rstyle -> Bool
sem topAllowed_SHExprOp =
  | _ ->
    true
  sem leftAllowed_SHExprOp : all lstyle. all style. all rstyle. {child: SHExprOp lstyle rstyle, parent: SHExprOp LOpen style} -> Bool
sem leftAllowed_SHExprOp =
  | _ ->
    true
  sem rightAllowed_SHExprOp : all style. all lstyle. all rstyle. {child: SHExprOp lstyle rstyle, parent: SHExprOp style ROpen} -> Bool
sem rightAllowed_SHExprOp =
  | _ ->
    true
  sem groupingsAllowed_SHExprOp : all lstyle. all rstyle. (SHExprOp lstyle ROpen, SHExprOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_SHExprOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_SHExprOp : all lstyle. all rstyle. SHExprOp lstyle rstyle -> AllowedDirection
sem parenAllowed_SHExprOp =
  | _ ->
    GEither
      {}
  sem getInfo_SHExprOp : all lstyle. all rstyle. SHExprOp lstyle rstyle -> Info
sem getInfo_SHExprOp =
  sem getTerms_SHExprOp : all lstyle. all rstyle. SHExprOp lstyle rstyle -> [Info]
sem getTerms_SHExprOp =
  sem unsplit_SHExprOp : PermanentNode SHExprOp -> (Info, SHExpr)
sem unsplit_SHExprOp =
end
lang LangSHFileOp =
  SHFileOpBase
  + LangSHFileAst
  syn SHFileOp lstyle rstyle +=
  | LangSHFileOp {name: [{i: Info, v: String}], decls: [SHDecl], __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHFileOp +=
  | LangSHFileOp x ->
    x.__br_info
  sem getTerms_SHFileOp +=
  | LangSHFileOp x ->
    x.__br_terms
  sem unsplit_SHFileOp +=
  | AtomP {self = LangSHFileOp x} ->
    (x.__br_info, LangSHFile
      { info = x.__br_info,
        decls = x.decls,
        name =
          match
            x.name
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang StartSHDeclOp =
  SHDeclOpBase
  + StartSHDeclAst
  syn SHDeclOp lstyle rstyle +=
  | StartSHDeclOp {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHDeclOp +=
  | StartSHDeclOp x ->
    x.__br_info
  sem getTerms_SHDeclOp +=
  | StartSHDeclOp x ->
    x.__br_terms
  sem unsplit_SHDeclOp +=
  | AtomP {self = StartSHDeclOp x} ->
    (x.__br_info, StartSHDecl
      { info = x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang IncludeSHDeclOp =
  SHDeclOpBase
  + IncludeSHDeclAst
  syn SHDeclOp lstyle rstyle +=
  | IncludeSHDeclOp {path: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHDeclOp +=
  | IncludeSHDeclOp x ->
    x.__br_info
  sem getTerms_SHDeclOp +=
  | IncludeSHDeclOp x ->
    x.__br_terms
  sem unsplit_SHDeclOp +=
  | AtomP {self = IncludeSHDeclOp x} ->
    (x.__br_info, IncludeSHDecl
      { info = x.__br_info,
        path =
          match
            x.path
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang TypeSHDeclOp =
  SHDeclOpBase
  + TypeSHDeclAst
  syn SHDeclOp lstyle rstyle +=
  | TypeSHDeclOp {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info], properties: [{val: SHExpr, name: {i: Info, v: String}}]}
  sem getInfo_SHDeclOp +=
  | TypeSHDeclOp x ->
    x.__br_info
  sem getTerms_SHDeclOp +=
  | TypeSHDeclOp x ->
    x.__br_terms
  sem unsplit_SHDeclOp +=
  | AtomP {self = TypeSHDeclOp x} ->
    (x.__br_info, TypeSHDecl
      { info = x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _
          in
          x1,
        properties = x.properties })
end
lang TokenSHDeclOp =
  SHDeclOpBase
  + TokenSHDeclAst
  syn SHDeclOp lstyle rstyle +=
  | TokenSHDeclOp {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info], properties: [{val: SHExpr, name: {i: Info, v: String}}]}
  sem getInfo_SHDeclOp +=
  | TokenSHDeclOp x ->
    x.__br_info
  sem getTerms_SHDeclOp +=
  | TokenSHDeclOp x ->
    x.__br_terms
  sem unsplit_SHDeclOp +=
  | AtomP {self = TokenSHDeclOp x} ->
    (x.__br_info, TokenSHDecl
      { info = x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _
          then
            Some
              x1
          else
            None
              {},
        properties = x.properties })
end
lang PrecedenceTableSHDeclOp =
  SHDeclOpBase
  + PrecedenceTableSHDeclAst
  syn SHDeclOp lstyle rstyle +=
  | PrecedenceTableSHDeclOp {levels: [{noeq: Option Info, operators: [{i: Info, v: Name}]}], __br_info: Info, __br_terms: [Info], exceptions: [{lefts: [{i: Info, v: Name}], rights: [{i: Info, v: Name}]}]}
  sem getInfo_SHDeclOp +=
  | PrecedenceTableSHDeclOp x ->
    x.__br_info
  sem getTerms_SHDeclOp +=
  | PrecedenceTableSHDeclOp x ->
    x.__br_terms
  sem unsplit_SHDeclOp +=
  | AtomP {self = PrecedenceTableSHDeclOp x} ->
    (x.__br_info, PrecedenceTableSHDecl
      { info = x.__br_info,
        levels = x.levels,
        exceptions = x.exceptions })
end
lang ProductionSHDeclOp =
  SHDeclOpBase
  + ProductionSHDeclAst
  syn SHDeclOp lstyle rstyle +=
  | ProductionSHDeclOp {nt: [{i: Info, v: Name}], kinf: [Info], name: [{i: Info, v: Name}], assoc: [{i: Info, v: String}], kpref: [Info], kprod: [Info], regex: [SHRegex], kpostf: [Info], __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHDeclOp +=
  | ProductionSHDeclOp x ->
    x.__br_info
  sem getTerms_SHDeclOp +=
  | ProductionSHDeclOp x ->
    x.__br_terms
  sem unsplit_SHDeclOp +=
  | AtomP {self = ProductionSHDeclOp x} ->
    (x.__br_info, ProductionSHDecl
      { info = x.__br_info,
        nt =
          match
            x.nt
          with
            [ x1 ] ++ _
          in
          x1,
        name =
          match
            x.name
          with
            [ x2 ] ++ _
          in
          x2,
        kinf =
          match
            x.kinf
          with
            [ x3 ] ++ _
          then
            Some
              x3
          else
            None
              {},
        kpref =
          match
            x.kpref
          with
            [ x4 ] ++ _
          then
            Some
              x4
          else
            None
              {},
        kprod =
          match
            x.kprod
          with
            [ x5 ] ++ _
          then
            Some
              x5
          else
            None
              {},
        kpostf =
          match
            x.kpostf
          with
            [ x6 ] ++ _
          then
            Some
              x6
          else
            None
              {},
        assoc =
          match
            x.assoc
          with
            [ x7 ] ++ _
          then
            Some
              x7
          else
            None
              {},
        regex =
          match
            x.regex
          with
            [ x8 ] ++ _
          in
          x8 })
end
lang RecordSHRegexOp =
  SHRegexOpBase
  + RecordSHRegexAst
  syn SHRegexOp lstyle rstyle +=
  | RecordSHRegexOp {regex: [SHRegex], __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHRegexOp +=
  | RecordSHRegexOp x ->
    x.__br_info
  sem getTerms_SHRegexOp +=
  | RecordSHRegexOp x ->
    x.__br_terms
  sem unsplit_SHRegexOp +=
  | AtomP {self = RecordSHRegexOp x} ->
    (x.__br_info, RecordSHRegex
      { info = x.__br_info,
        regex =
          match
            x.regex
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang EmptySHRegexOp =
  SHRegexOpBase
  + EmptySHRegexAst
  syn SHRegexOp lstyle rstyle +=
  | EmptySHRegexOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_SHRegexOp +=
  | EmptySHRegexOp x ->
    x.__br_info
  sem getTerms_SHRegexOp +=
  | EmptySHRegexOp x ->
    x.__br_terms
  sem unsplit_SHRegexOp +=
  | AtomP {self = EmptySHRegexOp x} ->
    (x.__br_info, EmptySHRegex
      { info = x.__br_info })
end
lang LiteralSHRegexOp =
  SHRegexOpBase
  + LiteralSHRegexAst
  syn SHRegexOp lstyle rstyle +=
  | LiteralSHRegexOp {val: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHRegexOp +=
  | LiteralSHRegexOp x ->
    x.__br_info
  sem getTerms_SHRegexOp +=
  | LiteralSHRegexOp x ->
    x.__br_terms
  sem unsplit_SHRegexOp +=
  | AtomP {self = LiteralSHRegexOp x} ->
    (x.__br_info, LiteralSHRegex
      { info = x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang TokenSHRegexOp =
  SHRegexOpBase
  + TokenSHRegexAst
  syn SHRegexOp lstyle rstyle +=
  | TokenSHRegexOp {arg: [SHExpr], name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHRegexOp +=
  | TokenSHRegexOp x ->
    x.__br_info
  sem getTerms_SHRegexOp +=
  | TokenSHRegexOp x ->
    x.__br_terms
  sem unsplit_SHRegexOp +=
  | AtomP {self = TokenSHRegexOp x} ->
    (x.__br_info, TokenSHRegex
      { info = x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _
          in
          x1,
        arg =
          match
            x.arg
          with
            [ x2 ] ++ _
          then
            Some
              x2
          else
            None
              {} })
end
lang RepeatPlusSHRegexOp =
  SHRegexOpBase
  + RepeatPlusSHRegexAst
  syn SHRegexOp lstyle rstyle +=
  | RepeatPlusSHRegexOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_SHRegexOp +=
  | RepeatPlusSHRegexOp x ->
    x.__br_info
  sem getTerms_SHRegexOp +=
  | RepeatPlusSHRegexOp x ->
    x.__br_terms
  sem unsplit_SHRegexOp +=
  | PostfixP {self = RepeatPlusSHRegexOp x, leftChildAlts = [ l ] ++ _} ->
    match
      unsplit_SHRegexOp l
    with
      (linfo, l)
    in
    let info = mergeInfo linfo x.__br_info in
      (info, RepeatPlusSHRegex
        { info = info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _
            in
            x1 })
end
lang RepeatStarSHRegexOp =
  SHRegexOpBase
  + RepeatStarSHRegexAst
  syn SHRegexOp lstyle rstyle +=
  | RepeatStarSHRegexOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_SHRegexOp +=
  | RepeatStarSHRegexOp x ->
    x.__br_info
  sem getTerms_SHRegexOp +=
  | RepeatStarSHRegexOp x ->
    x.__br_terms
  sem unsplit_SHRegexOp +=
  | PostfixP {self = RepeatStarSHRegexOp x, leftChildAlts = [ l ] ++ _} ->
    match
      unsplit_SHRegexOp l
    with
      (linfo, l)
    in
    let info = mergeInfo linfo x.__br_info in
      (info, RepeatStarSHRegex
        { info = info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _
            in
            x1 })
end
lang RepeatQuestionSHRegexOp =
  SHRegexOpBase
  + RepeatQuestionSHRegexAst
  syn SHRegexOp lstyle rstyle +=
  | RepeatQuestionSHRegexOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_SHRegexOp +=
  | RepeatQuestionSHRegexOp x ->
    x.__br_info
  sem getTerms_SHRegexOp +=
  | RepeatQuestionSHRegexOp x ->
    x.__br_terms
  sem unsplit_SHRegexOp +=
  | PostfixP {self = RepeatQuestionSHRegexOp x, leftChildAlts = [ l ] ++ _} ->
    match
      unsplit_SHRegexOp l
    with
      (linfo, l)
    in
    let info = mergeInfo linfo x.__br_info in
      (info, RepeatQuestionSHRegex
        { info = info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _
            in
            x1 })
end
lang NamedSHRegexOp =
  SHRegexOpBase
  + NamedSHRegexAst
  syn SHRegexOp lstyle rstyle +=
  | NamedSHRegexOp {name: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHRegexOp +=
  | NamedSHRegexOp x ->
    x.__br_info
  sem getTerms_SHRegexOp +=
  | NamedSHRegexOp x ->
    x.__br_terms
  sem unsplit_SHRegexOp +=
  | PrefixP {self = NamedSHRegexOp x, rightChildAlts = [ r ] ++ _} ->
    match
      unsplit_SHRegexOp r
    with
      (rinfo, r)
    in
    let info = mergeInfo x.__br_info rinfo in
      (info, NamedSHRegex
        { info = info,
          name =
            match
              x.name
            with
              [ x1 ] ++ _
            in
            x1,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _
            in
            x2 })
end
lang AlternativeSHRegexOp =
  SHRegexOpBase
  + AlternativeSHRegexAst
  sem groupingsAllowed_SHRegexOp +=
  | (AlternativeSHRegexOp _, AlternativeSHRegexOp _) ->
    GLeft
      {}
  syn SHRegexOp lstyle rstyle +=
  | AlternativeSHRegexOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_SHRegexOp +=
  | AlternativeSHRegexOp x ->
    x.__br_info
  sem getTerms_SHRegexOp +=
  | AlternativeSHRegexOp x ->
    x.__br_terms
  sem unsplit_SHRegexOp +=
  | InfixP {self = AlternativeSHRegexOp x, leftChildAlts = [ l ] ++ _, rightChildAlts = [ r ] ++ _} ->
    match
      (unsplit_SHRegexOp l, unsplit_SHRegexOp r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info = foldl mergeInfo linfo [ x.__br_info,
            rinfo ]
      in
      (info, AlternativeSHRegex
        { info = info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _
            in
            x1,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _
            in
            x2 })
end
lang ConcatSHRegexOp =
  SHRegexOpBase
  + ConcatSHRegexAst
  sem groupingsAllowed_SHRegexOp +=
  | (ConcatSHRegexOp _, ConcatSHRegexOp _) ->
    GLeft
      {}
  syn SHRegexOp lstyle rstyle +=
  | ConcatSHRegexOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_SHRegexOp +=
  | ConcatSHRegexOp x ->
    x.__br_info
  sem getTerms_SHRegexOp +=
  | ConcatSHRegexOp x ->
    x.__br_terms
  sem unsplit_SHRegexOp +=
  | InfixP {self = ConcatSHRegexOp x, leftChildAlts = [ l ] ++ _, rightChildAlts = [ r ] ++ _} ->
    match
      (unsplit_SHRegexOp l, unsplit_SHRegexOp r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info = foldl mergeInfo linfo [ x.__br_info,
            rinfo ]
      in
      (info, ConcatSHRegex
        { info = info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _
            in
            x1,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _
            in
            x2 })
end
lang AppSHExprOp =
  SHExprOpBase
  + AppSHExprAst
  sem groupingsAllowed_SHExprOp +=
  | (AppSHExprOp _, AppSHExprOp _) ->
    GLeft
      {}
  syn SHExprOp lstyle rstyle +=
  | AppSHExprOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_SHExprOp +=
  | AppSHExprOp x ->
    x.__br_info
  sem getTerms_SHExprOp +=
  | AppSHExprOp x ->
    x.__br_terms
  sem unsplit_SHExprOp +=
  | InfixP {self = AppSHExprOp x, leftChildAlts = [ l ] ++ _, rightChildAlts = [ r ] ++ _} ->
    match
      (unsplit_SHExprOp l, unsplit_SHExprOp r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info = foldl mergeInfo linfo [ x.__br_info,
            rinfo ]
      in
      (info, AppSHExpr
        { info = info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _
            in
            x1,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _
            in
            x2 })
end
lang ConSHExprOp =
  SHExprOpBase
  + ConSHExprAst
  syn SHExprOp lstyle rstyle +=
  | ConSHExprOp {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHExprOp +=
  | ConSHExprOp x ->
    x.__br_info
  sem getTerms_SHExprOp +=
  | ConSHExprOp x ->
    x.__br_terms
  sem unsplit_SHExprOp +=
  | AtomP {self = ConSHExprOp x} ->
    (x.__br_info, ConSHExpr
      { info = x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang StringSHExprOp =
  SHExprOpBase
  + StringSHExprAst
  syn SHExprOp lstyle rstyle +=
  | StringSHExprOp {val: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHExprOp +=
  | StringSHExprOp x ->
    x.__br_info
  sem getTerms_SHExprOp +=
  | StringSHExprOp x ->
    x.__br_terms
  sem unsplit_SHExprOp +=
  | AtomP {self = StringSHExprOp x} ->
    (x.__br_info, StringSHExpr
      { info = x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang VariableSHExprOp =
  SHExprOpBase
  + VariableSHExprAst
  syn SHExprOp lstyle rstyle +=
  | VariableSHExprOp {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHExprOp +=
  | VariableSHExprOp x ->
    x.__br_info
  sem getTerms_SHExprOp +=
  | VariableSHExprOp x ->
    x.__br_terms
  sem unsplit_SHExprOp +=
  | AtomP {self = VariableSHExprOp x} ->
    (x.__br_info, VariableSHExpr
      { info = x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang RecordSHExprOp =
  SHExprOpBase
  + RecordSHExprAst
  syn SHExprOp lstyle rstyle +=
  | RecordSHExprOp {fields: [{val: SHExpr, name: {i: Info, v: String}}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHExprOp +=
  | RecordSHExprOp x ->
    x.__br_info
  sem getTerms_SHExprOp +=
  | RecordSHExprOp x ->
    x.__br_terms
  sem unsplit_SHExprOp +=
  | AtomP {self = RecordSHExprOp x} ->
    (x.__br_info, RecordSHExpr
      { info = x.__br_info, fields = x.fields })
end
lang SHRegexGrouping =
  SHRegexOpBase
  syn SHRegexOp lstyle rstyle +=
  | SHRegexGrouping {inner: SHRegex, __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHRegexOp +=
  | SHRegexGrouping x ->
    x.__br_info
  sem getTerms_SHRegexOp +=
  | SHRegexGrouping x ->
    x.__br_terms
  sem unsplit_SHRegexOp +=
  | AtomP {self = SHRegexGrouping x} ->
    (x.__br_info, x.inner)
end
lang SHExprGrouping =
  SHExprOpBase
  syn SHExprOp lstyle rstyle +=
  | SHExprGrouping {inner: SHExpr, __br_info: Info, __br_terms: [Info]}
  sem getInfo_SHExprOp +=
  | SHExprGrouping x ->
    x.__br_info
  sem getTerms_SHExprOp +=
  | SHExprGrouping x ->
    x.__br_terms
  sem unsplit_SHExprOp +=
  | AtomP {self = SHExprGrouping x} ->
    (x.__br_info, x.inner)
end
lang ParseSelfhost =
  LangSHFileOp
  + StartSHDeclOp
  + IncludeSHDeclOp
  + TypeSHDeclOp
  + TokenSHDeclOp
  + PrecedenceTableSHDeclOp
  + ProductionSHDeclOp
  + RecordSHRegexOp
  + EmptySHRegexOp
  + LiteralSHRegexOp
  + TokenSHRegexOp
  + RepeatPlusSHRegexOp
  + RepeatStarSHRegexOp
  + RepeatQuestionSHRegexOp
  + NamedSHRegexOp
  + AlternativeSHRegexOp
  + ConcatSHRegexOp
  + AppSHExprOp
  + ConSHExprOp
  + StringSHExprOp
  + VariableSHExprOp
  + RecordSHExprOp
  + SHRegexGrouping
  + SHExprGrouping
  + BadSHFileAst
  + BadSHDeclAst
  + BadSHRegexAst
  + BadSHExprAst
  + LL1Parser
  + SemiTokenParser
  + CommaTokenParser
  + WhitespaceParser
  + LIdentTokenParser
  + LineCommentParser
  + StringTokenParser
  + UIdentTokenParser
  + BracketTokenParser
  + OperatorTokenParser
  + MultilineCommentParser
  sem groupingsAllowed_SHFileOp +=
  sem groupingsAllowed_SHDeclOp +=
  sem groupingsAllowed_SHRegexOp +=
  | (NamedSHRegexOp _, RepeatPlusSHRegexOp _) ->
    GLeft
      {}
  | (AlternativeSHRegexOp _, RepeatPlusSHRegexOp _) ->
    GRight
      {}
  | (ConcatSHRegexOp _, RepeatPlusSHRegexOp _) ->
    GRight
      {}
  | (NamedSHRegexOp _, RepeatStarSHRegexOp _) ->
    GLeft
      {}
  | (AlternativeSHRegexOp _, RepeatStarSHRegexOp _) ->
    GRight
      {}
  | (ConcatSHRegexOp _, RepeatStarSHRegexOp _) ->
    GRight
      {}
  | (NamedSHRegexOp _, RepeatQuestionSHRegexOp _) ->
    GLeft
      {}
  | (AlternativeSHRegexOp _, RepeatQuestionSHRegexOp _) ->
    GRight
      {}
  | (ConcatSHRegexOp _, RepeatQuestionSHRegexOp _) ->
    GRight
      {}
  | (NamedSHRegexOp _, AlternativeSHRegexOp _) ->
    GLeft
      {}
  | (NamedSHRegexOp _, ConcatSHRegexOp _) ->
    GLeft
      {}
  | (AlternativeSHRegexOp _, ConcatSHRegexOp _) ->
    GRight
      {}
  | (ConcatSHRegexOp _, AlternativeSHRegexOp _) ->
    GLeft
      {}
  sem groupingsAllowed_SHExprOp +=
end
let _table =
  use ParseSelfhost
  in
  let target =
    genParsingTable
      (let #var"SHFile" = nameSym "SHFile" in
       let #var"SHDecl" = nameSym "SHDecl" in
       let #var"SHRegex" = nameSym "SHRegex" in
       let #var"SHExpr" = nameSym "SHExpr" in
       let #var"SHFilePostfix" = nameSym "SHFilePostfix" in
       let #var"SHFilePrefix" = nameSym "SHFilePrefix" in
       let #var"SHFileInfix" = nameSym "SHFileInfix" in
       let #var"SHFileAtom" = nameSym "SHFileAtom" in
       let #var"SHDeclPostfix" = nameSym "SHDeclPostfix" in
       let #var"SHDeclPrefix" = nameSym "SHDeclPrefix" in
       let #var"SHDeclInfix" = nameSym "SHDeclInfix" in
       let #var"SHDeclAtom" = nameSym "SHDeclAtom" in
       let #var"SHRegexPostfix" = nameSym "SHRegexPostfix" in
       let #var"SHRegexPrefix" = nameSym "SHRegexPrefix" in
       let #var"SHRegexInfix" = nameSym "SHRegexInfix" in
       let #var"SHRegexAtom" = nameSym "SHRegexAtom" in
       let #var"SHExprPostfix" = nameSym "SHExprPostfix" in
       let #var"SHExprPrefix" = nameSym "SHExprPrefix" in
       let #var"SHExprInfix" = nameSym "SHExprInfix" in
       let #var"SHExprAtom" = nameSym "SHExprAtom" in
       let kleene = nameSym "kleene" in
       let kleene1 = nameSym "kleene" in
       let alt = nameSym "alt" in
       let alt1 = nameSym "alt" in
       let kleene2 = nameSym "kleene" in
       let alt2 = nameSym "alt" in
       let alt3 = nameSym "alt" in
       let kleene3 = nameSym "kleene" in
       let kleene4 = nameSym "kleene" in
       let kleene5 = nameSym "kleene" in
       let kleene6 = nameSym "kleene" in
       let kleene7 = nameSym "kleene" in
       let alt4 = nameSym "alt" in
       let alt5 = nameSym "alt" in
       let alt6 = nameSym "alt" in
       let alt7 = nameSym "alt" in
       let kleene8 = nameSym "kleene" in
       let alt8 = nameSym "alt" in
       let #var"SHFile_lclosed" = nameSym "SHFile_lclosed" in
       let #var"SHFile_lopen" = nameSym "SHFile_lopen" in
       let #var"SHDecl_lclosed" = nameSym "SHDecl_lclosed" in
       let #var"SHDecl_lopen" = nameSym "SHDecl_lopen" in
       let #var"SHRegex_lclosed" = nameSym "SHRegex_lclosed" in
       let #var"SHRegex_lopen" = nameSym "SHRegex_lopen" in
       let #var"SHExpr_lclosed" = nameSym "SHExpr_lclosed" in
       let #var"SHExpr_lopen" = nameSym "SHExpr_lopen" in
       { start = #var"SHFile",
         productions =
           let config =
             { parenAllowed = #frozen"parenAllowed_SHFileOp",
               topAllowed = #frozen"topAllowed_SHFileOp",
               leftAllowed = #frozen"leftAllowed_SHFileOp",
               rightAllowed = #frozen"rightAllowed_SHFileOp",
               groupingsAllowed = #frozen"groupingsAllowed_SHFileOp" }
           in
           let reportConfig =
             { parenAllowed = #frozen"parenAllowed_SHFileOp",
               topAllowed = #frozen"topAllowed_SHFileOp",
               terminalInfos = #frozen"getTerms_SHFileOp",
               getInfo = #frozen"getInfo_SHFileOp",
               lpar = "(",
               rpar = ")" }
           in
           let addSHFileOpAtom =
             lam #var"".
               lam x33.
                 lam st.
                   optionMap (breakableAddAtom config x33) st
           in
           let addSHFileOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x33.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st = breakableAddInfix config x33 st in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc (deref p.errors) (getInfo_SHFileOp x33, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addSHFileOpPrefix =
             lam #var"".
               lam x33.
                 lam st.
                   optionMap (breakableAddPrefix config x33) st
           in
           let addSHFileOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x33.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st = breakableAddPostfix config x33 st in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc (deref p.errors) (getInfo_SHFileOp x33, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeSHFileOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res60 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse config st
                        with
                          Some (tops & ([ top ] ++ _))
                        then
                          let errs = breakableDefaultHighlight reportConfig p.content tops
                          in
                          let res60 = unsplit_SHFileOp top in
                          match
                            null errs
                          with
                            true
                          then
                            Some
                              res60
                          else
                            (modref p.errors (concat (deref p.errors) errs))
                            ; Some
                              (res60.0, BadSHFile
                                { info = res60.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref p.errors)
                                  (NoInfo
                                    {}, "Unfinished SHFile")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadSHFile
                     { info = NoInfo
                           {} })
                   res60
           in
           let config1 =
             { parenAllowed = #frozen"parenAllowed_SHDeclOp",
               topAllowed = #frozen"topAllowed_SHDeclOp",
               leftAllowed = #frozen"leftAllowed_SHDeclOp",
               rightAllowed = #frozen"rightAllowed_SHDeclOp",
               groupingsAllowed = #frozen"groupingsAllowed_SHDeclOp" }
           in
           let reportConfig1 =
             { parenAllowed = #frozen"parenAllowed_SHDeclOp",
               topAllowed = #frozen"topAllowed_SHDeclOp",
               terminalInfos = #frozen"getTerms_SHDeclOp",
               getInfo = #frozen"getInfo_SHDeclOp",
               lpar = "(",
               rpar = ")" }
           in
           let addSHDeclOpAtom =
             lam #var"".
               lam x33.
                 lam st.
                   optionMap (breakableAddAtom config1 x33) st
           in
           let addSHDeclOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x33.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st = breakableAddInfix config1 x33 st in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc (deref p.errors) (getInfo_SHDeclOp x33, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addSHDeclOpPrefix =
             lam #var"".
               lam x33.
                 lam st.
                   optionMap (breakableAddPrefix config1 x33) st
           in
           let addSHDeclOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x33.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st = breakableAddPostfix config1 x33 st in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc (deref p.errors) (getInfo_SHDeclOp x33, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeSHDeclOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res60 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse config1 st
                        with
                          Some (tops & ([ top ] ++ _))
                        then
                          let errs = breakableDefaultHighlight reportConfig1 p.content tops
                          in
                          let res60 = unsplit_SHDeclOp top in
                          match
                            null errs
                          with
                            true
                          then
                            Some
                              res60
                          else
                            (modref p.errors (concat (deref p.errors) errs))
                            ; Some
                              (res60.0, BadSHDecl
                                { info = res60.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref p.errors)
                                  (NoInfo
                                    {}, "Unfinished SHDecl")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadSHDecl
                     { info = NoInfo
                           {} })
                   res60
           in
           let config2 =
             { parenAllowed = #frozen"parenAllowed_SHRegexOp",
               topAllowed = #frozen"topAllowed_SHRegexOp",
               leftAllowed = #frozen"leftAllowed_SHRegexOp",
               rightAllowed = #frozen"rightAllowed_SHRegexOp",
               groupingsAllowed = #frozen"groupingsAllowed_SHRegexOp" }
           in
           let reportConfig2 =
             { parenAllowed = #frozen"parenAllowed_SHRegexOp",
               topAllowed = #frozen"topAllowed_SHRegexOp",
               terminalInfos = #frozen"getTerms_SHRegexOp",
               getInfo = #frozen"getInfo_SHRegexOp",
               lpar = "(",
               rpar = ")" }
           in
           let addSHRegexOpAtom =
             lam #var"".
               lam x33.
                 lam st.
                   optionMap (breakableAddAtom config2 x33) st
           in
           let addSHRegexOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x33.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st = breakableAddInfix config2 x33 st in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc (deref p.errors) (getInfo_SHRegexOp x33, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addSHRegexOpPrefix =
             lam #var"".
               lam x33.
                 lam st.
                   optionMap (breakableAddPrefix config2 x33) st
           in
           let addSHRegexOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x33.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st = breakableAddPostfix config2 x33 st in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc (deref p.errors) (getInfo_SHRegexOp x33, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeSHRegexOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res60 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse config2 st
                        with
                          Some (tops & ([ top ] ++ _))
                        then
                          let errs = breakableDefaultHighlight reportConfig2 p.content tops
                          in
                          let res60 = unsplit_SHRegexOp top in
                          match
                            null errs
                          with
                            true
                          then
                            Some
                              res60
                          else
                            (modref p.errors (concat (deref p.errors) errs))
                            ; Some
                              (res60.0, BadSHRegex
                                { info = res60.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref p.errors)
                                  (NoInfo
                                    {}, "Unfinished SHRegex")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadSHRegex
                     { info = NoInfo
                           {} })
                   res60
           in
           let config3 =
             { parenAllowed = #frozen"parenAllowed_SHExprOp",
               topAllowed = #frozen"topAllowed_SHExprOp",
               leftAllowed = #frozen"leftAllowed_SHExprOp",
               rightAllowed = #frozen"rightAllowed_SHExprOp",
               groupingsAllowed = #frozen"groupingsAllowed_SHExprOp" }
           in
           let reportConfig3 =
             { parenAllowed = #frozen"parenAllowed_SHExprOp",
               topAllowed = #frozen"topAllowed_SHExprOp",
               terminalInfos = #frozen"getTerms_SHExprOp",
               getInfo = #frozen"getInfo_SHExprOp",
               lpar = "(",
               rpar = ")" }
           in
           let addSHExprOpAtom =
             lam #var"".
               lam x33.
                 lam st.
                   optionMap (breakableAddAtom config3 x33) st
           in
           let addSHExprOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x33.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st = breakableAddInfix config3 x33 st in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc (deref p.errors) (getInfo_SHExprOp x33, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addSHExprOpPrefix =
             lam #var"".
               lam x33.
                 lam st.
                   optionMap (breakableAddPrefix config3 x33) st
           in
           let addSHExprOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x33.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st = breakableAddPostfix config3 x33 st in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc (deref p.errors) (getInfo_SHExprOp x33, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeSHExprOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res60 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse config3 st
                        with
                          Some (tops & ([ top ] ++ _))
                        then
                          let errs = breakableDefaultHighlight reportConfig3 p.content tops
                          in
                          let res60 = unsplit_SHExprOp top in
                          match
                            null errs
                          with
                            true
                          then
                            Some
                              res60
                          else
                            (modref p.errors (concat (deref p.errors) errs))
                            ; Some
                              (res60.0, BadSHExpr
                                { info = res60.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref p.errors)
                                  (NoInfo
                                    {}, "Unfinished SHExpr")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadSHExpr
                     { info = NoInfo
                           {} })
                   res60
           in
           [ { nt = kleene,
               label = {},
               rhs = [ ntSym #var"SHDecl",
                   ntSym kleene ],
               action =
                 lam state: {errors: Ref [(Info, [Char])], content: String}.
                   lam res.
                     match
                       res
                     with
                       [ UserSym ntVal,
                         UserSym val1 ]
                     in
                     let ntVal: (Info, SHDecl) = fromDyn ntVal in
                       let val1: {decls: [SHDecl], __br_info: Info, __br_terms: [Info]} = fromDyn val1
                       in
                       asDyn
                         { __br_info = mergeInfo ntVal.0 val1.__br_info,
                           __br_terms = val1.__br_terms,
                           decls = concat [ ntVal.1 ] val1.decls } },
             { nt = kleene,
               label = {},
               rhs = "",
               action =
                 lam state1: {errors: Ref [(Info, [Char])], content: String}.
                   lam res1.
                     match
                       res1
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           decls = "" } },
             { nt = #var"SHFileAtom",
               label = {},
               rhs =
                 [ litSym "language",
                   tokSym (UIdentRepr
                        {}),
                   ntSym #var"SHDecl",
                   ntSym kleene ],
               action =
                 lam state2: {errors: Ref [(Info, [Char])], content: String}.
                   lam res2.
                     match
                       res2
                     with
                       [ LitParsed l,
                         TokParsed (UIdentTok x),
                         UserSym ntVal1,
                         UserSym val1 ]
                     in
                     let ntVal1: (Info, SHDecl) = fromDyn ntVal1 in
                       let val1: {decls: [SHDecl], __br_info: Info, __br_terms: [Info]} = fromDyn val1
                       in
                       asDyn
                         (LangSHFileOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l.info
                                  [ x.info,
                                    ntVal1.0,
                                    val1.__br_info ],
                              __br_terms =
                                join
                                  [ [ l.info ],
                                    [ x.info ],
                                    val1.__br_terms ],
                              decls = concat [ ntVal1.1 ] val1.decls,
                              name = [ { v = x.val, i = x.info } ] }) },
             { nt = #var"SHDeclAtom",
               label = {},
               rhs =
                 [ litSym "start",
                   tokSym (UIdentRepr
                        {}) ],
               action =
                 lam state3: {errors: Ref [(Info, [Char])], content: String}.
                   lam res3.
                     match
                       res3
                     with
                       [ LitParsed l1,
                         TokParsed (UIdentTok x1) ]
                     in
                     asDyn
                         (StartSHDeclOp
                            { __br_info = mergeInfo l1.info x1.info,
                              __br_terms = concat [ l1.info ] [ x1.info ],
                              name = [ { v = nameNoSym x1.val, i = x1.info } ] }) },
             { nt = #var"SHDeclAtom",
               label = {},
               rhs =
                 [ litSym "include",
                   tokSym (StringRepr
                        {}) ],
               action =
                 lam state4: {errors: Ref [(Info, [Char])], content: String}.
                   lam res4.
                     match
                       res4
                     with
                       [ LitParsed l2,
                         TokParsed (StringTok x2) ]
                     in
                     asDyn
                         (IncludeSHDeclOp
                            { __br_info = mergeInfo l2.info x2.info,
                              __br_terms = concat [ l2.info ] [ x2.info ],
                              path = [ { v = x2.val, i = x2.info } ] }) },
             { nt = kleene1,
               label = {},
               rhs =
                 [ tokSym (LIdentRepr
                        {}),
                   litSym "=",
                   ntSym #var"SHExpr",
                   litSym ",",
                   ntSym kleene1 ],
               action =
                 lam state5: {errors: Ref [(Info, [Char])], content: String}.
                   lam res5.
                     match
                       res5
                     with
                       [ TokParsed (LIdentTok x3),
                         LitParsed l3,
                         UserSym ntVal2,
                         LitParsed l4,
                         UserSym val2 ]
                     in
                     let ntVal2: (Info, SHExpr) = fromDyn ntVal2 in
                       let val2: {__br_info: Info, __br_terms: [Info], properties: [{val: SHExpr, name: {i: Info, v: String}}]} = fromDyn val2
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               x3.info
                               [ l3.info,
                                 ntVal2.0,
                                 l4.info,
                                 val2.__br_info ],
                           __br_terms =
                             join
                               [ [ x3.info ],
                                 [ l3.info ],
                                 [ l4.info ],
                                 val2.__br_terms ],
                           properties =
                             concat
                               [ { val =
                                     match
                                       [ ntVal2.1 ]
                                     with
                                       [ x4 ] ++ _
                                     in
                                     x4,
                                   name =
                                     match
                                       [ { v = x3.val, i = x3.info } ]
                                     with
                                       [ x5 ] ++ _
                                     in
                                     x5 } ]
                               val2.properties } },
             { nt = kleene1,
               label = {},
               rhs = "",
               action =
                 lam state6: {errors: Ref [(Info, [Char])], content: String}.
                   lam res6.
                     match
                       res6
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           properties = "" } },
             { nt = alt,
               label = {},
               rhs = "",
               action =
                 lam state7: {errors: Ref [(Info, [Char])], content: String}.
                   lam res7.
                     match
                       res7
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           properties = "" } },
             { nt = alt,
               label = {},
               rhs =
                 [ litSym "{",
                   ntSym kleene1,
                   litSym "}" ],
               action =
                 lam state8: {errors: Ref [(Info, [Char])], content: String}.
                   lam res8.
                     match
                       res8
                     with
                       [ LitParsed l5,
                         UserSym val2,
                         LitParsed l6 ]
                     in
                     let val2: {__br_info: Info, __br_terms: [Info], properties: [{val: SHExpr, name: {i: Info, v: String}}]} = fromDyn val2
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l5.info
                               [ val2.__br_info,
                                 l6.info ],
                           __br_terms =
                             join
                               [ [ l5.info ],
                                 val2.__br_terms,
                                 [ l6.info ] ],
                           properties = val2.properties } },
             { nt = #var"SHDeclAtom",
               label = {},
               rhs =
                 [ litSym "type",
                   tokSym (UIdentRepr
                        {}),
                   ntSym alt ],
               action =
                 lam state9: {errors: Ref [(Info, [Char])], content: String}.
                   lam res9.
                     match
                       res9
                     with
                       [ LitParsed l7,
                         TokParsed (UIdentTok x6),
                         UserSym val3 ]
                     in
                     let val3: {__br_info: Info, __br_terms: [Info], properties: [{val: SHExpr, name: {i: Info, v: String}}]} = fromDyn val3
                       in
                       asDyn
                         (TypeSHDeclOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l7.info
                                  [ x6.info,
                                    val3.__br_info ],
                              __br_terms =
                                join
                                  [ [ l7.info ],
                                    [ x6.info ],
                                    val3.__br_terms ],
                              name = [ { v = nameNoSym x6.val, i = x6.info } ],
                              properties = val3.properties }) },
             { nt = alt1,
               label = {},
               rhs = "",
               action =
                 lam state10: {errors: Ref [(Info, [Char])], content: String}.
                   lam res10.
                     match
                       res10
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           name = "" } },
             { nt = alt1,
               label = {},
               rhs = [ tokSym (UIdentRepr
                        {}) ],
               action =
                 lam state11: {errors: Ref [(Info, [Char])], content: String}.
                   lam res11.
                     match
                       res11
                     with
                       [ TokParsed (UIdentTok x7) ]
                     in
                     asDyn
                         { __br_info = x7.info,
                           __br_terms = [ x7.info ],
                           name = [ { v = nameNoSym x7.val, i = x7.info } ] } },
             { nt = kleene2,
               label = {},
               rhs =
                 [ tokSym (LIdentRepr
                        {}),
                   litSym "=",
                   ntSym #var"SHExpr",
                   litSym ",",
                   ntSym kleene2 ],
               action =
                 lam state12: {errors: Ref [(Info, [Char])], content: String}.
                   lam res12.
                     match
                       res12
                     with
                       [ TokParsed (LIdentTok x8),
                         LitParsed l8,
                         UserSym ntVal3,
                         LitParsed l9,
                         UserSym val4 ]
                     in
                     let ntVal3: (Info, SHExpr) = fromDyn ntVal3 in
                       let val4: {__br_info: Info, __br_terms: [Info], properties: [{val: SHExpr, name: {i: Info, v: String}}]} = fromDyn val4
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               x8.info
                               [ l8.info,
                                 ntVal3.0,
                                 l9.info,
                                 val4.__br_info ],
                           __br_terms =
                             join
                               [ [ x8.info ],
                                 [ l8.info ],
                                 [ l9.info ],
                                 val4.__br_terms ],
                           properties =
                             concat
                               [ { val =
                                     match
                                       [ ntVal3.1 ]
                                     with
                                       [ x9 ] ++ _
                                     in
                                     x9,
                                   name =
                                     match
                                       [ { v = x8.val, i = x8.info } ]
                                     with
                                       [ x10 ] ++ _
                                     in
                                     x10 } ]
                               val4.properties } },
             { nt = kleene2,
               label = {},
               rhs = "",
               action =
                 lam state13: {errors: Ref [(Info, [Char])], content: String}.
                   lam res13.
                     match
                       res13
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           properties = "" } },
             { nt = alt2,
               label = {},
               rhs = "",
               action =
                 lam state14: {errors: Ref [(Info, [Char])], content: String}.
                   lam res14.
                     match
                       res14
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           properties = "" } },
             { nt = alt2,
               label = {},
               rhs =
                 [ litSym "{",
                   ntSym kleene2,
                   litSym "}" ],
               action =
                 lam state15: {errors: Ref [(Info, [Char])], content: String}.
                   lam res15.
                     match
                       res15
                     with
                       [ LitParsed l10,
                         UserSym val4,
                         LitParsed l11 ]
                     in
                     let val4: {__br_info: Info, __br_terms: [Info], properties: [{val: SHExpr, name: {i: Info, v: String}}]} = fromDyn val4
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l10.info
                               [ val4.__br_info,
                                 l11.info ],
                           __br_terms =
                             join
                               [ [ l10.info ],
                                 val4.__br_terms,
                                 [ l11.info ] ],
                           properties = val4.properties } },
             { nt = #var"SHDeclAtom",
               label = {},
               rhs =
                 [ litSym "token",
                   ntSym alt1,
                   ntSym alt2 ],
               action =
                 lam state16: {errors: Ref [(Info, [Char])], content: String}.
                   lam res16.
                     match
                       res16
                     with
                       [ LitParsed l12,
                         UserSym val5,
                         UserSym val6 ]
                     in
                     let val5: {name: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} = fromDyn val5
                       in
                       let val6: {__br_info: Info, __br_terms: [Info], properties: [{val: SHExpr, name: {i: Info, v: String}}]} = fromDyn val6
                       in
                       asDyn
                         (TokenSHDeclOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l12.info
                                  [ val5.__br_info,
                                    val6.__br_info ],
                              __br_terms =
                                join
                                  [ [ l12.info ],
                                    val5.__br_terms,
                                    val6.__br_terms ],
                              name = val5.name,
                              properties = val6.properties }) },
             { nt = alt3,
               label = {},
               rhs = "",
               action =
                 lam state17: {errors: Ref [(Info, [Char])], content: String}.
                   lam res17.
                     match
                       res17
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           noeq = "" } },
             { nt = alt3,
               label = {},
               rhs = [ litSym "~" ],
               action =
                 lam state18: {errors: Ref [(Info, [Char])], content: String}.
                   lam res18.
                     match
                       res18
                     with
                       [ LitParsed l13 ]
                     in
                     asDyn
                         { __br_info = l13.info,
                           __br_terms = [ l13.info ],
                           noeq = [ l13.info ] } },
             { nt = kleene3,
               label = {},
               rhs =
                 [ tokSym (UIdentRepr
                        {}),
                   ntSym kleene3 ],
               action =
                 lam state19: {errors: Ref [(Info, [Char])], content: String}.
                   lam res19.
                     match
                       res19
                     with
                       [ TokParsed (UIdentTok x11),
                         UserSym val7 ]
                     in
                     let val7: {__br_info: Info, operators: [{i: Info, v: Name}], __br_terms: [Info]} = fromDyn val7
                       in
                       asDyn
                         { __br_info = mergeInfo x11.info val7.__br_info,
                           __br_terms = concat [ x11.info ] val7.__br_terms,
                           operators =
                             concat [ { v = nameNoSym x11.val, i = x11.info } ] val7.operators } },
             { nt = kleene3,
               label = {},
               rhs = "",
               action =
                 lam state20: {errors: Ref [(Info, [Char])], content: String}.
                   lam res20.
                     match
                       res20
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           operators = "" } },
             { nt = kleene4,
               label = {},
               rhs =
                 [ ntSym alt3,
                   tokSym (UIdentRepr
                        {}),
                   ntSym kleene3,
                   litSym ";",
                   ntSym kleene4 ],
               action =
                 lam state21: {errors: Ref [(Info, [Char])], content: String}.
                   lam res21.
                     match
                       res21
                     with
                       [ UserSym val8,
                         TokParsed (UIdentTok x12),
                         UserSym val7,
                         LitParsed l14,
                         UserSym val9 ]
                     in
                     let val8: {noeq: [Info], __br_info: Info, __br_terms: [Info]} = fromDyn val8
                       in
                       let val7: {__br_info: Info, operators: [{i: Info, v: Name}], __br_terms: [Info]} = fromDyn val7
                       in
                       let val9: {levels: [{noeq: Option Info, operators: [{i: Info, v: Name}]}], __br_info: Info, __br_terms: [Info]} = fromDyn val9
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               val8.__br_info
                               [ x12.info,
                                 val7.__br_info,
                                 l14.info,
                                 val9.__br_info ],
                           __br_terms =
                             join
                               [ val8.__br_terms,
                                 [ x12.info ],
                                 val7.__br_terms,
                                 [ l14.info ],
                                 val9.__br_terms ],
                           levels =
                             concat
                               [ { noeq =
                                     match
                                       val8.noeq
                                     with
                                       [ x13 ] ++ _
                                     then
                                       Some
                                         x13
                                     else
                                       None
                                         {},
                                   operators =
                                     concat [ { v = nameNoSym x12.val, i = x12.info } ] val7.operators } ]
                               val9.levels } },
             { nt = kleene4,
               label = {},
               rhs = "",
               action =
                 lam state22: {errors: Ref [(Info, [Char])], content: String}.
                   lam res22.
                     match
                       res22
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           levels = "" } },
             { nt = kleene5,
               label = {},
               rhs =
                 [ tokSym (UIdentRepr
                        {}),
                   ntSym kleene5 ],
               action =
                 lam state23: {errors: Ref [(Info, [Char])], content: String}.
                   lam res23.
                     match
                       res23
                     with
                       [ TokParsed (UIdentTok x14),
                         UserSym val10 ]
                     in
                     let val10: {lefts: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} = fromDyn val10
                       in
                       asDyn
                         { __br_info = mergeInfo x14.info val10.__br_info,
                           __br_terms = concat [ x14.info ] val10.__br_terms,
                           lefts =
                             concat [ { v = nameNoSym x14.val, i = x14.info } ] val10.lefts } },
             { nt = kleene5,
               label = {},
               rhs = "",
               action =
                 lam state24: {errors: Ref [(Info, [Char])], content: String}.
                   lam res24.
                     match
                       res24
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           lefts = "" } },
             { nt = kleene6,
               label = {},
               rhs =
                 [ tokSym (UIdentRepr
                        {}),
                   ntSym kleene6 ],
               action =
                 lam state25: {errors: Ref [(Info, [Char])], content: String}.
                   lam res25.
                     match
                       res25
                     with
                       [ TokParsed (UIdentTok x15),
                         UserSym val11 ]
                     in
                     let val11: {rights: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} = fromDyn val11
                       in
                       asDyn
                         { __br_info = mergeInfo x15.info val11.__br_info,
                           __br_terms = concat [ x15.info ] val11.__br_terms,
                           rights =
                             concat [ { v = nameNoSym x15.val, i = x15.info } ] val11.rights } },
             { nt = kleene6,
               label = {},
               rhs = "",
               action =
                 lam state26: {errors: Ref [(Info, [Char])], content: String}.
                   lam res26.
                     match
                       res26
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           rights = "" } },
             { nt = kleene7,
               label = {},
               rhs =
                 [ tokSym (UIdentRepr
                        {}),
                   ntSym kleene5,
                   litSym "?",
                   tokSym (UIdentRepr
                        {}),
                   ntSym kleene6,
                   litSym ";",
                   ntSym kleene7 ],
               action =
                 lam state27: {errors: Ref [(Info, [Char])], content: String}.
                   lam res27.
                     match
                       res27
                     with
                       [ TokParsed (UIdentTok x16),
                         UserSym val10,
                         LitParsed l15,
                         TokParsed (UIdentTok x17),
                         UserSym val11,
                         LitParsed l16,
                         UserSym val12 ]
                     in
                     let val10: {lefts: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} = fromDyn val10
                       in
                       let val11: {rights: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} = fromDyn val11
                       in
                       let val12: {__br_info: Info, __br_terms: [Info], exceptions: [{lefts: [{i: Info, v: Name}], rights: [{i: Info, v: Name}]}]} = fromDyn val12
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               x16.info
                               [ val10.__br_info,
                                 l15.info,
                                 x17.info,
                                 val11.__br_info,
                                 l16.info,
                                 val12.__br_info ],
                           __br_terms =
                             join
                               [ [ x16.info ],
                                 val10.__br_terms,
                                 [ l15.info ],
                                 [ x17.info ],
                                 val11.__br_terms,
                                 [ l16.info ],
                                 val12.__br_terms ],
                           exceptions =
                             concat
                               [ { lefts =
                                     concat [ { v = nameNoSym x16.val, i = x16.info } ] val10.lefts,
                                   rights =
                                     concat [ { v = nameNoSym x17.val, i = x17.info } ] val11.rights } ]
                               val12.exceptions } },
             { nt = kleene7,
               label = {},
               rhs = "",
               action =
                 lam state28: {errors: Ref [(Info, [Char])], content: String}.
                   lam res28.
                     match
                       res28
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           exceptions = "" } },
             { nt = alt4,
               label = {},
               rhs = "",
               action =
                 lam state29: {errors: Ref [(Info, [Char])], content: String}.
                   lam res29.
                     match
                       res29
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           exceptions = "" } },
             { nt = alt4,
               label = {},
               rhs =
                 [ litSym "except",
                   litSym "{",
                   ntSym kleene7,
                   litSym "}" ],
               action =
                 lam state30: {errors: Ref [(Info, [Char])], content: String}.
                   lam res30.
                     match
                       res30
                     with
                       [ LitParsed l17,
                         LitParsed l18,
                         UserSym val12,
                         LitParsed l19 ]
                     in
                     let val12: {__br_info: Info, __br_terms: [Info], exceptions: [{lefts: [{i: Info, v: Name}], rights: [{i: Info, v: Name}]}]} = fromDyn val12
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l17.info
                               [ l18.info,
                                 val12.__br_info,
                                 l19.info ],
                           __br_terms =
                             join
                               [ [ l17.info ],
                                 [ l18.info ],
                                 val12.__br_terms,
                                 [ l19.info ] ],
                           exceptions = val12.exceptions } },
             { nt = #var"SHDeclAtom",
               label = {},
               rhs =
                 [ litSym "precedence",
                   litSym "{",
                   ntSym kleene4,
                   litSym "}",
                   ntSym alt4 ],
               action =
                 lam state31: {errors: Ref [(Info, [Char])], content: String}.
                   lam res31.
                     match
                       res31
                     with
                       [ LitParsed l20,
                         LitParsed l21,
                         UserSym val9,
                         LitParsed l22,
                         UserSym val13 ]
                     in
                     let val9: {levels: [{noeq: Option Info, operators: [{i: Info, v: Name}]}], __br_info: Info, __br_terms: [Info]} = fromDyn val9
                       in
                       let val13: {__br_info: Info, __br_terms: [Info], exceptions: [{lefts: [{i: Info, v: Name}], rights: [{i: Info, v: Name}]}]} = fromDyn val13
                       in
                       asDyn
                         (PrecedenceTableSHDeclOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l20.info
                                  [ l21.info,
                                    val9.__br_info,
                                    l22.info,
                                    val13.__br_info ],
                              __br_terms =
                                join
                                  [ [ l20.info ],
                                    [ l21.info ],
                                    val9.__br_terms,
                                    [ l22.info ],
                                    val13.__br_terms ],
                              levels = val9.levels,
                              exceptions = val13.exceptions }) },
             { nt = alt5,
               label = {},
               rhs = [ litSym "prod" ],
               action =
                 lam state32: {errors: Ref [(Info, [Char])], content: String}.
                   lam res32.
                     match
                       res32
                     with
                       [ LitParsed l23 ]
                     in
                     asDyn
                         { __br_info = l23.info,
                           __br_terms = [ l23.info ],
                           kinf = "",
                           kpref = "",
                           kprod = [ l23.info ],
                           kpostf = "" } },
             { nt = alt5,
               label = {},
               rhs = [ litSym "infix" ],
               action =
                 lam state33: {errors: Ref [(Info, [Char])], content: String}.
                   lam res33.
                     match
                       res33
                     with
                       [ LitParsed l24 ]
                     in
                     asDyn
                         { __br_info = l24.info,
                           __br_terms = [ l24.info ],
                           kinf = [ l24.info ],
                           kpref = "",
                           kprod = "",
                           kpostf = "" } },
             { nt = alt5,
               label = {},
               rhs = [ litSym "prefix" ],
               action =
                 lam state34: {errors: Ref [(Info, [Char])], content: String}.
                   lam res34.
                     match
                       res34
                     with
                       [ LitParsed l25 ]
                     in
                     asDyn
                         { __br_info = l25.info,
                           __br_terms = [ l25.info ],
                           kinf = "",
                           kpref = [ l25.info ],
                           kprod = "",
                           kpostf = "" } },
             { nt = alt5,
               label = {},
               rhs = [ litSym "postfix" ],
               action =
                 lam state35: {errors: Ref [(Info, [Char])], content: String}.
                   lam res35.
                     match
                       res35
                     with
                       [ LitParsed l26 ]
                     in
                     asDyn
                         { __br_info = l26.info,
                           __br_terms = [ l26.info ],
                           kinf = "",
                           kpref = "",
                           kprod = "",
                           kpostf = [ l26.info ] } },
             { nt = alt6,
               label = {},
               rhs = "",
               action =
                 lam state36: {errors: Ref [(Info, [Char])], content: String}.
                   lam res36.
                     match
                       res36
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           assoc = "" } },
             { nt = alt6,
               label = {},
               rhs = [ tokSym (LIdentRepr
                        {}) ],
               action =
                 lam state37: {errors: Ref [(Info, [Char])], content: String}.
                   lam res37.
                     match
                       res37
                     with
                       [ TokParsed (LIdentTok x18) ]
                     in
                     asDyn
                         { __br_info = x18.info,
                           __br_terms = [ x18.info ],
                           assoc = [ { v = x18.val, i = x18.info } ] } },
             { nt = #var"SHDeclAtom",
               label = {},
               rhs =
                 [ ntSym alt5,
                   ntSym alt6,
                   tokSym (UIdentRepr
                        {}),
                   litSym ":",
                   tokSym (UIdentRepr
                        {}),
                   litSym "=",
                   ntSym #var"SHRegex" ],
               action =
                 lam state38: {errors: Ref [(Info, [Char])], content: String}.
                   lam res38.
                     match
                       res38
                     with
                       [ UserSym val14,
                         UserSym val15,
                         TokParsed (UIdentTok x19),
                         LitParsed l27,
                         TokParsed (UIdentTok x20),
                         LitParsed l28,
                         UserSym ntVal4 ]
                     in
                     let val14: {kinf: [Info], kpref: [Info], kprod: [Info], kpostf: [Info], __br_info: Info, __br_terms: [Info]} = fromDyn val14
                       in
                       let val15: {assoc: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]} = fromDyn val15
                       in
                       let ntVal4: (Info, SHRegex) = fromDyn ntVal4 in
                       asDyn
                         (ProductionSHDeclOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  val14.__br_info
                                  [ val15.__br_info,
                                    x19.info,
                                    l27.info,
                                    x20.info,
                                    l28.info,
                                    ntVal4.0 ],
                              __br_terms =
                                join
                                  [ val14.__br_terms,
                                    val15.__br_terms,
                                    [ x19.info ],
                                    [ l27.info ],
                                    [ x20.info ],
                                    [ l28.info ] ],
                              nt = [ { v = nameNoSym x20.val, i = x20.info } ],
                              name = [ { v = nameNoSym x19.val, i = x19.info } ],
                              kinf = val14.kinf,
                              kpref = val14.kpref,
                              kprod = val14.kprod,
                              kpostf = val14.kpostf,
                              assoc = val15.assoc,
                              regex = [ ntVal4.1 ] }) },
             { nt = #var"SHRegexAtom",
               label = {},
               rhs =
                 [ litSym "{",
                   ntSym #var"SHRegex",
                   litSym "}" ],
               action =
                 lam state39: {errors: Ref [(Info, [Char])], content: String}.
                   lam res39.
                     match
                       res39
                     with
                       [ LitParsed l29,
                         UserSym ntVal5,
                         LitParsed l30 ]
                     in
                     let ntVal5: (Info, SHRegex) = fromDyn ntVal5 in
                       asDyn
                         (RecordSHRegexOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l29.info
                                  [ ntVal5.0,
                                    l30.info ],
                              __br_terms = concat [ l29.info ] [ l30.info ],
                              regex = [ ntVal5.1 ] }) },
             { nt = #var"SHRegexAtom",
               label = {},
               rhs = [ litSym "empty" ],
               action =
                 lam state40: {errors: Ref [(Info, [Char])], content: String}.
                   lam res40.
                     match
                       res40
                     with
                       [ LitParsed l31 ]
                     in
                     asDyn
                         (EmptySHRegexOp
                            { __br_info = l31.info, __br_terms = [ l31.info ] }) },
             { nt = #var"SHRegexAtom",
               label = {},
               rhs = [ tokSym (StringRepr
                        {}) ],
               action =
                 lam state41: {errors: Ref [(Info, [Char])], content: String}.
                   lam res41.
                     match
                       res41
                     with
                       [ TokParsed (StringTok x21) ]
                     in
                     asDyn
                         (LiteralSHRegexOp
                            { val = [ { v = x21.val, i = x21.info } ],
                              __br_info = x21.info,
                              __br_terms = [ x21.info ] }) },
             { nt = alt7,
               label = {},
               rhs = "",
               action =
                 lam state42: {errors: Ref [(Info, [Char])], content: String}.
                   lam res42.
                     match
                       res42
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           arg = "" } },
             { nt = alt7,
               label = {},
               rhs =
                 [ litSym "[",
                   ntSym #var"SHExpr",
                   litSym "]" ],
               action =
                 lam state43: {errors: Ref [(Info, [Char])], content: String}.
                   lam res43.
                     match
                       res43
                     with
                       [ LitParsed l32,
                         UserSym ntVal6,
                         LitParsed l33 ]
                     in
                     let ntVal6: (Info, SHExpr) = fromDyn ntVal6 in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l32.info
                               [ ntVal6.0,
                                 l33.info ],
                           __br_terms = concat [ l32.info ] [ l33.info ],
                           arg = [ ntVal6.1 ] } },
             { nt = #var"SHRegexAtom",
               label = {},
               rhs =
                 [ tokSym (UIdentRepr
                        {}),
                   ntSym alt7 ],
               action =
                 lam state44: {errors: Ref [(Info, [Char])], content: String}.
                   lam res44.
                     match
                       res44
                     with
                       [ TokParsed (UIdentTok x22),
                         UserSym val16 ]
                     in
                     let val16: {arg: [SHExpr], __br_info: Info, __br_terms: [Info]} = fromDyn val16
                       in
                       asDyn
                         (TokenSHRegexOp
                            { __br_info = mergeInfo x22.info val16.__br_info,
                              __br_terms = concat [ x22.info ] val16.__br_terms,
                              name = [ { v = nameNoSym x22.val, i = x22.info } ],
                              arg = val16.arg }) },
             { nt = #var"SHRegexPostfix",
               label = {},
               rhs = [ litSym "+" ],
               action =
                 lam state45: {errors: Ref [(Info, [Char])], content: String}.
                   lam res45.
                     match
                       res45
                     with
                       [ LitParsed l34 ]
                     in
                     asDyn
                         (RepeatPlusSHRegexOp
                            { __br_info = l34.info, __br_terms = [ l34.info ] }) },
             { nt = #var"SHRegexPostfix",
               label = {},
               rhs = [ litSym "*" ],
               action =
                 lam state46: {errors: Ref [(Info, [Char])], content: String}.
                   lam res46.
                     match
                       res46
                     with
                       [ LitParsed l35 ]
                     in
                     asDyn
                         (RepeatStarSHRegexOp
                            { __br_info = l35.info, __br_terms = [ l35.info ] }) },
             { nt = #var"SHRegexPostfix",
               label = {},
               rhs = [ litSym "?" ],
               action =
                 lam state47: {errors: Ref [(Info, [Char])], content: String}.
                   lam res47.
                     match
                       res47
                     with
                       [ LitParsed l36 ]
                     in
                     asDyn
                         (RepeatQuestionSHRegexOp
                            { __br_info = l36.info, __br_terms = [ l36.info ] }) },
             { nt = #var"SHRegexPrefix",
               label = {},
               rhs =
                 [ tokSym (LIdentRepr
                        {}),
                   litSym ":" ],
               action =
                 lam state48: {errors: Ref [(Info, [Char])], content: String}.
                   lam res48.
                     match
                       res48
                     with
                       [ TokParsed (LIdentTok x23),
                         LitParsed l37 ]
                     in
                     asDyn
                         (NamedSHRegexOp
                            { __br_info = mergeInfo x23.info l37.info,
                              __br_terms = concat [ x23.info ] [ l37.info ],
                              name = [ { v = x23.val, i = x23.info } ] }) },
             { nt = #var"SHRegexInfix",
               label = {},
               rhs = [ litSym "|" ],
               action =
                 lam state49: {errors: Ref [(Info, [Char])], content: String}.
                   lam res49.
                     match
                       res49
                     with
                       [ LitParsed l38 ]
                     in
                     asDyn
                         (AlternativeSHRegexOp
                            { __br_info = l38.info, __br_terms = [ l38.info ] }) },
             { nt = #var"SHRegexInfix",
               label = {},
               rhs = "",
               action =
                 lam state50: {errors: Ref [(Info, [Char])], content: String}.
                   lam res50.
                     match
                       res50
                     with
                       ""
                     in
                     asDyn
                         (ConcatSHRegexOp
                            { __br_info = NoInfo
                                  {},
                              __br_terms = "" }) },
             { nt = #var"SHExprInfix",
               label = {},
               rhs = "",
               action =
                 lam state51: {errors: Ref [(Info, [Char])], content: String}.
                   lam res51.
                     match
                       res51
                     with
                       ""
                     in
                     asDyn
                         (AppSHExprOp
                            { __br_info = NoInfo
                                  {},
                              __br_terms = "" }) },
             { nt = #var"SHExprAtom",
               label = {},
               rhs = [ tokSym (UIdentRepr
                        {}) ],
               action =
                 lam state52: {errors: Ref [(Info, [Char])], content: String}.
                   lam res52.
                     match
                       res52
                     with
                       [ TokParsed (UIdentTok x24) ]
                     in
                     asDyn
                         (ConSHExprOp
                            { __br_info = x24.info,
                              __br_terms = [ x24.info ],
                              name = [ { v = nameNoSym x24.val, i = x24.info } ] }) },
             { nt = #var"SHExprAtom",
               label = {},
               rhs = [ tokSym (StringRepr
                        {}) ],
               action =
                 lam state53: {errors: Ref [(Info, [Char])], content: String}.
                   lam res53.
                     match
                       res53
                     with
                       [ TokParsed (StringTok x25) ]
                     in
                     asDyn
                         (StringSHExprOp
                            { val = [ { v = x25.val, i = x25.info } ],
                              __br_info = x25.info,
                              __br_terms = [ x25.info ] }) },
             { nt = #var"SHExprAtom",
               label = {},
               rhs = [ tokSym (LIdentRepr
                        {}) ],
               action =
                 lam state54: {errors: Ref [(Info, [Char])], content: String}.
                   lam res54.
                     match
                       res54
                     with
                       [ TokParsed (LIdentTok x26) ]
                     in
                     asDyn
                         (VariableSHExprOp
                            { __br_info = x26.info,
                              __br_terms = [ x26.info ],
                              name = [ { v = nameNoSym x26.val, i = x26.info } ] }) },
             { nt = kleene8,
               label = {},
               rhs =
                 [ litSym ",",
                   tokSym (LIdentRepr
                        {}),
                   litSym "=",
                   ntSym #var"SHExpr",
                   ntSym kleene8 ],
               action =
                 lam state55: {errors: Ref [(Info, [Char])], content: String}.
                   lam res55.
                     match
                       res55
                     with
                       [ LitParsed l39,
                         TokParsed (LIdentTok x27),
                         LitParsed l40,
                         UserSym ntVal7,
                         UserSym val17 ]
                     in
                     let ntVal7: (Info, SHExpr) = fromDyn ntVal7 in
                       let val17: {fields: [{val: SHExpr, name: {i: Info, v: String}}], __br_info: Info, __br_terms: [Info]} = fromDyn val17
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l39.info
                               [ x27.info,
                                 l40.info,
                                 ntVal7.0,
                                 val17.__br_info ],
                           __br_terms =
                             join
                               [ [ l39.info ],
                                 [ x27.info ],
                                 [ l40.info ],
                                 val17.__br_terms ],
                           fields =
                             concat
                               [ { val =
                                     match
                                       [ ntVal7.1 ]
                                     with
                                       [ x28 ] ++ _
                                     in
                                     x28,
                                   name =
                                     match
                                       [ { v = x27.val, i = x27.info } ]
                                     with
                                       [ x29 ] ++ _
                                     in
                                     x29 } ]
                               val17.fields } },
             { nt = kleene8,
               label = {},
               rhs = "",
               action =
                 lam state56: {errors: Ref [(Info, [Char])], content: String}.
                   lam res56.
                     match
                       res56
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           fields = "" } },
             { nt = alt8,
               label = {},
               rhs = "",
               action =
                 lam state57: {errors: Ref [(Info, [Char])], content: String}.
                   lam res57.
                     match
                       res57
                     with
                       ""
                     in
                     asDyn
                         { __br_info = NoInfo
                               {},
                           __br_terms = "",
                           fields = "" } },
             { nt = alt8,
               label = {},
               rhs =
                 [ tokSym (LIdentRepr
                        {}),
                   litSym "=",
                   ntSym #var"SHExpr",
                   ntSym kleene8 ],
               action =
                 lam state58: {errors: Ref [(Info, [Char])], content: String}.
                   lam res58.
                     match
                       res58
                     with
                       [ TokParsed (LIdentTok x30),
                         LitParsed l41,
                         UserSym ntVal8,
                         UserSym val17 ]
                     in
                     let ntVal8: (Info, SHExpr) = fromDyn ntVal8 in
                       let val17: {fields: [{val: SHExpr, name: {i: Info, v: String}}], __br_info: Info, __br_terms: [Info]} = fromDyn val17
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               x30.info
                               [ l41.info,
                                 ntVal8.0,
                                 val17.__br_info ],
                           __br_terms =
                             join
                               [ [ x30.info ],
                                 [ l41.info ],
                                 val17.__br_terms ],
                           fields =
                             concat
                               [ { val =
                                     match
                                       [ ntVal8.1 ]
                                     with
                                       [ x31 ] ++ _
                                     in
                                     x31,
                                   name =
                                     match
                                       [ { v = x30.val, i = x30.info } ]
                                     with
                                       [ x32 ] ++ _
                                     in
                                     x32 } ]
                               val17.fields } },
             { nt = #var"SHExprAtom",
               label = {},
               rhs =
                 [ litSym "{",
                   ntSym alt8,
                   litSym "}" ],
               action =
                 lam state59: {errors: Ref [(Info, [Char])], content: String}.
                   lam res59.
                     match
                       res59
                     with
                       [ LitParsed l42,
                         UserSym val18,
                         LitParsed l43 ]
                     in
                     let val18: {fields: [{val: SHExpr, name: {i: Info, v: String}}], __br_info: Info, __br_terms: [Info]} = fromDyn val18
                       in
                       asDyn
                         (RecordSHExprOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l42.info
                                  [ val18.__br_info,
                                    l43.info ],
                              __br_terms =
                                join
                                  [ [ l42.info ],
                                    val18.__br_terms,
                                    [ l43.info ] ],
                              fields = val18.fields }) },
             { nt = #var"SHRegexAtom",
               label = {},
               rhs =
                 [ litSym "(",
                   ntSym #var"SHRegex",
                   litSym ")" ],
               action =
                 lam #var"".
                   lam seq.
                     match
                       seq
                     with
                       [ LitParsed l44,
                         UserSym ntVal9,
                         LitParsed l45 ]
                     in
                     let ntVal9: (Info, SHRegex) = fromDyn ntVal9 in
                       asDyn
                         (SHRegexGrouping
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l44.info
                                  [ ntVal9.0,
                                    l45.info ],
                              __br_terms =
                                [ l44.info,
                                  l45.info ],
                              inner =
                                match
                                  [ ntVal9.1 ]
                                with
                                  [ x33 ]
                                in
                                x33 }) },
             { nt = #var"SHExprAtom",
               label = {},
               rhs =
                 [ litSym "(",
                   ntSym #var"SHExpr",
                   litSym ")" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ LitParsed l46,
                         UserSym ntVal10,
                         LitParsed l47 ]
                     in
                     let ntVal10: (Info, SHExpr) = fromDyn ntVal10 in
                       asDyn
                         (SHExprGrouping
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l46.info
                                  [ ntVal10.0,
                                    l47.info ],
                              __br_terms =
                                [ l46.info,
                                  l47.info ],
                              inner =
                                match
                                  [ ntVal10.1 ]
                                with
                                  [ x33 ]
                                in
                                x33 }) },
             { nt = #var"SHFile",
               label = {},
               rhs = [ ntSym #var"SHFile_lclosed" ],
               action =
                 lam #var"".
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState {})) },
             { nt = #var"SHFile_lclosed",
               label = {},
               rhs =
                 [ ntSym #var"SHFileAtom",
                   ntSym #var"SHFile_lopen" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHFileOpAtom p (fromDyn x33) st)) },
             { nt = #var"SHFile_lopen",
               label = {},
               rhs =
                 [ ntSym #var"SHFileInfix",
                   ntSym #var"SHFile_lclosed" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHFileOpInfix p (fromDyn x33) st)) },
             { nt = #var"SHFile_lclosed",
               label = {},
               rhs =
                 [ ntSym #var"SHFilePrefix",
                   ntSym #var"SHFile_lclosed" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHFileOpPrefix p (fromDyn x33) st)) },
             { nt = #var"SHFile_lopen",
               label = {},
               rhs =
                 [ ntSym #var"SHFilePostfix",
                   ntSym #var"SHFile_lopen" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHFileOpPostfix p (fromDyn x33) st)) },
             { nt = #var"SHFile_lopen",
               label = {},
               rhs = "",
               action =
                 lam p.
                   lam #var"".
                     asDyn (lam st.
                          finalizeSHFileOp p st) },
             { nt = #var"SHDecl",
               label = {},
               rhs = [ ntSym #var"SHDecl_lclosed" ],
               action =
                 lam #var"".
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState {})) },
             { nt = #var"SHDecl_lclosed",
               label = {},
               rhs =
                 [ ntSym #var"SHDeclAtom",
                   ntSym #var"SHDecl_lopen" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHDeclOpAtom p (fromDyn x33) st)) },
             { nt = #var"SHDecl_lopen",
               label = {},
               rhs =
                 [ ntSym #var"SHDeclInfix",
                   ntSym #var"SHDecl_lclosed" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHDeclOpInfix p (fromDyn x33) st)) },
             { nt = #var"SHDecl_lclosed",
               label = {},
               rhs =
                 [ ntSym #var"SHDeclPrefix",
                   ntSym #var"SHDecl_lclosed" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHDeclOpPrefix p (fromDyn x33) st)) },
             { nt = #var"SHDecl_lopen",
               label = {},
               rhs =
                 [ ntSym #var"SHDeclPostfix",
                   ntSym #var"SHDecl_lopen" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHDeclOpPostfix p (fromDyn x33) st)) },
             { nt = #var"SHDecl_lopen",
               label = {},
               rhs = "",
               action =
                 lam p.
                   lam #var"".
                     asDyn (lam st.
                          finalizeSHDeclOp p st) },
             { nt = #var"SHRegex",
               label = {},
               rhs = [ ntSym #var"SHRegex_lclosed" ],
               action =
                 lam #var"".
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState {})) },
             { nt = #var"SHRegex_lclosed",
               label = {},
               rhs =
                 [ ntSym #var"SHRegexAtom",
                   ntSym #var"SHRegex_lopen" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHRegexOpAtom p (fromDyn x33) st)) },
             { nt = #var"SHRegex_lopen",
               label = {},
               rhs =
                 [ ntSym #var"SHRegexInfix",
                   ntSym #var"SHRegex_lclosed" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHRegexOpInfix p (fromDyn x33) st)) },
             { nt = #var"SHRegex_lclosed",
               label = {},
               rhs =
                 [ ntSym #var"SHRegexPrefix",
                   ntSym #var"SHRegex_lclosed" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHRegexOpPrefix p (fromDyn x33) st)) },
             { nt = #var"SHRegex_lopen",
               label = {},
               rhs =
                 [ ntSym #var"SHRegexPostfix",
                   ntSym #var"SHRegex_lopen" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHRegexOpPostfix p (fromDyn x33) st)) },
             { nt = #var"SHRegex_lopen",
               label = {},
               rhs = "",
               action =
                 lam p.
                   lam #var"".
                     asDyn (lam st.
                          finalizeSHRegexOp p st) },
             { nt = #var"SHExpr",
               label = {},
               rhs = [ ntSym #var"SHExpr_lclosed" ],
               action =
                 lam #var"".
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState {})) },
             { nt = #var"SHExpr_lclosed",
               label = {},
               rhs =
                 [ ntSym #var"SHExprAtom",
                   ntSym #var"SHExpr_lopen" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHExprOpAtom p (fromDyn x33) st)) },
             { nt = #var"SHExpr_lopen",
               label = {},
               rhs =
                 [ ntSym #var"SHExprInfix",
                   ntSym #var"SHExpr_lclosed" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHExprOpInfix p (fromDyn x33) st)) },
             { nt = #var"SHExpr_lclosed",
               label = {},
               rhs =
                 [ ntSym #var"SHExprPrefix",
                   ntSym #var"SHExpr_lclosed" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHExprOpPrefix p (fromDyn x33) st)) },
             { nt = #var"SHExpr_lopen",
               label = {},
               rhs =
                 [ ntSym #var"SHExprPostfix",
                   ntSym #var"SHExpr_lopen" ],
               action =
                 lam p.
                   lam seq2.
                     match
                       seq2
                     with
                       [ UserSym x33,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn cont (addSHExprOpPostfix p (fromDyn x33) st)) },
             { nt = #var"SHExpr_lopen",
               label = {},
               rhs = "",
               action =
                 lam p.
                   lam #var"".
                     asDyn (lam st.
                          finalizeSHExprOp p st) } ] })
  in
  match
    target
  with
    Right table
  in
  table
let parseSelfhost =
  lam filename.
    lam content.
      use ParseSelfhost
      in
      let config4 = { errors = ref "", content = content } in
      let res60 = parseWithTable _table filename config4 content in
      let #var"X" = (res60, deref config4.errors) in
      match
        #var"X"
      with
        (Right dyn, "")
      then
        match
          fromDyn dyn
        with
          (_, res60)
        in
        Right
            res60
      else match
        #var"X"
      with
        (Left err, errors)
      then
        let err = ll1DefaultHighlight content (ll1ToErrorHighlightSpec err)
        in
        Left
          (snoc errors err)
      else match
        #var"X"
      with
        (_, errors)
      in
      Left
          errors
let parseSelfhostExn =
  lam filename.
    lam content.
      let #var"X" = parseSelfhost filename content in
      match
        #var"X"
      with
        Left errors
      then
        (for_
             errors
             (lam x33.
                match
                  x33
                with
                  (info, msg)
                in
                printLn (infoErrorString info msg)))
        ; exit 1
      else match
        #var"X"
      with
        Right file
      in
      file
mexpr
{}