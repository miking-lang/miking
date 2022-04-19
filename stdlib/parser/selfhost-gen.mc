include "seq.mc"

include "parser/ll1.mc"

include "parser/breakable.mc"

lang SelfhostBaseAst

  syn File =
  syn Decl =
  syn Regex =
  syn Expr =

  sem smapAccumL_File_File : ((a) -> ((File) -> ((a, File)))) -> ((a) -> ((File) -> ((a, File))))
  sem smapAccumL_File_File f acc =
  | x ->
    (acc, x)

  sem smap_File_File : ((File) -> (File)) -> ((File) -> (File))
  sem smap_File_File f =
  | x ->
    (smapAccumL_File_File
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_File_File : ((a) -> ((File) -> (a))) -> ((a) -> ((File) -> (a)))
  sem sfold_File_File f acc =
  | x ->
    (smapAccumL_File_File
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_File_Decl : ((a) -> ((Decl) -> ((a, Decl)))) -> ((a) -> ((File) -> ((a, File))))
  sem smapAccumL_File_Decl f acc =
  | x ->
    (acc, x)

  sem smap_File_Decl : ((Decl) -> (Decl)) -> ((File) -> (File))
  sem smap_File_Decl f =
  | x ->
    (smapAccumL_File_Decl
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_File_Decl : ((a) -> ((Decl) -> (a))) -> ((a) -> ((File) -> (a)))
  sem sfold_File_Decl f acc =
  | x ->
    (smapAccumL_File_Decl
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_File_Regex : ((a) -> ((Regex) -> ((a, Regex)))) -> ((a) -> ((File) -> ((a, File))))
  sem smapAccumL_File_Regex f acc =
  | x ->
    (acc, x)

  sem smap_File_Regex : ((Regex) -> (Regex)) -> ((File) -> (File))
  sem smap_File_Regex f =
  | x ->
    (smapAccumL_File_Regex
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_File_Regex : ((a) -> ((Regex) -> (a))) -> ((a) -> ((File) -> (a)))
  sem sfold_File_Regex f acc =
  | x ->
    (smapAccumL_File_Regex
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_File_Expr : ((a) -> ((Expr) -> ((a, Expr)))) -> ((a) -> ((File) -> ((a, File))))
  sem smapAccumL_File_Expr f acc =
  | x ->
    (acc, x)

  sem smap_File_Expr : ((Expr) -> (Expr)) -> ((File) -> (File))
  sem smap_File_Expr f =
  | x ->
    (smapAccumL_File_Expr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_File_Expr : ((a) -> ((Expr) -> (a))) -> ((a) -> ((File) -> (a)))
  sem sfold_File_Expr f acc =
  | x ->
    (smapAccumL_File_Expr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Decl_File : ((a) -> ((File) -> ((a, File)))) -> ((a) -> ((Decl) -> ((a, Decl))))
  sem smapAccumL_Decl_File f acc =
  | x ->
    (acc, x)

  sem smap_Decl_File : ((File) -> (File)) -> ((Decl) -> (Decl))
  sem smap_Decl_File f =
  | x ->
    (smapAccumL_Decl_File
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Decl_File : ((a) -> ((File) -> (a))) -> ((a) -> ((Decl) -> (a)))
  sem sfold_Decl_File f acc =
  | x ->
    (smapAccumL_Decl_File
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Decl_Decl : ((a) -> ((Decl) -> ((a, Decl)))) -> ((a) -> ((Decl) -> ((a, Decl))))
  sem smapAccumL_Decl_Decl f acc =
  | x ->
    (acc, x)

  sem smap_Decl_Decl : ((Decl) -> (Decl)) -> ((Decl) -> (Decl))
  sem smap_Decl_Decl f =
  | x ->
    (smapAccumL_Decl_Decl
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Decl_Decl : ((a) -> ((Decl) -> (a))) -> ((a) -> ((Decl) -> (a)))
  sem sfold_Decl_Decl f acc =
  | x ->
    (smapAccumL_Decl_Decl
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Decl_Regex : ((a) -> ((Regex) -> ((a, Regex)))) -> ((a) -> ((Decl) -> ((a, Decl))))
  sem smapAccumL_Decl_Regex f acc =
  | x ->
    (acc, x)

  sem smap_Decl_Regex : ((Regex) -> (Regex)) -> ((Decl) -> (Decl))
  sem smap_Decl_Regex f =
  | x ->
    (smapAccumL_Decl_Regex
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Decl_Regex : ((a) -> ((Regex) -> (a))) -> ((a) -> ((Decl) -> (a)))
  sem sfold_Decl_Regex f acc =
  | x ->
    (smapAccumL_Decl_Regex
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Decl_Expr : ((a) -> ((Expr) -> ((a, Expr)))) -> ((a) -> ((Decl) -> ((a, Decl))))
  sem smapAccumL_Decl_Expr f acc =
  | x ->
    (acc, x)

  sem smap_Decl_Expr : ((Expr) -> (Expr)) -> ((Decl) -> (Decl))
  sem smap_Decl_Expr f =
  | x ->
    (smapAccumL_Decl_Expr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Decl_Expr : ((a) -> ((Expr) -> (a))) -> ((a) -> ((Decl) -> (a)))
  sem sfold_Decl_Expr f acc =
  | x ->
    (smapAccumL_Decl_Expr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Regex_File : ((a) -> ((File) -> ((a, File)))) -> ((a) -> ((Regex) -> ((a, Regex))))
  sem smapAccumL_Regex_File f acc =
  | x ->
    (acc, x)

  sem smap_Regex_File : ((File) -> (File)) -> ((Regex) -> (Regex))
  sem smap_Regex_File f =
  | x ->
    (smapAccumL_Regex_File
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Regex_File : ((a) -> ((File) -> (a))) -> ((a) -> ((Regex) -> (a)))
  sem sfold_Regex_File f acc =
  | x ->
    (smapAccumL_Regex_File
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Regex_Decl : ((a) -> ((Decl) -> ((a, Decl)))) -> ((a) -> ((Regex) -> ((a, Regex))))
  sem smapAccumL_Regex_Decl f acc =
  | x ->
    (acc, x)

  sem smap_Regex_Decl : ((Decl) -> (Decl)) -> ((Regex) -> (Regex))
  sem smap_Regex_Decl f =
  | x ->
    (smapAccumL_Regex_Decl
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Regex_Decl : ((a) -> ((Decl) -> (a))) -> ((a) -> ((Regex) -> (a)))
  sem sfold_Regex_Decl f acc =
  | x ->
    (smapAccumL_Regex_Decl
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Regex_Regex : ((a) -> ((Regex) -> ((a, Regex)))) -> ((a) -> ((Regex) -> ((a, Regex))))
  sem smapAccumL_Regex_Regex f acc =
  | x ->
    (acc, x)

  sem smap_Regex_Regex : ((Regex) -> (Regex)) -> ((Regex) -> (Regex))
  sem smap_Regex_Regex f =
  | x ->
    (smapAccumL_Regex_Regex
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Regex_Regex : ((a) -> ((Regex) -> (a))) -> ((a) -> ((Regex) -> (a)))
  sem sfold_Regex_Regex f acc =
  | x ->
    (smapAccumL_Regex_Regex
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Regex_Expr : ((a) -> ((Expr) -> ((a, Expr)))) -> ((a) -> ((Regex) -> ((a, Regex))))
  sem smapAccumL_Regex_Expr f acc =
  | x ->
    (acc, x)

  sem smap_Regex_Expr : ((Expr) -> (Expr)) -> ((Regex) -> (Regex))
  sem smap_Regex_Expr f =
  | x ->
    (smapAccumL_Regex_Expr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Regex_Expr : ((a) -> ((Expr) -> (a))) -> ((a) -> ((Regex) -> (a)))
  sem sfold_Regex_Expr f acc =
  | x ->
    (smapAccumL_Regex_Expr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Expr_File : ((a) -> ((File) -> ((a, File)))) -> ((a) -> ((Expr) -> ((a, Expr))))
  sem smapAccumL_Expr_File f acc =
  | x ->
    (acc, x)

  sem smap_Expr_File : ((File) -> (File)) -> ((Expr) -> (Expr))
  sem smap_Expr_File f =
  | x ->
    (smapAccumL_Expr_File
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Expr_File : ((a) -> ((File) -> (a))) -> ((a) -> ((Expr) -> (a)))
  sem sfold_Expr_File f acc =
  | x ->
    (smapAccumL_Expr_File
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Expr_Decl : ((a) -> ((Decl) -> ((a, Decl)))) -> ((a) -> ((Expr) -> ((a, Expr))))
  sem smapAccumL_Expr_Decl f acc =
  | x ->
    (acc, x)

  sem smap_Expr_Decl : ((Decl) -> (Decl)) -> ((Expr) -> (Expr))
  sem smap_Expr_Decl f =
  | x ->
    (smapAccumL_Expr_Decl
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Expr_Decl : ((a) -> ((Decl) -> (a))) -> ((a) -> ((Expr) -> (a)))
  sem sfold_Expr_Decl f acc =
  | x ->
    (smapAccumL_Expr_Decl
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Expr_Regex : ((a) -> ((Regex) -> ((a, Regex)))) -> ((a) -> ((Expr) -> ((a, Expr))))
  sem smapAccumL_Expr_Regex f acc =
  | x ->
    (acc, x)

  sem smap_Expr_Regex : ((Regex) -> (Regex)) -> ((Expr) -> (Expr))
  sem smap_Expr_Regex f =
  | x ->
    (smapAccumL_Expr_Regex
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Expr_Regex : ((a) -> ((Regex) -> (a))) -> ((a) -> ((Expr) -> (a)))
  sem sfold_Expr_Regex f acc =
  | x ->
    (smapAccumL_Expr_Regex
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem smapAccumL_Expr_Expr : ((a) -> ((Expr) -> ((a, Expr)))) -> ((a) -> ((Expr) -> ((a, Expr))))
  sem smapAccumL_Expr_Expr f acc =
  | x ->
    (acc, x)

  sem smap_Expr_Expr : ((Expr) -> (Expr)) -> ((Expr) -> (Expr))
  sem smap_Expr_Expr f =
  | x ->
    (smapAccumL_Expr_Expr
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).#label"1"

  sem sfold_Expr_Expr : ((a) -> ((Expr) -> (a))) -> ((a) -> ((Expr) -> (a)))
  sem sfold_Expr_Expr f acc =
  | x ->
    (smapAccumL_Expr_Expr
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).#label"0"

  sem get_File_info : (File) -> (Info)

  sem set_File_info : (Info) -> ((File) -> (File))

  sem mapAccum_File_info : ((a) -> ((Info) -> ((a, Info)))) -> ((a) -> ((File) -> ((a, File))))
  sem mapAccum_File_info f acc =
  | target ->
    match
      f
        acc
        (get_File_info
           target)
    with
      (acc, val)
    then
      (acc, set_File_info
        val
        target)
    else
      never

  sem map_File_info : ((Info) -> (Info)) -> ((File) -> (File))
  sem map_File_info f =
  | target ->
    set_File_info
      (f
         (get_File_info
            target))
      target

  sem get_Decl_info : (Decl) -> (Info)

  sem set_Decl_info : (Info) -> ((Decl) -> (Decl))

  sem mapAccum_Decl_info : ((a) -> ((Info) -> ((a, Info)))) -> ((a) -> ((Decl) -> ((a, Decl))))
  sem mapAccum_Decl_info f acc =
  | target ->
    match
      f
        acc
        (get_Decl_info
           target)
    with
      (acc, val)
    then
      (acc, set_Decl_info
        val
        target)
    else
      never

  sem map_Decl_info : ((Info) -> (Info)) -> ((Decl) -> (Decl))
  sem map_Decl_info f =
  | target ->
    set_Decl_info
      (f
         (get_Decl_info
            target))
      target

  sem get_Regex_info : (Regex) -> (Info)

  sem set_Regex_info : (Info) -> ((Regex) -> (Regex))

  sem mapAccum_Regex_info : ((a) -> ((Info) -> ((a, Info)))) -> ((a) -> ((Regex) -> ((a, Regex))))
  sem mapAccum_Regex_info f acc =
  | target ->
    match
      f
        acc
        (get_Regex_info
           target)
    with
      (acc, val)
    then
      (acc, set_Regex_info
        val
        target)
    else
      never

  sem map_Regex_info : ((Info) -> (Info)) -> ((Regex) -> (Regex))
  sem map_Regex_info f =
  | target ->
    set_Regex_info
      (f
         (get_Regex_info
            target))
      target

  sem get_Expr_info : (Expr) -> (Info)

  sem set_Expr_info : (Info) -> ((Expr) -> (Expr))

  sem mapAccum_Expr_info : ((a) -> ((Info) -> ((a, Info)))) -> ((a) -> ((Expr) -> ((a, Expr))))
  sem mapAccum_Expr_info f acc =
  | target ->
    match
      f
        acc
        (get_Expr_info
           target)
    with
      (acc, val)
    then
      (acc, set_Expr_info
        val
        target)
    else
      never

  sem map_Expr_info : ((Info) -> (Info)) -> ((Expr) -> (Expr))
  sem map_Expr_info f =
  | target ->
    set_Expr_info
      (f
         (get_Expr_info
            target))
      target

end

lang FileAst = SelfhostBaseAst
  type FileRecord = {decls: [Decl], info: Info}

  syn File =
  | File FileRecord

  sem smapAccumL_File_Decl f acc =
  | File x ->
    match
      match
        let decls =
          x.decls
        in
        mapAccumL
          (lam acc1.
             lam x1: Decl.
               f
                 acc1
                 x1)
          acc
          decls
      with
        (acc, decls)
      then
        (acc, { x
          with
          decls =
            decls })
      else
        never
    with
      (acc, x)
    then
      (acc, File
        x)
    else
      never

  sem get_File_info =
  | File target ->
    target.info

  sem set_File_info val =
  | File target ->
    File
      { target
        with
        info =
          val }

end

lang StartDeclAst = SelfhostBaseAst
  type StartDeclRecord = {info: Info, name: {v: Name, i: Info}}

  syn Decl =
  | StartDecl StartDeclRecord

  sem get_Decl_info =
  | StartDecl target ->
    target.info

  sem set_Decl_info val =
  | StartDecl target ->
    StartDecl
      { target
        with
        info =
          val }

end

lang TypeDeclAst = SelfhostBaseAst
  type TypeDeclRecord = {info: Info, name: {v: Name, i: Info}, properties: [{val: Expr, name: {v: Name, i: Info}}]}

  syn Decl =
  | TypeDecl TypeDeclRecord

  sem smapAccumL_Decl_Expr f acc =
  | TypeDecl x ->
    match
      match
        let properties =
          x.properties
        in
        mapAccumL
          (lam acc1.
             lam x1: {val: Expr, name: {v: Name, i: Info}}.
               match
                 let val =
                   x1.val
                 in
                 f
                   acc1
                   val
               with
                 (acc1, val)
               then
                 (acc1, { x1
                   with
                   val =
                     val })
               else
                 never)
          acc
          properties
      with
        (acc, properties)
      then
        (acc, { x
          with
          properties =
            properties })
      else
        never
    with
      (acc, x)
    then
      (acc, TypeDecl
        x)
    else
      never

  sem get_Decl_info =
  | TypeDecl target ->
    target.info

  sem set_Decl_info val =
  | TypeDecl target ->
    TypeDecl
      { target
        with
        info =
          val }

end

lang TokenDeclAst = SelfhostBaseAst
  type TokenDeclRecord = {info: Info, name: (Option) ({v: Name, i: Info}), properties: [{val: Expr, name: {v: Name, i: Info}}]}

  syn Decl =
  | TokenDecl TokenDeclRecord

  sem smapAccumL_Decl_Expr f acc =
  | TokenDecl x ->
    match
      match
        let properties =
          x.properties
        in
        mapAccumL
          (lam acc1.
             lam x1: {val: Expr, name: {v: Name, i: Info}}.
               match
                 let val =
                   x1.val
                 in
                 f
                   acc1
                   val
               with
                 (acc1, val)
               then
                 (acc1, { x1
                   with
                   val =
                     val })
               else
                 never)
          acc
          properties
      with
        (acc, properties)
      then
        (acc, { x
          with
          properties =
            properties })
      else
        never
    with
      (acc, x)
    then
      (acc, TokenDecl
        x)
    else
      never

  sem get_Decl_info =
  | TokenDecl target ->
    target.info

  sem set_Decl_info val =
  | TokenDecl target ->
    TokenDecl
      { target
        with
        info =
          val }

end

lang PrecedenceTableDeclAst = SelfhostBaseAst
  type PrecedenceTableDeclRecord = {info: Info, levels: [{noeq: (Option) (Info), operators: [{v: Name, i: Info}]}], exceptions: [{lefts: [{v: Name, i: Info}], rights: [{v: Name, i: Info}]}]}

  syn Decl =
  | PrecedenceTableDecl PrecedenceTableDeclRecord

  sem get_Decl_info =
  | PrecedenceTableDecl target ->
    target.info

  sem set_Decl_info val =
  | PrecedenceTableDecl target ->
    PrecedenceTableDecl
      { target
        with
        info =
          val }

end

lang ProductionDeclAst = SelfhostBaseAst
  type ProductionDeclRecord = {nt: {v: Name, i: Info}, info: Info, name: {v: Name, i: Info}, kinf: (Option) (Info), kpref: (Option) (Info), kprod: (Option) (Info), kpostf: (Option) (Info), assoc: (Option) ({v: String, i: Info}), regex: Regex}

  syn Decl =
  | ProductionDecl ProductionDeclRecord

  sem smapAccumL_Decl_Regex f acc =
  | ProductionDecl x ->
    match
      match
        let regex =
          x.regex
        in
        f
          acc
          regex
      with
        (acc, regex)
      then
        (acc, { x
          with
          regex =
            regex })
      else
        never
    with
      (acc, x)
    then
      (acc, ProductionDecl
        x)
    else
      never

  sem get_Decl_info =
  | ProductionDecl target ->
    target.info

  sem set_Decl_info val =
  | ProductionDecl target ->
    ProductionDecl
      { target
        with
        info =
          val }

end

lang RecordRegexAst = SelfhostBaseAst
  type RecordRegexRecord = {info: Info, regex: Regex}

  syn Regex =
  | RecordRegex RecordRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | RecordRegex x ->
    match
      match
        let regex =
          x.regex
        in
        f
          acc
          regex
      with
        (acc, regex)
      then
        (acc, { x
          with
          regex =
            regex })
      else
        never
    with
      (acc, x)
    then
      (acc, RecordRegex
        x)
    else
      never

  sem get_Regex_info =
  | RecordRegex target ->
    target.info

  sem set_Regex_info val =
  | RecordRegex target ->
    RecordRegex
      { target
        with
        info =
          val }

end

lang EmptyRegexAst = SelfhostBaseAst
  type EmptyRegexRecord = {info: Info}

  syn Regex =
  | EmptyRegex EmptyRegexRecord

  sem get_Regex_info =
  | EmptyRegex target ->
    target.info

  sem set_Regex_info val =
  | EmptyRegex target ->
    EmptyRegex
      { target
        with
        info =
          val }

end

lang LiteralRegexAst = SelfhostBaseAst
  type LiteralRegexRecord = {info: Info, val: {v: String, i: Info}}

  syn Regex =
  | LiteralRegex LiteralRegexRecord

  sem get_Regex_info =
  | LiteralRegex target ->
    target.info

  sem set_Regex_info val =
  | LiteralRegex target ->
    LiteralRegex
      { target
        with
        info =
          val }

end

lang TokenRegexAst = SelfhostBaseAst
  type TokenRegexRecord = {info: Info, name: {v: Name, i: Info}, arg: (Option) (Expr)}

  syn Regex =
  | TokenRegex TokenRegexRecord

  sem smapAccumL_Regex_Expr f acc =
  | TokenRegex x ->
    match
      match
        let arg =
          x.arg
        in
        optionMapAccum
          (lam acc1.
             lam x1.
               f
                 acc1
                 x1)
          acc
          arg
      with
        (acc, arg)
      then
        (acc, { x
          with
          arg =
            arg })
      else
        never
    with
      (acc, x)
    then
      (acc, TokenRegex
        x)
    else
      never

  sem get_Regex_info =
  | TokenRegex target ->
    target.info

  sem set_Regex_info val =
  | TokenRegex target ->
    TokenRegex
      { target
        with
        info =
          val }

end

lang RepeatPlusRegexAst = SelfhostBaseAst
  type RepeatPlusRegexRecord = {info: Info, left: Regex}

  syn Regex =
  | RepeatPlusRegex RepeatPlusRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | RepeatPlusRegex x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      then
        (acc, { x
          with
          left =
            left })
      else
        never
    with
      (acc, x)
    then
      (acc, RepeatPlusRegex
        x)
    else
      never

  sem get_Regex_info =
  | RepeatPlusRegex target ->
    target.info

  sem set_Regex_info val =
  | RepeatPlusRegex target ->
    RepeatPlusRegex
      { target
        with
        info =
          val }

end

lang RepeatStarRegexAst = SelfhostBaseAst
  type RepeatStarRegexRecord = {info: Info, left: Regex}

  syn Regex =
  | RepeatStarRegex RepeatStarRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | RepeatStarRegex x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      then
        (acc, { x
          with
          left =
            left })
      else
        never
    with
      (acc, x)
    then
      (acc, RepeatStarRegex
        x)
    else
      never

  sem get_Regex_info =
  | RepeatStarRegex target ->
    target.info

  sem set_Regex_info val =
  | RepeatStarRegex target ->
    RepeatStarRegex
      { target
        with
        info =
          val }

end

lang RepeatQuestionRegexAst = SelfhostBaseAst
  type RepeatQuestionRegexRecord = {info: Info, left: Regex}

  syn Regex =
  | RepeatQuestionRegex RepeatQuestionRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | RepeatQuestionRegex x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      then
        (acc, { x
          with
          left =
            left })
      else
        never
    with
      (acc, x)
    then
      (acc, RepeatQuestionRegex
        x)
    else
      never

  sem get_Regex_info =
  | RepeatQuestionRegex target ->
    target.info

  sem set_Regex_info val =
  | RepeatQuestionRegex target ->
    RepeatQuestionRegex
      { target
        with
        info =
          val }

end

lang NamedRegexAst = SelfhostBaseAst
  type NamedRegexRecord = {info: Info, name: {v: String, i: Info}, right: Regex}

  syn Regex =
  | NamedRegex NamedRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | NamedRegex x ->
    match
      match
        let right =
          x.right
        in
        f
          acc
          right
      with
        (acc, right)
      then
        (acc, { x
          with
          right =
            right })
      else
        never
    with
      (acc, x)
    then
      (acc, NamedRegex
        x)
    else
      never

  sem get_Regex_info =
  | NamedRegex target ->
    target.info

  sem set_Regex_info val =
  | NamedRegex target ->
    NamedRegex
      { target
        with
        info =
          val }

end

lang AlternativeRegexAst = SelfhostBaseAst
  type AlternativeRegexRecord = {info: Info, left: Regex, right: Regex}

  syn Regex =
  | AlternativeRegex AlternativeRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | AlternativeRegex x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      then
        match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        then
          (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
        else
          never
      else
        never
    with
      (acc, x)
    then
      (acc, AlternativeRegex
        x)
    else
      never

  sem get_Regex_info =
  | AlternativeRegex target ->
    target.info

  sem set_Regex_info val =
  | AlternativeRegex target ->
    AlternativeRegex
      { target
        with
        info =
          val }

end

lang ConcatRegexAst = SelfhostBaseAst
  type ConcatRegexRecord = {info: Info, left: Regex, right: Regex}

  syn Regex =
  | ConcatRegex ConcatRegexRecord

  sem smapAccumL_Regex_Regex f acc =
  | ConcatRegex x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      then
        match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        then
          (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
        else
          never
      else
        never
    with
      (acc, x)
    then
      (acc, ConcatRegex
        x)
    else
      never

  sem get_Regex_info =
  | ConcatRegex target ->
    target.info

  sem set_Regex_info val =
  | ConcatRegex target ->
    ConcatRegex
      { target
        with
        info =
          val }

end

lang AppExprAst = SelfhostBaseAst
  type AppExprRecord = {info: Info, left: Expr, right: Expr}

  syn Expr =
  | AppExpr AppExprRecord

  sem smapAccumL_Expr_Expr f acc =
  | AppExpr x ->
    match
      match
        let left =
          x.left
        in
        f
          acc
          left
      with
        (acc, left)
      then
        match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        then
          (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
        else
          never
      else
        never
    with
      (acc, x)
    then
      (acc, AppExpr
        x)
    else
      never

  sem get_Expr_info =
  | AppExpr target ->
    target.info

  sem set_Expr_info val =
  | AppExpr target ->
    AppExpr
      { target
        with
        info =
          val }

end

lang ConExprAst = SelfhostBaseAst
  type ConExprRecord = {info: Info, name: {v: Name, i: Info}}

  syn Expr =
  | ConExpr ConExprRecord

  sem get_Expr_info =
  | ConExpr target ->
    target.info

  sem set_Expr_info val =
  | ConExpr target ->
    ConExpr
      { target
        with
        info =
          val }

end

lang StringExprAst = SelfhostBaseAst
  type StringExprRecord = {info: Info, val: {v: String, i: Info}}

  syn Expr =
  | StringExpr StringExprRecord

  sem get_Expr_info =
  | StringExpr target ->
    target.info

  sem set_Expr_info val =
  | StringExpr target ->
    StringExpr
      { target
        with
        info =
          val }

end

lang VariableExprAst = SelfhostBaseAst
  type VariableExprRecord = {info: Info, name: {v: Name, i: Info}}

  syn Expr =
  | VariableExpr VariableExprRecord

  sem get_Expr_info =
  | VariableExpr target ->
    target.info

  sem set_Expr_info val =
  | VariableExpr target ->
    VariableExpr
      { target
        with
        info =
          val }

end

lang RecordExprAst = SelfhostBaseAst
  type RecordExprRecord = {info: Info, fields: [{val: Expr, name: {v: String, i: Info}}]}

  syn Expr =
  | RecordExpr RecordExprRecord

  sem smapAccumL_Expr_Expr f acc =
  | RecordExpr x ->
    match
      match
        let fields =
          x.fields
        in
        mapAccumL
          (lam acc1.
             lam x1: {val: Expr, name: {v: String, i: Info}}.
               match
                 let val =
                   x1.val
                 in
                 f
                   acc1
                   val
               with
                 (acc1, val)
               then
                 (acc1, { x1
                   with
                   val =
                     val })
               else
                 never)
          acc
          fields
      with
        (acc, fields)
      then
        (acc, { x
          with
          fields =
            fields })
      else
        never
    with
      (acc, x)
    then
      (acc, RecordExpr
        x)
    else
      never

  sem get_Expr_info =
  | RecordExpr target ->
    target.info

  sem set_Expr_info val =
  | RecordExpr target ->
    RecordExpr
      { target
        with
        info =
          val }

end

lang BadFileAst = SelfhostBaseAst
  type BadFileRecord = {info: Info}

  syn File =
  | BadFile BadFileRecord

  sem get_File_info =
  | BadFile target ->
    target.info

  sem set_File_info val =
  | BadFile target ->
    BadFile
      { target
        with
        info =
          val }

end

lang BadDeclAst = SelfhostBaseAst
  type BadDeclRecord = {info: Info}

  syn Decl =
  | BadDecl BadDeclRecord

  sem get_Decl_info =
  | BadDecl target ->
    target.info

  sem set_Decl_info val =
  | BadDecl target ->
    BadDecl
      { target
        with
        info =
          val }

end

lang BadRegexAst = SelfhostBaseAst
  type BadRegexRecord = {info: Info}

  syn Regex =
  | BadRegex BadRegexRecord

  sem get_Regex_info =
  | BadRegex target ->
    target.info

  sem set_Regex_info val =
  | BadRegex target ->
    BadRegex
      { target
        with
        info =
          val }

end

lang BadExprAst = SelfhostBaseAst
  type BadExprRecord = {info: Info}

  syn Expr =
  | BadExpr BadExprRecord

  sem get_Expr_info =
  | BadExpr target ->
    target.info

  sem set_Expr_info val =
  | BadExpr target ->
    BadExpr
      { target
        with
        info =
          val }

end

lang SelfhostAst = FileAst + StartDeclAst + TypeDeclAst + TokenDeclAst + PrecedenceTableDeclAst + ProductionDeclAst + RecordRegexAst + EmptyRegexAst + LiteralRegexAst + TokenRegexAst + RepeatPlusRegexAst + RepeatStarRegexAst + RepeatQuestionRegexAst + NamedRegexAst + AlternativeRegexAst + ConcatRegexAst + AppExprAst + ConExprAst + StringExprAst + VariableExprAst + RecordExprAst + BadFileAst + BadDeclAst + BadRegexAst + BadExprAst



end

lang FileOpBase = SelfhostBaseAst

  syn FileOp =

  sem topAllowed_FileOp : (FileOp) -> (Bool)
  sem topAllowed_FileOp =
  | _ ->
    true

  sem leftAllowed_FileOp : ({parent: FileOp, child: FileOp}) -> (Bool)
  sem leftAllowed_FileOp =
  | _ ->
    true

  sem rightAllowed_FileOp : ({parent: FileOp, child: FileOp}) -> (Bool)
  sem rightAllowed_FileOp =
  | _ ->
    true

  sem groupingsAllowed_FileOp : (FileOp) -> (AllowedDirection)
  sem groupingsAllowed_FileOp =
  | _ ->
    GEither
      {}

  sem parenAllowed_FileOp : (FileOp) -> (AllowedDirection)
  sem parenAllowed_FileOp =
  | _ ->
    GEither
      {}

  sem get_FileOp_info : (FileOp) -> (Info)

  sem get_FileOp_terms : (FileOp) -> ([Info])

  sem unsplit_FileOp : ((PermanentNode) (FileOp)) -> ((Info, File))

end

lang DeclOpBase = SelfhostBaseAst

  syn DeclOp =

  sem topAllowed_DeclOp : (DeclOp) -> (Bool)
  sem topAllowed_DeclOp =
  | _ ->
    true

  sem leftAllowed_DeclOp : ({parent: DeclOp, child: DeclOp}) -> (Bool)
  sem leftAllowed_DeclOp =
  | _ ->
    true

  sem rightAllowed_DeclOp : ({parent: DeclOp, child: DeclOp}) -> (Bool)
  sem rightAllowed_DeclOp =
  | _ ->
    true

  sem groupingsAllowed_DeclOp : (DeclOp) -> (AllowedDirection)
  sem groupingsAllowed_DeclOp =
  | _ ->
    GEither
      {}

  sem parenAllowed_DeclOp : (DeclOp) -> (AllowedDirection)
  sem parenAllowed_DeclOp =
  | _ ->
    GEither
      {}

  sem get_DeclOp_info : (DeclOp) -> (Info)

  sem get_DeclOp_terms : (DeclOp) -> ([Info])

  sem unsplit_DeclOp : ((PermanentNode) (DeclOp)) -> ((Info, Decl))

end

lang RegexOpBase = SelfhostBaseAst

  syn RegexOp =

  sem topAllowed_RegexOp : (RegexOp) -> (Bool)
  sem topAllowed_RegexOp =
  | _ ->
    true

  sem leftAllowed_RegexOp : ({parent: RegexOp, child: RegexOp}) -> (Bool)
  sem leftAllowed_RegexOp =
  | _ ->
    true

  sem rightAllowed_RegexOp : ({parent: RegexOp, child: RegexOp}) -> (Bool)
  sem rightAllowed_RegexOp =
  | _ ->
    true

  sem groupingsAllowed_RegexOp : (RegexOp) -> (AllowedDirection)
  sem groupingsAllowed_RegexOp =
  | _ ->
    GEither
      {}

  sem parenAllowed_RegexOp : (RegexOp) -> (AllowedDirection)
  sem parenAllowed_RegexOp =
  | _ ->
    GEither
      {}

  sem get_RegexOp_info : (RegexOp) -> (Info)

  sem get_RegexOp_terms : (RegexOp) -> ([Info])

  sem unsplit_RegexOp : ((PermanentNode) (RegexOp)) -> ((Info, Regex))

end

lang ExprOpBase = SelfhostBaseAst

  syn ExprOp =

  sem topAllowed_ExprOp : (ExprOp) -> (Bool)
  sem topAllowed_ExprOp =
  | _ ->
    true

  sem leftAllowed_ExprOp : ({parent: ExprOp, child: ExprOp}) -> (Bool)
  sem leftAllowed_ExprOp =
  | _ ->
    true

  sem rightAllowed_ExprOp : ({parent: ExprOp, child: ExprOp}) -> (Bool)
  sem rightAllowed_ExprOp =
  | _ ->
    true

  sem groupingsAllowed_ExprOp : (ExprOp) -> (AllowedDirection)
  sem groupingsAllowed_ExprOp =
  | _ ->
    GEither
      {}

  sem parenAllowed_ExprOp : (ExprOp) -> (AllowedDirection)
  sem parenAllowed_ExprOp =
  | _ ->
    GEither
      {}

  sem get_ExprOp_info : (ExprOp) -> (Info)

  sem get_ExprOp_terms : (ExprOp) -> ([Info])

  sem unsplit_ExprOp : ((PermanentNode) (ExprOp)) -> ((Info, Expr))

end

lang FileOp = FileOpBase + FileAst

  syn FileOp =
  | FileOp {__br_terms: [Info], decls: [Decl], __br_info: Info}

  sem get_FileOp_info =
  | FileOp x ->
    x.__br_info

  sem get_FileOp_terms =
  | FileOp x ->
    x.__br_terms

  sem unsplit_FileOp =
  | AtomP {self = FileOp x} ->
    (x.__br_info, File
      { decls =
          x.decls,
        info =
          x.__br_info })

end

lang StartDeclOp = DeclOpBase + StartDeclAst

  syn DeclOp =
  | StartDeclOp {__br_terms: [Info], __br_info: Info, name: [{v: Name, i: Info}]}

  sem get_DeclOp_info =
  | StartDeclOp x ->
    x.__br_info

  sem get_DeclOp_terms =
  | StartDeclOp x ->
    x.__br_terms

  sem unsplit_DeclOp =
  | AtomP {self = StartDeclOp x} ->
    (x.__br_info, StartDecl
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang TypeDeclOp = DeclOpBase + TypeDeclAst

  syn DeclOp =
  | TypeDeclOp {__br_terms: [Info], __br_info: Info, name: [{v: Name, i: Info}], properties: [{val: Expr, name: {v: Name, i: Info}}]}

  sem get_DeclOp_info =
  | TypeDeclOp x ->
    x.__br_info

  sem get_DeclOp_terms =
  | TypeDeclOp x ->
    x.__br_terms

  sem unsplit_DeclOp =
  | AtomP {self = TypeDeclOp x} ->
    (x.__br_info, TypeDecl
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never,
        properties =
          x.properties })

end

lang TokenDeclOp = DeclOpBase + TokenDeclAst

  syn DeclOp =
  | TokenDeclOp {__br_terms: [Info], __br_info: Info, name: [{v: Name, i: Info}], properties: [{val: Expr, name: {v: Name, i: Info}}]}

  sem get_DeclOp_info =
  | TokenDeclOp x ->
    x.__br_info

  sem get_DeclOp_terms =
  | TokenDeclOp x ->
    x.__br_terms

  sem unsplit_DeclOp =
  | AtomP {self = TokenDeclOp x} ->
    (x.__br_info, TokenDecl
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            Some
              x1
          else
            None
              {},
        properties =
          x.properties })

end

lang PrecedenceTableDeclOp = DeclOpBase + PrecedenceTableDeclAst

  syn DeclOp =
  | PrecedenceTableDeclOp {__br_terms: [Info], __br_info: Info, levels: [{noeq: (Option) (Info), operators: [{v: Name, i: Info}]}], exceptions: [{lefts: [{v: Name, i: Info}], rights: [{v: Name, i: Info}]}]}

  sem get_DeclOp_info =
  | PrecedenceTableDeclOp x ->
    x.__br_info

  sem get_DeclOp_terms =
  | PrecedenceTableDeclOp x ->
    x.__br_terms

  sem unsplit_DeclOp =
  | AtomP {self = PrecedenceTableDeclOp x} ->
    (x.__br_info, PrecedenceTableDecl
      { info =
          x.__br_info,
        levels =
          x.levels,
        exceptions =
          x.exceptions })

end

lang ProductionDeclOp = DeclOpBase + ProductionDeclAst

  syn DeclOp =
  | ProductionDeclOp {__br_terms: [Info], __br_info: Info, nt: [{v: Name, i: Info}], name: [{v: Name, i: Info}], kinf: [Info], kpref: [Info], kprod: [Info], kpostf: [Info], assoc: [{v: String, i: Info}], regex: [Regex]}

  sem get_DeclOp_info =
  | ProductionDeclOp x ->
    x.__br_info

  sem get_DeclOp_terms =
  | ProductionDeclOp x ->
    x.__br_terms

  sem unsplit_DeclOp =
  | AtomP {self = ProductionDeclOp x} ->
    (x.__br_info, ProductionDecl
      { nt =
          match
            x.nt
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never,
        info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x2 ] ++ _ ++ ""
          then
            x2
          else
            never,
        kinf =
          match
            x.kinf
          with
            [ x3 ] ++ _ ++ ""
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
            [ x4 ] ++ _ ++ ""
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
            [ x5 ] ++ _ ++ ""
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
            [ x6 ] ++ _ ++ ""
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
            [ x7 ] ++ _ ++ ""
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
            [ x8 ] ++ _ ++ ""
          then
            x8
          else
            never })

end

lang RecordRegexOp = RegexOpBase + RecordRegexAst

  syn RegexOp =
  | RecordRegexOp {__br_terms: [Info], __br_info: Info, regex: [Regex]}

  sem get_RegexOp_info =
  | RecordRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | RecordRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | AtomP {self = RecordRegexOp x} ->
    (x.__br_info, RecordRegex
      { info =
          x.__br_info,
        regex =
          match
            x.regex
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang EmptyRegexOp = RegexOpBase + EmptyRegexAst

  syn RegexOp =
  | EmptyRegexOp {__br_terms: [Info], __br_info: Info}

  sem get_RegexOp_info =
  | EmptyRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | EmptyRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | AtomP {self = EmptyRegexOp x} ->
    (x.__br_info, EmptyRegex
      { info =
          x.__br_info })

end

lang LiteralRegexOp = RegexOpBase + LiteralRegexAst

  syn RegexOp =
  | LiteralRegexOp {__br_terms: [Info], __br_info: Info, val: [{v: String, i: Info}]}

  sem get_RegexOp_info =
  | LiteralRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | LiteralRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | AtomP {self = LiteralRegexOp x} ->
    (x.__br_info, LiteralRegex
      { info =
          x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang TokenRegexOp = RegexOpBase + TokenRegexAst

  syn RegexOp =
  | TokenRegexOp {__br_terms: [Info], __br_info: Info, name: [{v: Name, i: Info}], arg: [Expr]}

  sem get_RegexOp_info =
  | TokenRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | TokenRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | AtomP {self = TokenRegexOp x} ->
    (x.__br_info, TokenRegex
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never,
        arg =
          match
            x.arg
          with
            [ x2 ] ++ _ ++ ""
          then
            Some
              x2
          else
            None
              {} })

end

lang RepeatPlusRegexOp = RegexOpBase + RepeatPlusRegexAst

  syn RegexOp =
  | RepeatPlusRegexOp {__br_terms: [Info], __br_info: Info}

  sem get_RegexOp_info =
  | RepeatPlusRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | RepeatPlusRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | PostfixP {self = RepeatPlusRegexOp x, leftChildAlts = [ l ] ++ _ ++ ""} ->
    match
      unsplit_RegexOp
        l
    with
      (linfo, l)
    then
      let info =
        mergeInfo
          linfo
          (x.__br_info)
      in
      (info, RepeatPlusRegex
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never })
    else
      never

end

lang RepeatStarRegexOp = RegexOpBase + RepeatStarRegexAst

  syn RegexOp =
  | RepeatStarRegexOp {__br_terms: [Info], __br_info: Info}

  sem get_RegexOp_info =
  | RepeatStarRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | RepeatStarRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | PostfixP {self = RepeatStarRegexOp x, leftChildAlts = [ l ] ++ _ ++ ""} ->
    match
      unsplit_RegexOp
        l
    with
      (linfo, l)
    then
      let info =
        mergeInfo
          linfo
          (x.__br_info)
      in
      (info, RepeatStarRegex
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never })
    else
      never

end

lang RepeatQuestionRegexOp = RegexOpBase + RepeatQuestionRegexAst

  syn RegexOp =
  | RepeatQuestionRegexOp {__br_terms: [Info], __br_info: Info}

  sem get_RegexOp_info =
  | RepeatQuestionRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | RepeatQuestionRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | PostfixP {self = RepeatQuestionRegexOp x, leftChildAlts = [ l ] ++ _ ++ ""} ->
    match
      unsplit_RegexOp
        l
    with
      (linfo, l)
    then
      let info =
        mergeInfo
          linfo
          (x.__br_info)
      in
      (info, RepeatQuestionRegex
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never })
    else
      never

end

lang NamedRegexOp = RegexOpBase + NamedRegexAst

  syn RegexOp =
  | NamedRegexOp {__br_terms: [Info], __br_info: Info, name: [{v: String, i: Info}]}

  sem get_RegexOp_info =
  | NamedRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | NamedRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | PrefixP {self = NamedRegexOp x, rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      unsplit_RegexOp
        r
    with
      (rinfo, r)
    then
      let info =
        mergeInfo
          (x.__br_info)
          rinfo
      in
      (info, NamedRegex
        { info =
            info,
          name =
            match
              x.name
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            then
              x2
            else
              never })
    else
      never

end

lang AlternativeRegexOp = RegexOpBase + AlternativeRegexAst

  syn RegexOp =
  | AlternativeRegexOp {__br_terms: [Info], __br_info: Info}

  sem get_RegexOp_info =
  | AlternativeRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | AlternativeRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | InfixP {self = AlternativeRegexOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_RegexOp
        l, unsplit_RegexOp
        r)
    with
      ((linfo, l), (rinfo, r))
    then
      let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, AlternativeRegex
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            then
              x2
            else
              never })
    else
      never

end

lang ConcatRegexOp = RegexOpBase + ConcatRegexAst

  syn RegexOp =
  | ConcatRegexOp {__br_terms: [Info], __br_info: Info}

  sem get_RegexOp_info =
  | ConcatRegexOp x ->
    x.__br_info

  sem get_RegexOp_terms =
  | ConcatRegexOp x ->
    x.__br_terms

  sem unsplit_RegexOp =
  | InfixP {self = ConcatRegexOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_RegexOp
        l, unsplit_RegexOp
        r)
    with
      ((linfo, l), (rinfo, r))
    then
      let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, ConcatRegex
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            then
              x2
            else
              never })
    else
      never

end

lang AppExprOp = ExprOpBase + AppExprAst

  syn ExprOp =
  | AppExprOp {__br_terms: [Info], __br_info: Info}

  sem get_ExprOp_info =
  | AppExprOp x ->
    x.__br_info

  sem get_ExprOp_terms =
  | AppExprOp x ->
    x.__br_terms

  sem unsplit_ExprOp =
  | InfixP {self = AppExprOp x, leftChildAlts = [ l ] ++ _ ++ "", rightChildAlts = [ r ] ++ _ ++ ""} ->
    match
      (unsplit_ExprOp
        l, unsplit_ExprOp
        r)
    with
      ((linfo, l), (rinfo, r))
    then
      let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, AppExpr
        { info =
            info,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _ ++ ""
            then
              x1
            else
              never,
          right =
            match
              [ r ]
            with
              [ x2 ] ++ _ ++ ""
            then
              x2
            else
              never })
    else
      never

end

lang ConExprOp = ExprOpBase + ConExprAst

  syn ExprOp =
  | ConExprOp {__br_terms: [Info], __br_info: Info, name: [{v: Name, i: Info}]}

  sem get_ExprOp_info =
  | ConExprOp x ->
    x.__br_info

  sem get_ExprOp_terms =
  | ConExprOp x ->
    x.__br_terms

  sem unsplit_ExprOp =
  | AtomP {self = ConExprOp x} ->
    (x.__br_info, ConExpr
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang StringExprOp = ExprOpBase + StringExprAst

  syn ExprOp =
  | StringExprOp {__br_terms: [Info], __br_info: Info, val: [{v: String, i: Info}]}

  sem get_ExprOp_info =
  | StringExprOp x ->
    x.__br_info

  sem get_ExprOp_terms =
  | StringExprOp x ->
    x.__br_terms

  sem unsplit_ExprOp =
  | AtomP {self = StringExprOp x} ->
    (x.__br_info, StringExpr
      { info =
          x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang VariableExprOp = ExprOpBase + VariableExprAst

  syn ExprOp =
  | VariableExprOp {__br_terms: [Info], __br_info: Info, name: [{v: Name, i: Info}]}

  sem get_ExprOp_info =
  | VariableExprOp x ->
    x.__br_info

  sem get_ExprOp_terms =
  | VariableExprOp x ->
    x.__br_terms

  sem unsplit_ExprOp =
  | AtomP {self = VariableExprOp x} ->
    (x.__br_info, VariableExpr
      { info =
          x.__br_info,
        name =
          match
            x.name
          with
            [ x1 ] ++ _ ++ ""
          then
            x1
          else
            never })

end

lang RecordExprOp = ExprOpBase + RecordExprAst

  syn ExprOp =
  | RecordExprOp {__br_terms: [Info], __br_info: Info, fields: [{val: Expr, name: {v: String, i: Info}}]}

  sem get_ExprOp_info =
  | RecordExprOp x ->
    x.__br_info

  sem get_ExprOp_terms =
  | RecordExprOp x ->
    x.__br_terms

  sem unsplit_ExprOp =
  | AtomP {self = RecordExprOp x} ->
    (x.__br_info, RecordExpr
      { info =
          x.__br_info,
        fields =
          x.fields })

end

lang ParseSelfhost = FileOp + StartDeclOp + TypeDeclOp + TokenDeclOp + PrecedenceTableDeclOp + ProductionDeclOp + RecordRegexOp + EmptyRegexOp + LiteralRegexOp + TokenRegexOp + RepeatPlusRegexOp + RepeatStarRegexOp + RepeatQuestionRegexOp + NamedRegexOp + AlternativeRegexOp + ConcatRegexOp + AppExprOp + ConExprOp + StringExprOp + VariableExprOp + RecordExprOp + BadFileAst + BadDeclAst + BadRegexAst + BadExprAst + LL1Parser + UIdentTokenParser + LIdentTokenParser + StringTokenParser



end



let _table = use ParseSelfhost in let target =
  genParsingTable
    (let #var"File" =
       nameSym
         "File"
     in
     let #var"Decl" =
       nameSym
         "Decl"
     in
     let #var"Regex" =
       nameSym
         "Regex"
     in
     let #var"Expr" =
       nameSym
         "Expr"
     in
     let #var"FileAtom" =
       nameSym
         "FileAtom"
     in
     let #var"FileInfix" =
       nameSym
         "FileInfix"
     in
     let #var"FilePrefix" =
       nameSym
         "FilePrefix"
     in
     let #var"FilePostfix" =
       nameSym
         "FilePostfix"
     in
     let #var"DeclAtom" =
       nameSym
         "DeclAtom"
     in
     let #var"DeclInfix" =
       nameSym
         "DeclInfix"
     in
     let #var"DeclPrefix" =
       nameSym
         "DeclPrefix"
     in
     let #var"DeclPostfix" =
       nameSym
         "DeclPostfix"
     in
     let #var"RegexAtom" =
       nameSym
         "RegexAtom"
     in
     let #var"RegexInfix" =
       nameSym
         "RegexInfix"
     in
     let #var"RegexPrefix" =
       nameSym
         "RegexPrefix"
     in
     let #var"RegexPostfix" =
       nameSym
         "RegexPostfix"
     in
     let #var"ExprAtom" =
       nameSym
         "ExprAtom"
     in
     let #var"ExprInfix" =
       nameSym
         "ExprInfix"
     in
     let #var"ExprPrefix" =
       nameSym
         "ExprPrefix"
     in
     let #var"ExprPostfix" =
       nameSym
         "ExprPostfix"
     in
     let kleene =
       nameSym
         "kleene"
     in
     let kleene1 =
       nameSym
         "kleene"
     in
     let alt =
       nameSym
         "alt"
     in
     let alt1 =
       nameSym
         "alt"
     in
     let kleene2 =
       nameSym
         "kleene"
     in
     let alt2 =
       nameSym
         "alt"
     in
     let alt3 =
       nameSym
         "alt"
     in
     let kleene3 =
       nameSym
         "kleene"
     in
     let kleene4 =
       nameSym
         "kleene"
     in
     let kleene5 =
       nameSym
         "kleene"
     in
     let kleene6 =
       nameSym
         "kleene"
     in
     let kleene7 =
       nameSym
         "kleene"
     in
     let alt4 =
       nameSym
         "alt"
     in
     let alt5 =
       nameSym
         "alt"
     in
     let alt6 =
       nameSym
         "alt"
     in
     let alt7 =
       nameSym
         "alt"
     in
     let kleene8 =
       nameSym
         "kleene"
     in
     let alt8 =
       nameSym
         "alt"
     in
     let #var"File_lclosed" =
       nameSym
         "File_lclosed"
     in
     let #var"File_lopen" =
       nameSym
         "File_lopen"
     in
     let #var"Decl_lclosed" =
       nameSym
         "Decl_lclosed"
     in
     let #var"Decl_lopen" =
       nameSym
         "Decl_lopen"
     in
     let #var"Regex_lclosed" =
       nameSym
         "Regex_lclosed"
     in
     let #var"Regex_lopen" =
       nameSym
         "Regex_lopen"
     in
     let #var"Expr_lclosed" =
       nameSym
         "Expr_lclosed"
     in
     let #var"Expr_lopen" =
       nameSym
         "Expr_lopen"
     in
     { start =
         #var"File",
       productions =
         let config =
           { topAllowed =
               topAllowed_FileOp,
             leftAllowed =
               leftAllowed_FileOp,
             rightAllowed =
               rightAllowed_FileOp,
             parenAllowed =
               parenAllowed_FileOp,
             groupingsAllowed =
               groupingsAllowed_FileOp }
         in
         let reportConfig =
           { topAllowed =
               topAllowed_FileOp,
             parenAllowed =
               parenAllowed_FileOp,
             terminalInfos =
               get_FileOp_terms,
             getInfo =
               get_FileOp_info,
             lpar =
               "(",
             rpar =
               ")" }
         in
         let addFileOpAtom =
           lam #var"".
             lam x31.
               lam st.
                 optionMap
                   (breakableAddAtom
                      config
                      x31)
                   st
         in
         let addFileOpInfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x31.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddInfix
                       config
                       x31
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_FileOp_info
                               x31, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   st
         in
         let addFileOpPrefix =
           lam #var"".
             lam x31.
               lam st.
                 optionMap
                   (breakableAddPrefix
                      config
                      x31)
                   st
         in
         let addFileOpPostfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x31.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddPostfix
                       config
                       x31
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_FileOp_info
                               x31, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   st
         in
         let finalizeFileOp =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam st.
               let res59 =
                 optionBind
                   st
                   (lam st.
                      match
                        breakableFinalizeParse
                          config
                          st
                      with
                        Some (tops & ([ top ] ++ _ ++ ""))
                      then
                        let errs =
                          breakableDefaultHighlight
                            reportConfig
                            (p.content)
                            tops
                        in
                        let res59: (Info, File) =
                          unsplit_FileOp
                            top
                        in
                        match
                          null
                            errs
                        with
                          true
                        then
                          Some
                            res59
                        else
                          (modref
                               (p.errors)
                               (concat
                                  (deref
                                     (p.errors))
                                  errs))
                          ;Some
                            (res59.#label"0", BadFile
                              { info =
                                  res59.#label"0" })
                      else
                        (modref
                             (p.errors)
                             (snoc
                                (deref
                                   (p.errors))
                                (NoInfo
                                  {}, "Unfinished File")))
                        ;None
                          {})
               in
               optionGetOr
                 (NoInfo
                   {}, BadFile
                   { info =
                       NoInfo
                         {} })
                 res59
         in
         let config1 =
           { topAllowed =
               topAllowed_DeclOp,
             leftAllowed =
               leftAllowed_DeclOp,
             rightAllowed =
               rightAllowed_DeclOp,
             parenAllowed =
               parenAllowed_DeclOp,
             groupingsAllowed =
               groupingsAllowed_DeclOp }
         in
         let reportConfig1 =
           { topAllowed =
               topAllowed_DeclOp,
             parenAllowed =
               parenAllowed_DeclOp,
             terminalInfos =
               get_DeclOp_terms,
             getInfo =
               get_DeclOp_info,
             lpar =
               "(",
             rpar =
               ")" }
         in
         let addDeclOpAtom =
           lam #var"".
             lam x31.
               lam st.
                 optionMap
                   (breakableAddAtom
                      config1
                      x31)
                   st
         in
         let addDeclOpInfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x31.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddInfix
                       config1
                       x31
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_DeclOp_info
                               x31, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   st
         in
         let addDeclOpPrefix =
           lam #var"".
             lam x31.
               lam st.
                 optionMap
                   (breakableAddPrefix
                      config1
                      x31)
                   st
         in
         let addDeclOpPostfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x31.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddPostfix
                       config1
                       x31
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_DeclOp_info
                               x31, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   st
         in
         let finalizeDeclOp =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam st.
               let res59 =
                 optionBind
                   st
                   (lam st.
                      match
                        breakableFinalizeParse
                          config1
                          st
                      with
                        Some (tops & ([ top ] ++ _ ++ ""))
                      then
                        let errs =
                          breakableDefaultHighlight
                            reportConfig1
                            (p.content)
                            tops
                        in
                        let res59: (Info, Decl) =
                          unsplit_DeclOp
                            top
                        in
                        match
                          null
                            errs
                        with
                          true
                        then
                          Some
                            res59
                        else
                          (modref
                               (p.errors)
                               (concat
                                  (deref
                                     (p.errors))
                                  errs))
                          ;Some
                            (res59.#label"0", BadDecl
                              { info =
                                  res59.#label"0" })
                      else
                        (modref
                             (p.errors)
                             (snoc
                                (deref
                                   (p.errors))
                                (NoInfo
                                  {}, "Unfinished Decl")))
                        ;None
                          {})
               in
               optionGetOr
                 (NoInfo
                   {}, BadDecl
                   { info =
                       NoInfo
                         {} })
                 res59
         in
         let config2 =
           { topAllowed =
               topAllowed_RegexOp,
             leftAllowed =
               leftAllowed_RegexOp,
             rightAllowed =
               rightAllowed_RegexOp,
             parenAllowed =
               parenAllowed_RegexOp,
             groupingsAllowed =
               groupingsAllowed_RegexOp }
         in
         let reportConfig2 =
           { topAllowed =
               topAllowed_RegexOp,
             parenAllowed =
               parenAllowed_RegexOp,
             terminalInfos =
               get_RegexOp_terms,
             getInfo =
               get_RegexOp_info,
             lpar =
               "(",
             rpar =
               ")" }
         in
         let addRegexOpAtom =
           lam #var"".
             lam x31.
               lam st.
                 optionMap
                   (breakableAddAtom
                      config2
                      x31)
                   st
         in
         let addRegexOpInfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x31.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddInfix
                       config2
                       x31
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_RegexOp_info
                               x31, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   st
         in
         let addRegexOpPrefix =
           lam #var"".
             lam x31.
               lam st.
                 optionMap
                   (breakableAddPrefix
                      config2
                      x31)
                   st
         in
         let addRegexOpPostfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x31.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddPostfix
                       config2
                       x31
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_RegexOp_info
                               x31, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   st
         in
         let finalizeRegexOp =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam st.
               let res59 =
                 optionBind
                   st
                   (lam st.
                      match
                        breakableFinalizeParse
                          config2
                          st
                      with
                        Some (tops & ([ top ] ++ _ ++ ""))
                      then
                        let errs =
                          breakableDefaultHighlight
                            reportConfig2
                            (p.content)
                            tops
                        in
                        let res59: (Info, Regex) =
                          unsplit_RegexOp
                            top
                        in
                        match
                          null
                            errs
                        with
                          true
                        then
                          Some
                            res59
                        else
                          (modref
                               (p.errors)
                               (concat
                                  (deref
                                     (p.errors))
                                  errs))
                          ;Some
                            (res59.#label"0", BadRegex
                              { info =
                                  res59.#label"0" })
                      else
                        (modref
                             (p.errors)
                             (snoc
                                (deref
                                   (p.errors))
                                (NoInfo
                                  {}, "Unfinished Regex")))
                        ;None
                          {})
               in
               optionGetOr
                 (NoInfo
                   {}, BadRegex
                   { info =
                       NoInfo
                         {} })
                 res59
         in
         let config3 =
           { topAllowed =
               topAllowed_ExprOp,
             leftAllowed =
               leftAllowed_ExprOp,
             rightAllowed =
               rightAllowed_ExprOp,
             parenAllowed =
               parenAllowed_ExprOp,
             groupingsAllowed =
               groupingsAllowed_ExprOp }
         in
         let reportConfig3 =
           { topAllowed =
               topAllowed_ExprOp,
             parenAllowed =
               parenAllowed_ExprOp,
             terminalInfos =
               get_ExprOp_terms,
             getInfo =
               get_ExprOp_info,
             lpar =
               "(",
             rpar =
               ")" }
         in
         let addExprOpAtom =
           lam #var"".
             lam x31.
               lam st.
                 optionMap
                   (breakableAddAtom
                      config3
                      x31)
                   st
         in
         let addExprOpInfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x31.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddInfix
                       config3
                       x31
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_ExprOp_info
                               x31, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   st
         in
         let addExprOpPrefix =
           lam #var"".
             lam x31.
               lam st.
                 optionMap
                   (breakableAddPrefix
                      config3
                      x31)
                   st
         in
         let addExprOpPostfix =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam x31.
               lam st.
                 match
                   st
                 with
                   Some st
                 then
                   let st =
                     breakableAddPostfix
                       config3
                       x31
                       st
                   in
                   (match
                        st
                      with
                        None _
                      then
                        modref
                          (p.errors)
                          (snoc
                             (deref
                                (p.errors))
                             (get_ExprOp_info
                               x31, "Invalid input"))
                      else
                        {})
                   ;st
                 else
                   st
         in
         let finalizeExprOp =
           lam p: {errors: (Ref) ([(Info, [Char])]), content: String}.
             lam st.
               let res59 =
                 optionBind
                   st
                   (lam st.
                      match
                        breakableFinalizeParse
                          config3
                          st
                      with
                        Some (tops & ([ top ] ++ _ ++ ""))
                      then
                        let errs =
                          breakableDefaultHighlight
                            reportConfig3
                            (p.content)
                            tops
                        in
                        let res59: (Info, Expr) =
                          unsplit_ExprOp
                            top
                        in
                        match
                          null
                            errs
                        with
                          true
                        then
                          Some
                            res59
                        else
                          (modref
                               (p.errors)
                               (concat
                                  (deref
                                     (p.errors))
                                  errs))
                          ;Some
                            (res59.#label"0", BadExpr
                              { info =
                                  res59.#label"0" })
                      else
                        (modref
                             (p.errors)
                             (snoc
                                (deref
                                   (p.errors))
                                (NoInfo
                                  {}, "Unfinished Expr")))
                        ;None
                          {})
               in
               optionGetOr
                 (NoInfo
                   {}, BadExpr
                   { info =
                       NoInfo
                         {} })
                 res59
         in
         [ { nt =
               kleene,
             label =
               {},
             rhs =
               [ ntSym
                   #var"Decl",
                 ntSym
                   kleene ],
             action =
               lam state: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res.
                   match
                     res
                   with
                     [ UserSym (info, val),
                       UserSym val1 ]
                   then
                     let val1: {__br_terms: [Info], decls: [Decl], __br_info: Info} =
                       val1
                     in
                     { __br_terms =
                         val1.__br_terms,
                       decls =
                         concat
                           [ val ]
                           (val1.decls),
                       __br_info =
                         mergeInfo
                           info
                           (val1.__br_info) }
                   else
                     never },
           { nt =
               kleene,
             label =
               {},
             rhs =
               "",
             action =
               lam state1: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res1.
                   match
                     res1
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       decls =
                         "",
                       __br_info =
                         NoInfo
                           {} }
                   else
                     never },
           { nt =
               #var"FileAtom",
             label =
               {},
             rhs =
               [ ntSym
                   #var"Decl",
                 ntSym
                   kleene ],
             action =
               lam state2: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res2.
                   match
                     res2
                   with
                     [ UserSym (info1, val2),
                       UserSym val1 ]
                   then
                     let val1: {__br_terms: [Info], decls: [Decl], __br_info: Info} =
                       val1
                     in
                     FileOp
                       { __br_terms =
                           val1.__br_terms,
                         decls =
                           concat
                             [ val2 ]
                             (val1.decls),
                         __br_info =
                           mergeInfo
                             info1
                             (val1.__br_info) }
                   else
                     never },
           { nt =
               #var"DeclAtom",
             label =
               {},
             rhs =
               [ litSym
                   "start",
                 tokSym
                   (UIdentRepr
                      {}) ],
             action =
               lam state3: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res3.
                   match
                     res3
                   with
                     [ LitParsed l,
                       TokParsed (UIdentTok x) ]
                   then
                     StartDeclOp
                       { __br_terms =
                           concat
                             [ l.info ]
                             [ x.info ],
                         __br_info =
                           mergeInfo
                             (l.info)
                             (x.info),
                         name =
                           [ { v =
                                 nameNoSym
                                   (x.val),
                               i =
                                 x.info } ] }
                   else
                     never },
           { nt =
               kleene1,
             label =
               {},
             rhs =
               [ tokSym
                   (LIdentRepr
                      {}),
                 litSym
                   "=",
                 ntSym
                   #var"Expr",
                 litSym
                   ",",
                 ntSym
                   kleene1 ],
             action =
               lam state4: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res4.
                   match
                     res4
                   with
                     [ TokParsed (LIdentTok x1),
                       LitParsed l1,
                       UserSym (info2, val3),
                       LitParsed l2,
                       UserSym val4 ]
                   then
                     let val4: {__br_terms: [Info], __br_info: Info, properties: [{val: Expr, name: {v: Name, i: Info}}]} =
                       val4
                     in
                     { __br_terms =
                         join
                           [ [ x1.info ],
                             [ l1.info ],
                             [ l2.info ],
                             val4.__br_terms ],
                       __br_info =
                         foldl
                           mergeInfo
                           (x1.info)
                           [ l1.info,
                             info2,
                             l2.info,
                             val4.__br_info ],
                       properties =
                         concat
                           [ { val =
                                 match
                                   [ val3 ]
                                 with
                                   [ x2 ] ++ _ ++ ""
                                 then
                                   x2
                                 else
                                   never,
                               name =
                                 match
                                   [ { v =
                                         nameNoSym
                                           (x1.val),
                                       i =
                                         x1.info } ]
                                 with
                                   [ x3 ] ++ _ ++ ""
                                 then
                                   x3
                                 else
                                   never } ]
                           (val4.properties) }
                   else
                     never },
           { nt =
               kleene1,
             label =
               {},
             rhs =
               "",
             action =
               lam state5: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res5.
                   match
                     res5
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       properties =
                         "" }
                   else
                     never },
           { nt =
               alt,
             label =
               {},
             rhs =
               "",
             action =
               lam state6: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res6.
                   match
                     res6
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       properties =
                         "" }
                   else
                     never },
           { nt =
               alt,
             label =
               {},
             rhs =
               [ litSym
                   "{",
                 ntSym
                   kleene1,
                 litSym
                   "}" ],
             action =
               lam state7: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res7.
                   match
                     res7
                   with
                     [ LitParsed l3,
                       UserSym val4,
                       LitParsed l4 ]
                   then
                     let val4: {__br_terms: [Info], __br_info: Info, properties: [{val: Expr, name: {v: Name, i: Info}}]} =
                       val4
                     in
                     { __br_terms =
                         join
                           [ [ l3.info ],
                             val4.__br_terms,
                             [ l4.info ] ],
                       __br_info =
                         foldl
                           mergeInfo
                           (l3.info)
                           [ val4.__br_info,
                             l4.info ],
                       properties =
                         val4.properties }
                   else
                     never },
           { nt =
               #var"DeclAtom",
             label =
               {},
             rhs =
               [ litSym
                   "type",
                 tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   alt ],
             action =
               lam state8: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res8.
                   match
                     res8
                   with
                     [ LitParsed l5,
                       TokParsed (UIdentTok x4),
                       UserSym val5 ]
                   then
                     let val5: {__br_terms: [Info], __br_info: Info, properties: [{val: Expr, name: {v: Name, i: Info}}]} =
                       val5
                     in
                     TypeDeclOp
                       { __br_terms =
                           join
                             [ [ l5.info ],
                               [ x4.info ],
                               val5.__br_terms ],
                         __br_info =
                           foldl
                             mergeInfo
                             (l5.info)
                             [ x4.info,
                               val5.__br_info ],
                         name =
                           [ { v =
                                 nameNoSym
                                   (x4.val),
                               i =
                                 x4.info } ],
                         properties =
                           val5.properties }
                   else
                     never },
           { nt =
               alt1,
             label =
               {},
             rhs =
               "",
             action =
               lam state9: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res9.
                   match
                     res9
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       name =
                         "" }
                   else
                     never },
           { nt =
               alt1,
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}) ],
             action =
               lam state10: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res10.
                   match
                     res10
                   with
                     [ TokParsed (UIdentTok x5) ]
                   then
                     { __br_terms =
                         [ x5.info ],
                       __br_info =
                         x5.info,
                       name =
                         [ { v =
                               nameNoSym
                                 (x5.val),
                             i =
                               x5.info } ] }
                   else
                     never },
           { nt =
               kleene2,
             label =
               {},
             rhs =
               [ tokSym
                   (LIdentRepr
                      {}),
                 litSym
                   "=",
                 ntSym
                   #var"Expr",
                 litSym
                   ",",
                 ntSym
                   kleene2 ],
             action =
               lam state11: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res11.
                   match
                     res11
                   with
                     [ TokParsed (LIdentTok x6),
                       LitParsed l6,
                       UserSym (info3, val6),
                       LitParsed l7,
                       UserSym val7 ]
                   then
                     let val7: {__br_terms: [Info], __br_info: Info, properties: [{val: Expr, name: {v: Name, i: Info}}]} =
                       val7
                     in
                     { __br_terms =
                         join
                           [ [ x6.info ],
                             [ l6.info ],
                             [ l7.info ],
                             val7.__br_terms ],
                       __br_info =
                         foldl
                           mergeInfo
                           (x6.info)
                           [ l6.info,
                             info3,
                             l7.info,
                             val7.__br_info ],
                       properties =
                         concat
                           [ { val =
                                 match
                                   [ val6 ]
                                 with
                                   [ x7 ] ++ _ ++ ""
                                 then
                                   x7
                                 else
                                   never,
                               name =
                                 match
                                   [ { v =
                                         nameNoSym
                                           (x6.val),
                                       i =
                                         x6.info } ]
                                 with
                                   [ x8 ] ++ _ ++ ""
                                 then
                                   x8
                                 else
                                   never } ]
                           (val7.properties) }
                   else
                     never },
           { nt =
               kleene2,
             label =
               {},
             rhs =
               "",
             action =
               lam state12: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res12.
                   match
                     res12
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       properties =
                         "" }
                   else
                     never },
           { nt =
               alt2,
             label =
               {},
             rhs =
               "",
             action =
               lam state13: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res13.
                   match
                     res13
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       properties =
                         "" }
                   else
                     never },
           { nt =
               alt2,
             label =
               {},
             rhs =
               [ litSym
                   "{",
                 ntSym
                   kleene2,
                 litSym
                   "}" ],
             action =
               lam state14: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res14.
                   match
                     res14
                   with
                     [ LitParsed l8,
                       UserSym val7,
                       LitParsed l9 ]
                   then
                     let val7: {__br_terms: [Info], __br_info: Info, properties: [{val: Expr, name: {v: Name, i: Info}}]} =
                       val7
                     in
                     { __br_terms =
                         join
                           [ [ l8.info ],
                             val7.__br_terms,
                             [ l9.info ] ],
                       __br_info =
                         foldl
                           mergeInfo
                           (l8.info)
                           [ val7.__br_info,
                             l9.info ],
                       properties =
                         val7.properties }
                   else
                     never },
           { nt =
               #var"DeclAtom",
             label =
               {},
             rhs =
               [ litSym
                   "token",
                 ntSym
                   alt1,
                 ntSym
                   alt2 ],
             action =
               lam state15: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res15.
                   match
                     res15
                   with
                     [ LitParsed l10,
                       UserSym val8,
                       UserSym val9 ]
                   then
                     let val8: {__br_terms: [Info], __br_info: Info, name: [{v: Name, i: Info}]} =
                       val8
                     in
                     let val9: {__br_terms: [Info], __br_info: Info, properties: [{val: Expr, name: {v: Name, i: Info}}]} =
                       val9
                     in
                     TokenDeclOp
                       { __br_terms =
                           join
                             [ [ l10.info ],
                               val8.__br_terms,
                               val9.__br_terms ],
                         __br_info =
                           foldl
                             mergeInfo
                             (l10.info)
                             [ val8.__br_info,
                               val9.__br_info ],
                         name =
                           val8.name,
                         properties =
                           val9.properties }
                   else
                     never },
           { nt =
               alt3,
             label =
               {},
             rhs =
               "",
             action =
               lam state16: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res16.
                   match
                     res16
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       noeq =
                         "" }
                   else
                     never },
           { nt =
               alt3,
             label =
               {},
             rhs =
               [ litSym
                   "~" ],
             action =
               lam state17: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res17.
                   match
                     res17
                   with
                     [ LitParsed l11 ]
                   then
                     { __br_terms =
                         [ l11.info ],
                       __br_info =
                         l11.info,
                       noeq =
                         [ l11.info ] }
                   else
                     never },
           { nt =
               kleene3,
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   kleene3 ],
             action =
               lam state18: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res18.
                   match
                     res18
                   with
                     [ TokParsed (UIdentTok x9),
                       UserSym val10 ]
                   then
                     let val10: {__br_terms: [Info], __br_info: Info, operators: [{v: Name, i: Info}]} =
                       val10
                     in
                     { __br_terms =
                         concat
                           [ x9.info ]
                           (val10.__br_terms),
                       __br_info =
                         mergeInfo
                           (x9.info)
                           (val10.__br_info),
                       operators =
                         concat
                           [ { v =
                                 nameNoSym
                                   (x9.val),
                               i =
                                 x9.info } ]
                           (val10.operators) }
                   else
                     never },
           { nt =
               kleene3,
             label =
               {},
             rhs =
               "",
             action =
               lam state19: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res19.
                   match
                     res19
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       operators =
                         "" }
                   else
                     never },
           { nt =
               kleene4,
             label =
               {},
             rhs =
               [ ntSym
                   alt3,
                 tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   kleene3,
                 litSym
                   ";",
                 ntSym
                   kleene4 ],
             action =
               lam state20: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res20.
                   match
                     res20
                   with
                     [ UserSym val11,
                       TokParsed (UIdentTok x10),
                       UserSym val10,
                       LitParsed l12,
                       UserSym val12 ]
                   then
                     let val11: {__br_terms: [Info], __br_info: Info, noeq: [Info]} =
                       val11
                     in
                     let val10: {__br_terms: [Info], __br_info: Info, operators: [{v: Name, i: Info}]} =
                       val10
                     in
                     let val12: {__br_terms: [Info], __br_info: Info, levels: [{noeq: (Option) (Info), operators: [{v: Name, i: Info}]}]} =
                       val12
                     in
                     { __br_terms =
                         join
                           [ val11.__br_terms,
                             [ x10.info ],
                             val10.__br_terms,
                             [ l12.info ],
                             val12.__br_terms ],
                       __br_info =
                         foldl
                           mergeInfo
                           (val11.__br_info)
                           [ x10.info,
                             val10.__br_info,
                             l12.info,
                             val12.__br_info ],
                       levels =
                         concat
                           [ { noeq =
                                 match
                                   val11.noeq
                                 with
                                   [ x11 ] ++ _ ++ ""
                                 then
                                   Some
                                     x11
                                 else
                                   None
                                     {},
                               operators =
                                 concat
                                   [ { v =
                                         nameNoSym
                                           (x10.val),
                                       i =
                                         x10.info } ]
                                   (val10.operators) } ]
                           (val12.levels) }
                   else
                     never },
           { nt =
               kleene4,
             label =
               {},
             rhs =
               "",
             action =
               lam state21: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res21.
                   match
                     res21
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       levels =
                         "" }
                   else
                     never },
           { nt =
               kleene5,
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   kleene5 ],
             action =
               lam state22: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res22.
                   match
                     res22
                   with
                     [ TokParsed (UIdentTok x12),
                       UserSym val13 ]
                   then
                     let val13: {__br_terms: [Info], __br_info: Info, lefts: [{v: Name, i: Info}]} =
                       val13
                     in
                     { __br_terms =
                         concat
                           [ x12.info ]
                           (val13.__br_terms),
                       __br_info =
                         mergeInfo
                           (x12.info)
                           (val13.__br_info),
                       lefts =
                         concat
                           [ { v =
                                 nameNoSym
                                   (x12.val),
                               i =
                                 x12.info } ]
                           (val13.lefts) }
                   else
                     never },
           { nt =
               kleene5,
             label =
               {},
             rhs =
               "",
             action =
               lam state23: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res23.
                   match
                     res23
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       lefts =
                         "" }
                   else
                     never },
           { nt =
               kleene6,
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   kleene6 ],
             action =
               lam state24: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res24.
                   match
                     res24
                   with
                     [ TokParsed (UIdentTok x13),
                       UserSym val14 ]
                   then
                     let val14: {__br_terms: [Info], __br_info: Info, rights: [{v: Name, i: Info}]} =
                       val14
                     in
                     { __br_terms =
                         concat
                           [ x13.info ]
                           (val14.__br_terms),
                       __br_info =
                         mergeInfo
                           (x13.info)
                           (val14.__br_info),
                       rights =
                         concat
                           [ { v =
                                 nameNoSym
                                   (x13.val),
                               i =
                                 x13.info } ]
                           (val14.rights) }
                   else
                     never },
           { nt =
               kleene6,
             label =
               {},
             rhs =
               "",
             action =
               lam state25: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res25.
                   match
                     res25
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       rights =
                         "" }
                   else
                     never },
           { nt =
               kleene7,
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   kleene5,
                 litSym
                   "?",
                 tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   kleene6,
                 litSym
                   ";",
                 ntSym
                   kleene7 ],
             action =
               lam state26: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res26.
                   match
                     res26
                   with
                     [ TokParsed (UIdentTok x14),
                       UserSym val13,
                       LitParsed l13,
                       TokParsed (UIdentTok x15),
                       UserSym val14,
                       LitParsed l14,
                       UserSym val15 ]
                   then
                     let val13: {__br_terms: [Info], __br_info: Info, lefts: [{v: Name, i: Info}]} =
                       val13
                     in
                     let val14: {__br_terms: [Info], __br_info: Info, rights: [{v: Name, i: Info}]} =
                       val14
                     in
                     let val15: {__br_terms: [Info], __br_info: Info, exceptions: [{lefts: [{v: Name, i: Info}], rights: [{v: Name, i: Info}]}]} =
                       val15
                     in
                     { __br_terms =
                         join
                           [ [ x14.info ],
                             val13.__br_terms,
                             [ l13.info ],
                             [ x15.info ],
                             val14.__br_terms,
                             [ l14.info ],
                             val15.__br_terms ],
                       __br_info =
                         foldl
                           mergeInfo
                           (x14.info)
                           [ val13.__br_info,
                             l13.info,
                             x15.info,
                             val14.__br_info,
                             l14.info,
                             val15.__br_info ],
                       exceptions =
                         concat
                           [ { lefts =
                                 concat
                                   [ { v =
                                         nameNoSym
                                           (x14.val),
                                       i =
                                         x14.info } ]
                                   (val13.lefts),
                               rights =
                                 concat
                                   [ { v =
                                         nameNoSym
                                           (x15.val),
                                       i =
                                         x15.info } ]
                                   (val14.rights) } ]
                           (val15.exceptions) }
                   else
                     never },
           { nt =
               kleene7,
             label =
               {},
             rhs =
               "",
             action =
               lam state27: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res27.
                   match
                     res27
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       exceptions =
                         "" }
                   else
                     never },
           { nt =
               alt4,
             label =
               {},
             rhs =
               "",
             action =
               lam state28: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res28.
                   match
                     res28
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       exceptions =
                         "" }
                   else
                     never },
           { nt =
               alt4,
             label =
               {},
             rhs =
               [ litSym
                   "except",
                 litSym
                   "{",
                 ntSym
                   kleene7,
                 litSym
                   "}" ],
             action =
               lam state29: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res29.
                   match
                     res29
                   with
                     [ LitParsed l15,
                       LitParsed l16,
                       UserSym val15,
                       LitParsed l17 ]
                   then
                     let val15: {__br_terms: [Info], __br_info: Info, exceptions: [{lefts: [{v: Name, i: Info}], rights: [{v: Name, i: Info}]}]} =
                       val15
                     in
                     { __br_terms =
                         join
                           [ [ l15.info ],
                             [ l16.info ],
                             val15.__br_terms,
                             [ l17.info ] ],
                       __br_info =
                         foldl
                           mergeInfo
                           (l15.info)
                           [ l16.info,
                             val15.__br_info,
                             l17.info ],
                       exceptions =
                         val15.exceptions }
                   else
                     never },
           { nt =
               #var"DeclAtom",
             label =
               {},
             rhs =
               [ litSym
                   "precedence",
                 litSym
                   "{",
                 ntSym
                   kleene4,
                 litSym
                   "}",
                 ntSym
                   alt4 ],
             action =
               lam state30: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res30.
                   match
                     res30
                   with
                     [ LitParsed l18,
                       LitParsed l19,
                       UserSym val12,
                       LitParsed l20,
                       UserSym val16 ]
                   then
                     let val12: {__br_terms: [Info], __br_info: Info, levels: [{noeq: (Option) (Info), operators: [{v: Name, i: Info}]}]} =
                       val12
                     in
                     let val16: {__br_terms: [Info], __br_info: Info, exceptions: [{lefts: [{v: Name, i: Info}], rights: [{v: Name, i: Info}]}]} =
                       val16
                     in
                     PrecedenceTableDeclOp
                       { __br_terms =
                           join
                             [ [ l18.info ],
                               [ l19.info ],
                               val12.__br_terms,
                               [ l20.info ],
                               val16.__br_terms ],
                         __br_info =
                           foldl
                             mergeInfo
                             (l18.info)
                             [ l19.info,
                               val12.__br_info,
                               l20.info,
                               val16.__br_info ],
                         levels =
                           val12.levels,
                         exceptions =
                           val16.exceptions }
                   else
                     never },
           { nt =
               alt5,
             label =
               {},
             rhs =
               [ litSym
                   "prod" ],
             action =
               lam state31: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res31.
                   match
                     res31
                   with
                     [ LitParsed l21 ]
                   then
                     { __br_terms =
                         [ l21.info ],
                       __br_info =
                         l21.info,
                       kinf =
                         "",
                       kpref =
                         "",
                       kprod =
                         [ l21.info ],
                       kpostf =
                         "" }
                   else
                     never },
           { nt =
               alt5,
             label =
               {},
             rhs =
               [ litSym
                   "infix" ],
             action =
               lam state32: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res32.
                   match
                     res32
                   with
                     [ LitParsed l22 ]
                   then
                     { __br_terms =
                         [ l22.info ],
                       __br_info =
                         l22.info,
                       kinf =
                         [ l22.info ],
                       kpref =
                         "",
                       kprod =
                         "",
                       kpostf =
                         "" }
                   else
                     never },
           { nt =
               alt5,
             label =
               {},
             rhs =
               [ litSym
                   "prefix" ],
             action =
               lam state33: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res33.
                   match
                     res33
                   with
                     [ LitParsed l23 ]
                   then
                     { __br_terms =
                         [ l23.info ],
                       __br_info =
                         l23.info,
                       kinf =
                         "",
                       kpref =
                         [ l23.info ],
                       kprod =
                         "",
                       kpostf =
                         "" }
                   else
                     never },
           { nt =
               alt5,
             label =
               {},
             rhs =
               [ litSym
                   "postfix" ],
             action =
               lam state34: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res34.
                   match
                     res34
                   with
                     [ LitParsed l24 ]
                   then
                     { __br_terms =
                         [ l24.info ],
                       __br_info =
                         l24.info,
                       kinf =
                         "",
                       kpref =
                         "",
                       kprod =
                         "",
                       kpostf =
                         [ l24.info ] }
                   else
                     never },
           { nt =
               alt6,
             label =
               {},
             rhs =
               "",
             action =
               lam state35: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res35.
                   match
                     res35
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       assoc =
                         "" }
                   else
                     never },
           { nt =
               alt6,
             label =
               {},
             rhs =
               [ tokSym
                   (LIdentRepr
                      {}) ],
             action =
               lam state36: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res36.
                   match
                     res36
                   with
                     [ TokParsed (LIdentTok x16) ]
                   then
                     { __br_terms =
                         [ x16.info ],
                       __br_info =
                         x16.info,
                       assoc =
                         [ { v =
                               x16.val,
                             i =
                               x16.info } ] }
                   else
                     never },
           { nt =
               #var"DeclAtom",
             label =
               {},
             rhs =
               [ ntSym
                   alt5,
                 ntSym
                   alt6,
                 tokSym
                   (UIdentRepr
                      {}),
                 litSym
                   ":",
                 tokSym
                   (UIdentRepr
                      {}),
                 litSym
                   "=",
                 ntSym
                   #var"Regex" ],
             action =
               lam state37: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res37.
                   match
                     res37
                   with
                     [ UserSym val17,
                       UserSym val18,
                       TokParsed (UIdentTok x17),
                       LitParsed l25,
                       TokParsed (UIdentTok x18),
                       LitParsed l26,
                       UserSym (info4, val19) ]
                   then
                     let val17: {__br_terms: [Info], __br_info: Info, kinf: [Info], kpref: [Info], kprod: [Info], kpostf: [Info]} =
                       val17
                     in
                     let val18: {__br_terms: [Info], __br_info: Info, assoc: [{v: String, i: Info}]} =
                       val18
                     in
                     ProductionDeclOp
                       { __br_terms =
                           join
                             [ val17.__br_terms,
                               val18.__br_terms,
                               [ x17.info ],
                               [ l25.info ],
                               [ x18.info ],
                               [ l26.info ] ],
                         __br_info =
                           foldl
                             mergeInfo
                             (val17.__br_info)
                             [ val18.__br_info,
                               x17.info,
                               l25.info,
                               x18.info,
                               l26.info,
                               info4 ],
                         nt =
                           [ { v =
                                 nameNoSym
                                   (x18.val),
                               i =
                                 x18.info } ],
                         name =
                           [ { v =
                                 nameNoSym
                                   (x17.val),
                               i =
                                 x17.info } ],
                         kinf =
                           val17.kinf,
                         kpref =
                           val17.kpref,
                         kprod =
                           val17.kprod,
                         kpostf =
                           val17.kpostf,
                         assoc =
                           val18.assoc,
                         regex =
                           [ val19 ] }
                   else
                     never },
           { nt =
               #var"RegexAtom",
             label =
               {},
             rhs =
               [ litSym
                   "{",
                 ntSym
                   #var"Regex",
                 litSym
                   "}" ],
             action =
               lam state38: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res38.
                   match
                     res38
                   with
                     [ LitParsed l27,
                       UserSym (info5, val20),
                       LitParsed l28 ]
                   then
                     RecordRegexOp
                       { __br_terms =
                           concat
                             [ l27.info ]
                             [ l28.info ],
                         __br_info =
                           foldl
                             mergeInfo
                             (l27.info)
                             [ info5,
                               l28.info ],
                         regex =
                           [ val20 ] }
                   else
                     never },
           { nt =
               #var"RegexAtom",
             label =
               {},
             rhs =
               [ litSym
                   "empty" ],
             action =
               lam state39: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res39.
                   match
                     res39
                   with
                     [ LitParsed l29 ]
                   then
                     EmptyRegexOp
                       { __br_terms =
                           [ l29.info ],
                         __br_info =
                           l29.info }
                   else
                     never },
           { nt =
               #var"RegexAtom",
             label =
               {},
             rhs =
               [ tokSym
                   (StringRepr
                      {}) ],
             action =
               lam state40: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res40.
                   match
                     res40
                   with
                     [ TokParsed (StringTok x19) ]
                   then
                     LiteralRegexOp
                       { __br_terms =
                           [ x19.info ],
                         __br_info =
                           x19.info,
                         val =
                           [ { v =
                                 x19.val,
                               i =
                                 x19.info } ] }
                   else
                     never },
           { nt =
               alt7,
             label =
               {},
             rhs =
               "",
             action =
               lam state41: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res41.
                   match
                     res41
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       arg =
                         "" }
                   else
                     never },
           { nt =
               alt7,
             label =
               {},
             rhs =
               [ litSym
                   "[",
                 ntSym
                   #var"Expr",
                 litSym
                   "]" ],
             action =
               lam state42: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res42.
                   match
                     res42
                   with
                     [ LitParsed l30,
                       UserSym (info6, val21),
                       LitParsed l31 ]
                   then
                     { __br_terms =
                         concat
                           [ l30.info ]
                           [ l31.info ],
                       __br_info =
                         foldl
                           mergeInfo
                           (l30.info)
                           [ info6,
                             l31.info ],
                       arg =
                         [ val21 ] }
                   else
                     never },
           { nt =
               #var"RegexAtom",
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}),
                 ntSym
                   alt7 ],
             action =
               lam state43: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res43.
                   match
                     res43
                   with
                     [ TokParsed (UIdentTok x20),
                       UserSym val22 ]
                   then
                     let val22: {__br_terms: [Info], __br_info: Info, arg: [Expr]} =
                       val22
                     in
                     TokenRegexOp
                       { __br_terms =
                           concat
                             [ x20.info ]
                             (val22.__br_terms),
                         __br_info =
                           mergeInfo
                             (x20.info)
                             (val22.__br_info),
                         name =
                           [ { v =
                                 nameNoSym
                                   (x20.val),
                               i =
                                 x20.info } ],
                         arg =
                           val22.arg }
                   else
                     never },
           { nt =
               #var"RegexPostfix",
             label =
               {},
             rhs =
               [ litSym
                   "+" ],
             action =
               lam state44: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res44.
                   match
                     res44
                   with
                     [ LitParsed l32 ]
                   then
                     RepeatPlusRegexOp
                       { __br_terms =
                           [ l32.info ],
                         __br_info =
                           l32.info }
                   else
                     never },
           { nt =
               #var"RegexPostfix",
             label =
               {},
             rhs =
               [ litSym
                   "*" ],
             action =
               lam state45: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res45.
                   match
                     res45
                   with
                     [ LitParsed l33 ]
                   then
                     RepeatStarRegexOp
                       { __br_terms =
                           [ l33.info ],
                         __br_info =
                           l33.info }
                   else
                     never },
           { nt =
               #var"RegexPostfix",
             label =
               {},
             rhs =
               [ litSym
                   "?" ],
             action =
               lam state46: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res46.
                   match
                     res46
                   with
                     [ LitParsed l34 ]
                   then
                     RepeatQuestionRegexOp
                       { __br_terms =
                           [ l34.info ],
                         __br_info =
                           l34.info }
                   else
                     never },
           { nt =
               #var"RegexPrefix",
             label =
               {},
             rhs =
               [ tokSym
                   (LIdentRepr
                      {}),
                 litSym
                   ":" ],
             action =
               lam state47: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res47.
                   match
                     res47
                   with
                     [ TokParsed (LIdentTok x21),
                       LitParsed l35 ]
                   then
                     NamedRegexOp
                       { __br_terms =
                           concat
                             [ x21.info ]
                             [ l35.info ],
                         __br_info =
                           mergeInfo
                             (x21.info)
                             (l35.info),
                         name =
                           [ { v =
                                 x21.val,
                               i =
                                 x21.info } ] }
                   else
                     never },
           { nt =
               #var"RegexInfix",
             label =
               {},
             rhs =
               [ litSym
                   "|" ],
             action =
               lam state48: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res48.
                   match
                     res48
                   with
                     [ LitParsed l36 ]
                   then
                     AlternativeRegexOp
                       { __br_terms =
                           [ l36.info ],
                         __br_info =
                           l36.info }
                   else
                     never },
           { nt =
               #var"RegexInfix",
             label =
               {},
             rhs =
               "",
             action =
               lam state49: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res49.
                   match
                     res49
                   with
                     ""
                   then
                     ConcatRegexOp
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {} }
                   else
                     never },
           { nt =
               #var"ExprInfix",
             label =
               {},
             rhs =
               "",
             action =
               lam state50: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res50.
                   match
                     res50
                   with
                     ""
                   then
                     AppExprOp
                       { __br_terms =
                           "",
                         __br_info =
                           NoInfo
                             {} }
                   else
                     never },
           { nt =
               #var"ExprAtom",
             label =
               {},
             rhs =
               [ tokSym
                   (UIdentRepr
                      {}) ],
             action =
               lam state51: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res51.
                   match
                     res51
                   with
                     [ TokParsed (UIdentTok x22) ]
                   then
                     ConExprOp
                       { __br_terms =
                           [ x22.info ],
                         __br_info =
                           x22.info,
                         name =
                           [ { v =
                                 nameNoSym
                                   (x22.val),
                               i =
                                 x22.info } ] }
                   else
                     never },
           { nt =
               #var"ExprAtom",
             label =
               {},
             rhs =
               [ tokSym
                   (StringRepr
                      {}) ],
             action =
               lam state52: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res52.
                   match
                     res52
                   with
                     [ TokParsed (StringTok x23) ]
                   then
                     StringExprOp
                       { __br_terms =
                           [ x23.info ],
                         __br_info =
                           x23.info,
                         val =
                           [ { v =
                                 x23.val,
                               i =
                                 x23.info } ] }
                   else
                     never },
           { nt =
               #var"ExprAtom",
             label =
               {},
             rhs =
               [ tokSym
                   (LIdentRepr
                      {}) ],
             action =
               lam state53: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res53.
                   match
                     res53
                   with
                     [ TokParsed (LIdentTok x24) ]
                   then
                     VariableExprOp
                       { __br_terms =
                           [ x24.info ],
                         __br_info =
                           x24.info,
                         name =
                           [ { v =
                                 nameNoSym
                                   (x24.val),
                               i =
                                 x24.info } ] }
                   else
                     never },
           { nt =
               kleene8,
             label =
               {},
             rhs =
               [ litSym
                   ",",
                 tokSym
                   (StringRepr
                      {}),
                 litSym
                   "=",
                 ntSym
                   #var"Expr",
                 ntSym
                   kleene8 ],
             action =
               lam state54: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res54.
                   match
                     res54
                   with
                     [ LitParsed l37,
                       TokParsed (StringTok x25),
                       LitParsed l38,
                       UserSym (info7, val23),
                       UserSym val24 ]
                   then
                     let val24: {__br_terms: [Info], __br_info: Info, fields: [{val: Expr, name: {v: String, i: Info}}]} =
                       val24
                     in
                     { __br_terms =
                         join
                           [ [ l37.info ],
                             [ x25.info ],
                             [ l38.info ],
                             val24.__br_terms ],
                       __br_info =
                         foldl
                           mergeInfo
                           (l37.info)
                           [ x25.info,
                             l38.info,
                             info7,
                             val24.__br_info ],
                       fields =
                         concat
                           [ { val =
                                 match
                                   [ val23 ]
                                 with
                                   [ x26 ] ++ _ ++ ""
                                 then
                                   x26
                                 else
                                   never,
                               name =
                                 match
                                   [ { v =
                                         x25.val,
                                       i =
                                         x25.info } ]
                                 with
                                   [ x27 ] ++ _ ++ ""
                                 then
                                   x27
                                 else
                                   never } ]
                           (val24.fields) }
                   else
                     never },
           { nt =
               kleene8,
             label =
               {},
             rhs =
               "",
             action =
               lam state55: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res55.
                   match
                     res55
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       fields =
                         "" }
                   else
                     never },
           { nt =
               alt8,
             label =
               {},
             rhs =
               "",
             action =
               lam state56: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res56.
                   match
                     res56
                   with
                     ""
                   then
                     { __br_terms =
                         "",
                       __br_info =
                         NoInfo
                           {},
                       fields =
                         "" }
                   else
                     never },
           { nt =
               alt8,
             label =
               {},
             rhs =
               [ tokSym
                   (StringRepr
                      {}),
                 litSym
                   "=",
                 ntSym
                   #var"Expr",
                 ntSym
                   kleene8 ],
             action =
               lam state57: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res57.
                   match
                     res57
                   with
                     [ TokParsed (StringTok x28),
                       LitParsed l39,
                       UserSym (info8, val25),
                       UserSym val24 ]
                   then
                     let val24: {__br_terms: [Info], __br_info: Info, fields: [{val: Expr, name: {v: String, i: Info}}]} =
                       val24
                     in
                     { __br_terms =
                         join
                           [ [ x28.info ],
                             [ l39.info ],
                             val24.__br_terms ],
                       __br_info =
                         foldl
                           mergeInfo
                           (x28.info)
                           [ l39.info,
                             info8,
                             val24.__br_info ],
                       fields =
                         concat
                           [ { val =
                                 match
                                   [ val25 ]
                                 with
                                   [ x29 ] ++ _ ++ ""
                                 then
                                   x29
                                 else
                                   never,
                               name =
                                 match
                                   [ { v =
                                         x28.val,
                                       i =
                                         x28.info } ]
                                 with
                                   [ x30 ] ++ _ ++ ""
                                 then
                                   x30
                                 else
                                   never } ]
                           (val24.fields) }
                   else
                     never },
           { nt =
               #var"ExprAtom",
             label =
               {},
             rhs =
               [ litSym
                   "{",
                 ntSym
                   alt8,
                 litSym
                   "}" ],
             action =
               lam state58: {errors: (Ref) ([(Info, [Char])]), content: String}.
                 lam res58.
                   match
                     res58
                   with
                     [ LitParsed l40,
                       UserSym val26,
                       LitParsed l41 ]
                   then
                     let val26: {__br_terms: [Info], __br_info: Info, fields: [{val: Expr, name: {v: String, i: Info}}]} =
                       val26
                     in
                     RecordExprOp
                       { __br_terms =
                           join
                             [ [ l40.info ],
                               val26.__br_terms,
                               [ l41.info ] ],
                         __br_info =
                           foldl
                             mergeInfo
                             (l40.info)
                             [ val26.__br_info,
                               l41.info ],
                         fields =
                           val26.fields }
                   else
                     never },
           { nt =
               #var"File",
             label =
               {},
             rhs =
               [ ntSym
                   #var"File_lclosed" ],
             action =
               lam #var"".
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym cont ]
                   then
                     cont
                       (Some
                          (breakableInitState
                             {}))
                   else
                     never },
           { nt =
               #var"File_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"FileAtom",
                 ntSym
                   #var"File_lopen" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addFileOpAtom
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"File_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"FileInfix",
                 ntSym
                   #var"File_lclosed" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addFileOpInfix
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"File_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"FilePrefix",
                 ntSym
                   #var"File_lclosed" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addFileOpPrefix
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"File_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"FilePostfix",
                 ntSym
                   #var"File_lopen" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addFileOpPostfix
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"File_lopen",
             label =
               {},
             rhs =
               "",
             action =
               lam p.
                 lam #var"".
                   lam st.
                     finalizeFileOp
                       p
                       st },
           { nt =
               #var"Decl",
             label =
               {},
             rhs =
               [ ntSym
                   #var"Decl_lclosed" ],
             action =
               lam #var"".
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym cont ]
                   then
                     cont
                       (Some
                          (breakableInitState
                             {}))
                   else
                     never },
           { nt =
               #var"Decl_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"DeclAtom",
                 ntSym
                   #var"Decl_lopen" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addDeclOpAtom
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"Decl_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"DeclInfix",
                 ntSym
                   #var"Decl_lclosed" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addDeclOpInfix
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"Decl_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"DeclPrefix",
                 ntSym
                   #var"Decl_lclosed" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addDeclOpPrefix
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"Decl_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"DeclPostfix",
                 ntSym
                   #var"Decl_lopen" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addDeclOpPostfix
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"Decl_lopen",
             label =
               {},
             rhs =
               "",
             action =
               lam p.
                 lam #var"".
                   lam st.
                     finalizeDeclOp
                       p
                       st },
           { nt =
               #var"Regex",
             label =
               {},
             rhs =
               [ ntSym
                   #var"Regex_lclosed" ],
             action =
               lam #var"".
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym cont ]
                   then
                     cont
                       (Some
                          (breakableInitState
                             {}))
                   else
                     never },
           { nt =
               #var"Regex_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"RegexAtom",
                 ntSym
                   #var"Regex_lopen" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addRegexOpAtom
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"Regex_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"RegexInfix",
                 ntSym
                   #var"Regex_lclosed" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addRegexOpInfix
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"Regex_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"RegexPrefix",
                 ntSym
                   #var"Regex_lclosed" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addRegexOpPrefix
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"Regex_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"RegexPostfix",
                 ntSym
                   #var"Regex_lopen" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addRegexOpPostfix
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"Regex_lopen",
             label =
               {},
             rhs =
               "",
             action =
               lam p.
                 lam #var"".
                   lam st.
                     finalizeRegexOp
                       p
                       st },
           { nt =
               #var"Expr",
             label =
               {},
             rhs =
               [ ntSym
                   #var"Expr_lclosed" ],
             action =
               lam #var"".
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym cont ]
                   then
                     cont
                       (Some
                          (breakableInitState
                             {}))
                   else
                     never },
           { nt =
               #var"Expr_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"ExprAtom",
                 ntSym
                   #var"Expr_lopen" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addExprOpAtom
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"Expr_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"ExprInfix",
                 ntSym
                   #var"Expr_lclosed" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addExprOpInfix
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"Expr_lclosed",
             label =
               {},
             rhs =
               [ ntSym
                   #var"ExprPrefix",
                 ntSym
                   #var"Expr_lclosed" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addExprOpPrefix
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"Expr_lopen",
             label =
               {},
             rhs =
               [ ntSym
                   #var"ExprPostfix",
                 ntSym
                   #var"Expr_lopen" ],
             action =
               lam p.
                 lam seq.
                   match
                     seq
                   with
                     [ UserSym x31,
                       UserSym cont ]
                   then
                     lam st.
                       cont
                         (addExprOpPostfix
                            p
                            x31
                            st)
                   else
                     never },
           { nt =
               #var"Expr_lopen",
             label =
               {},
             rhs =
               "",
             action =
               lam p.
                 lam #var"".
                   lam st.
                     finalizeExprOp
                       p
                       st } ] })
in
match
  target
with
  Right table
then
  table
else
  never

let parseSelfhost
: String -> String -> Either [(Info, String)] File
= lam filename. lam content.
  use ParseSelfhost in
  let config = {errors = ref [], content = content} in
  let res = parseWithTable _table filename config content in
  let errors = deref config.errors in
  let errors =
    match res with Left err then
      let err = ll1DefaultHighlight content (ll1ToErrorHighlightSpec err) in
      snoc errors err
    else errors in
  if null errors then eitherMapRight (lam x. match x with (_, x) in x) res else Left errors

let parseSelfhostExn
: String -> String -> File
= lam filename. lam content.
  switch parseSelfhost filename content
  case Left errors then
    for_ errors (lam x. match x with (info, msg) in printLn (infoErrorString info msg));
    exit 1
  case Right file then file
  end
