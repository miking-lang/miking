include "seq.mc"
include "parser/ll1.mc"
include "parser/breakable.mc"
include "parser/lexer.mc"
lang MergedBaseAst
  syn Binder =
  syn Merged =
  syn MergedTop =
  syn MergedFile =
  sem smapAccumL_MergedFile_MergedFile : all a. (a -> MergedFile -> (a, MergedFile)) -> a -> MergedFile -> (a, MergedFile)
sem smapAccumL_MergedFile_MergedFile f acc =
  | x ->
    (acc, x)
  sem smap_MergedFile_MergedFile : (MergedFile -> MergedFile) -> MergedFile -> MergedFile
sem smap_MergedFile_MergedFile f =
  | x ->
    (smapAccumL_MergedFile_MergedFile
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_MergedFile_MergedFile : all a. (a -> MergedFile -> a) -> a -> MergedFile -> a
sem sfold_MergedFile_MergedFile f acc =
  | x ->
    (smapAccumL_MergedFile_MergedFile
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_MergedFile_MergedTop : all a. (a -> MergedTop -> (a, MergedTop)) -> a -> MergedFile -> (a, MergedFile)
sem smapAccumL_MergedFile_MergedTop f acc =
  | x ->
    (acc, x)
  sem smap_MergedFile_MergedTop : (MergedTop -> MergedTop) -> MergedFile -> MergedFile
sem smap_MergedFile_MergedTop f =
  | x ->
    (smapAccumL_MergedFile_MergedTop
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_MergedFile_MergedTop : all a. (a -> MergedTop -> a) -> a -> MergedFile -> a
sem sfold_MergedFile_MergedTop f acc =
  | x ->
    (smapAccumL_MergedFile_MergedTop
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_MergedFile_Merged : all a. (a -> Merged -> (a, Merged)) -> a -> MergedFile -> (a, MergedFile)
sem smapAccumL_MergedFile_Merged f acc =
  | x ->
    (acc, x)
  sem smap_MergedFile_Merged : (Merged -> Merged) -> MergedFile -> MergedFile
sem smap_MergedFile_Merged f =
  | x ->
    (smapAccumL_MergedFile_Merged
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_MergedFile_Merged : all a. (a -> Merged -> a) -> a -> MergedFile -> a
sem sfold_MergedFile_Merged f acc =
  | x ->
    (smapAccumL_MergedFile_Merged
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_MergedFile_Binder : all a. (a -> Binder -> (a, Binder)) -> a -> MergedFile -> (a, MergedFile)
sem smapAccumL_MergedFile_Binder f acc =
  | x ->
    (acc, x)
  sem smap_MergedFile_Binder : (Binder -> Binder) -> MergedFile -> MergedFile
sem smap_MergedFile_Binder f =
  | x ->
    (smapAccumL_MergedFile_Binder
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_MergedFile_Binder : all a. (a -> Binder -> a) -> a -> MergedFile -> a
sem sfold_MergedFile_Binder f acc =
  | x ->
    (smapAccumL_MergedFile_Binder
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_MergedTop_MergedFile : all a. (a -> MergedFile -> (a, MergedFile)) -> a -> MergedTop -> (a, MergedTop)
sem smapAccumL_MergedTop_MergedFile f acc =
  | x ->
    (acc, x)
  sem smap_MergedTop_MergedFile : (MergedFile -> MergedFile) -> MergedTop -> MergedTop
sem smap_MergedTop_MergedFile f =
  | x ->
    (smapAccumL_MergedTop_MergedFile
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_MergedTop_MergedFile : all a. (a -> MergedFile -> a) -> a -> MergedTop -> a
sem sfold_MergedTop_MergedFile f acc =
  | x ->
    (smapAccumL_MergedTop_MergedFile
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_MergedTop_MergedTop : all a. (a -> MergedTop -> (a, MergedTop)) -> a -> MergedTop -> (a, MergedTop)
sem smapAccumL_MergedTop_MergedTop f acc =
  | x ->
    (acc, x)
  sem smap_MergedTop_MergedTop : (MergedTop -> MergedTop) -> MergedTop -> MergedTop
sem smap_MergedTop_MergedTop f =
  | x ->
    (smapAccumL_MergedTop_MergedTop
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_MergedTop_MergedTop : all a. (a -> MergedTop -> a) -> a -> MergedTop -> a
sem sfold_MergedTop_MergedTop f acc =
  | x ->
    (smapAccumL_MergedTop_MergedTop
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_MergedTop_Merged : all a. (a -> Merged -> (a, Merged)) -> a -> MergedTop -> (a, MergedTop)
sem smapAccumL_MergedTop_Merged f acc =
  | x ->
    (acc, x)
  sem smap_MergedTop_Merged : (Merged -> Merged) -> MergedTop -> MergedTop
sem smap_MergedTop_Merged f =
  | x ->
    (smapAccumL_MergedTop_Merged
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_MergedTop_Merged : all a. (a -> Merged -> a) -> a -> MergedTop -> a
sem sfold_MergedTop_Merged f acc =
  | x ->
    (smapAccumL_MergedTop_Merged
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_MergedTop_Binder : all a. (a -> Binder -> (a, Binder)) -> a -> MergedTop -> (a, MergedTop)
sem smapAccumL_MergedTop_Binder f acc =
  | x ->
    (acc, x)
  sem smap_MergedTop_Binder : (Binder -> Binder) -> MergedTop -> MergedTop
sem smap_MergedTop_Binder f =
  | x ->
    (smapAccumL_MergedTop_Binder
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_MergedTop_Binder : all a. (a -> Binder -> a) -> a -> MergedTop -> a
sem sfold_MergedTop_Binder f acc =
  | x ->
    (smapAccumL_MergedTop_Binder
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_Merged_MergedFile : all a. (a -> MergedFile -> (a, MergedFile)) -> a -> Merged -> (a, Merged)
sem smapAccumL_Merged_MergedFile f acc =
  | x ->
    (acc, x)
  sem smap_Merged_MergedFile : (MergedFile -> MergedFile) -> Merged -> Merged
sem smap_Merged_MergedFile f =
  | x ->
    (smapAccumL_Merged_MergedFile
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_Merged_MergedFile : all a. (a -> MergedFile -> a) -> a -> Merged -> a
sem sfold_Merged_MergedFile f acc =
  | x ->
    (smapAccumL_Merged_MergedFile
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_Merged_MergedTop : all a. (a -> MergedTop -> (a, MergedTop)) -> a -> Merged -> (a, Merged)
sem smapAccumL_Merged_MergedTop f acc =
  | x ->
    (acc, x)
  sem smap_Merged_MergedTop : (MergedTop -> MergedTop) -> Merged -> Merged
sem smap_Merged_MergedTop f =
  | x ->
    (smapAccumL_Merged_MergedTop
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_Merged_MergedTop : all a. (a -> MergedTop -> a) -> a -> Merged -> a
sem sfold_Merged_MergedTop f acc =
  | x ->
    (smapAccumL_Merged_MergedTop
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_Merged_Merged : all a. (a -> Merged -> (a, Merged)) -> a -> Merged -> (a, Merged)
sem smapAccumL_Merged_Merged f acc =
  | x ->
    (acc, x)
  sem smap_Merged_Merged : (Merged -> Merged) -> Merged -> Merged
sem smap_Merged_Merged f =
  | x ->
    (smapAccumL_Merged_Merged
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_Merged_Merged : all a. (a -> Merged -> a) -> a -> Merged -> a
sem sfold_Merged_Merged f acc =
  | x ->
    (smapAccumL_Merged_Merged
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_Merged_Binder : all a. (a -> Binder -> (a, Binder)) -> a -> Merged -> (a, Merged)
sem smapAccumL_Merged_Binder f acc =
  | x ->
    (acc, x)
  sem smap_Merged_Binder : (Binder -> Binder) -> Merged -> Merged
sem smap_Merged_Binder f =
  | x ->
    (smapAccumL_Merged_Binder
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_Merged_Binder : all a. (a -> Binder -> a) -> a -> Merged -> a
sem sfold_Merged_Binder f acc =
  | x ->
    (smapAccumL_Merged_Binder
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_Binder_MergedFile : all a. (a -> MergedFile -> (a, MergedFile)) -> a -> Binder -> (a, Binder)
sem smapAccumL_Binder_MergedFile f acc =
  | x ->
    (acc, x)
  sem smap_Binder_MergedFile : (MergedFile -> MergedFile) -> Binder -> Binder
sem smap_Binder_MergedFile f =
  | x ->
    (smapAccumL_Binder_MergedFile
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_Binder_MergedFile : all a. (a -> MergedFile -> a) -> a -> Binder -> a
sem sfold_Binder_MergedFile f acc =
  | x ->
    (smapAccumL_Binder_MergedFile
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_Binder_MergedTop : all a. (a -> MergedTop -> (a, MergedTop)) -> a -> Binder -> (a, Binder)
sem smapAccumL_Binder_MergedTop f acc =
  | x ->
    (acc, x)
  sem smap_Binder_MergedTop : (MergedTop -> MergedTop) -> Binder -> Binder
sem smap_Binder_MergedTop f =
  | x ->
    (smapAccumL_Binder_MergedTop
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_Binder_MergedTop : all a. (a -> MergedTop -> a) -> a -> Binder -> a
sem sfold_Binder_MergedTop f acc =
  | x ->
    (smapAccumL_Binder_MergedTop
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_Binder_Merged : all a. (a -> Merged -> (a, Merged)) -> a -> Binder -> (a, Binder)
sem smapAccumL_Binder_Merged f acc =
  | x ->
    (acc, x)
  sem smap_Binder_Merged : (Merged -> Merged) -> Binder -> Binder
sem smap_Binder_Merged f =
  | x ->
    (smapAccumL_Binder_Merged
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_Binder_Merged : all a. (a -> Merged -> a) -> a -> Binder -> a
sem sfold_Binder_Merged f acc =
  | x ->
    (smapAccumL_Binder_Merged
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem smapAccumL_Binder_Binder : all a. (a -> Binder -> (a, Binder)) -> a -> Binder -> (a, Binder)
sem smapAccumL_Binder_Binder f acc =
  | x ->
    (acc, x)
  sem smap_Binder_Binder : (Binder -> Binder) -> Binder -> Binder
sem smap_Binder_Binder f =
  | x ->
    (smapAccumL_Binder_Binder
       (lam #var"".
          lam x.
            ({}, f
              x))
       {}
       x).1
  sem sfold_Binder_Binder : all a. (a -> Binder -> a) -> a -> Binder -> a
sem sfold_Binder_Binder f acc =
  | x ->
    (smapAccumL_Binder_Binder
       (lam acc.
          lam x.
            (f
              acc
              x, x))
       acc
       x).0
  sem get_MergedFile_info : MergedFile -> Info
sem get_MergedFile_info =
  sem set_MergedFile_info : Info -> MergedFile -> MergedFile
sem set_MergedFile_info val =
  sem mapAccum_MergedFile_info : all a. (a -> Info -> (a, Info)) -> a -> MergedFile -> (a, MergedFile)
sem mapAccum_MergedFile_info f acc =
  | target ->
    match
      f
        acc
        (get_MergedFile_info
           target)
    with
      (acc, val)
    in
    (acc, set_MergedFile_info
        val
        target)
  sem map_MergedFile_info : (Info -> Info) -> MergedFile -> MergedFile
sem map_MergedFile_info f =
  | target ->
    set_MergedFile_info
      (f
         (get_MergedFile_info
            target))
      target
  sem get_MergedTop_info : MergedTop -> Info
sem get_MergedTop_info =
  sem set_MergedTop_info : Info -> MergedTop -> MergedTop
sem set_MergedTop_info val =
  sem mapAccum_MergedTop_info : all a. (a -> Info -> (a, Info)) -> a -> MergedTop -> (a, MergedTop)
sem mapAccum_MergedTop_info f acc =
  | target ->
    match
      f
        acc
        (get_MergedTop_info
           target)
    with
      (acc, val)
    in
    (acc, set_MergedTop_info
        val
        target)
  sem map_MergedTop_info : (Info -> Info) -> MergedTop -> MergedTop
sem map_MergedTop_info f =
  | target ->
    set_MergedTop_info
      (f
         (get_MergedTop_info
            target))
      target
  sem get_Merged_info : Merged -> Info
sem get_Merged_info =
  sem set_Merged_info : Info -> Merged -> Merged
sem set_Merged_info val =
  sem mapAccum_Merged_info : all a. (a -> Info -> (a, Info)) -> a -> Merged -> (a, Merged)
sem mapAccum_Merged_info f acc =
  | target ->
    match
      f
        acc
        (get_Merged_info
           target)
    with
      (acc, val)
    in
    (acc, set_Merged_info
        val
        target)
  sem map_Merged_info : (Info -> Info) -> Merged -> Merged
sem map_Merged_info f =
  | target ->
    set_Merged_info
      (f
         (get_Merged_info
            target))
      target
  sem get_Binder_info : Binder -> Info
sem get_Binder_info =
  sem set_Binder_info : Info -> Binder -> Binder
sem set_Binder_info val =
  sem mapAccum_Binder_info : all a. (a -> Info -> (a, Info)) -> a -> Binder -> (a, Binder)
sem mapAccum_Binder_info f acc =
  | target ->
    match
      f
        acc
        (get_Binder_info
           target)
    with
      (acc, val)
    in
    (acc, set_Binder_info
        val
        target)
  sem map_Binder_info : (Info -> Info) -> Binder -> Binder
sem map_Binder_info f =
  | target ->
    set_Binder_info
      (f
         (get_Binder_info
            target))
      target
end
lang TopsMergedFileAst =
  MergedBaseAst
  type TopsMergedFileRecord =
    {info: Info, tops: [MergedTop]}
  syn MergedFile =
  | TopsMergedFile TopsMergedFileRecord
  sem smapAccumL_MergedFile_MergedTop f acc =
  | TopsMergedFile x ->
    match
      match
        let tops =
          x.tops
        in
        mapAccumL
          (lam acc1.
             lam x1: MergedTop.
               f
                 acc1
                 x1)
          acc
          tops
      with
        (acc, tops)
      in
      (acc, { x
          with
          tops =
            tops })
    with
      (acc, x)
    in
    (acc, TopsMergedFile
        x)
  sem get_MergedFile_info =
  | TopsMergedFile target ->
    target.info
  sem set_MergedFile_info val =
  | TopsMergedFile target ->
    TopsMergedFile
      { target
        with
        info =
          val }
end
lang DefMergedTopAst =
  MergedBaseAst
  type DefMergedTopRecord =
    {b: Binder, info: Info}
  syn MergedTop =
  | DefMergedTop DefMergedTopRecord
  sem smapAccumL_MergedTop_Binder f acc =
  | DefMergedTop x ->
    match
      match
        let b =
          x.b
        in
        f
          acc
          b
      with
        (acc, b)
      in
      (acc, { x
          with
          b =
            b })
    with
      (acc, x)
    in
    (acc, DefMergedTop
        x)
  sem get_MergedTop_info =
  | DefMergedTop target ->
    target.info
  sem set_MergedTop_info val =
  | DefMergedTop target ->
    DefMergedTop
      { target
        with
        info =
          val }
end
lang ExprMergedTopAst =
  MergedBaseAst
  type ExprMergedTopRecord =
    {e: Merged, info: Info}
  syn MergedTop =
  | ExprMergedTop ExprMergedTopRecord
  sem smapAccumL_MergedTop_Merged f acc =
  | ExprMergedTop x ->
    match
      match
        let e =
          x.e
        in
        f
          acc
          e
      with
        (acc, e)
      in
      (acc, { x
          with
          e =
            e })
    with
      (acc, x)
    in
    (acc, ExprMergedTop
        x)
  sem get_MergedTop_info =
  | ExprMergedTop target ->
    target.info
  sem set_MergedTop_info val =
  | ExprMergedTop target ->
    ExprMergedTop
      { target
        with
        info =
          val }
end
lang IncludeMergedTopAst =
  MergedBaseAst
  type IncludeMergedTopRecord =
    {info: Info, path: {i: Info, v: String}}
  syn MergedTop =
  | IncludeMergedTop IncludeMergedTopRecord
  sem get_MergedTop_info =
  | IncludeMergedTop target ->
    target.info
  sem set_MergedTop_info val =
  | IncludeMergedTop target ->
    IncludeMergedTop
      { target
        with
        info =
          val }
end
lang TypeBinderAst =
  MergedBaseAst
  type TypeBinderRecord =
    {info: Info, ident: {i: Info, v: Name}, params: [{i: Info, v: Name}], tyIdent: Option Merged}
  syn Binder =
  | TypeBinder TypeBinderRecord
  sem smapAccumL_Binder_Merged f acc =
  | TypeBinder x ->
    match
      match
        let tyIdent =
          x.tyIdent
        in
        optionMapAccum
          (lam acc1.
             lam x1.
               f
                 acc1
                 x1)
          acc
          tyIdent
      with
        (acc, tyIdent)
      in
      (acc, { x
          with
          tyIdent =
            tyIdent })
    with
      (acc, x)
    in
    (acc, TypeBinder
        x)
  sem get_Binder_info =
  | TypeBinder target ->
    target.info
  sem set_Binder_info val =
  | TypeBinder target ->
    TypeBinder
      { target
        with
        info =
          val }
end
lang ConBinderAst =
  MergedBaseAst
  type ConBinderRecord =
    {info: Info, ident: {i: Info, v: Name}, tyIdent: Merged}
  syn Binder =
  | ConBinder ConBinderRecord
  sem smapAccumL_Binder_Merged f acc =
  | ConBinder x ->
    match
      match
        let tyIdent =
          x.tyIdent
        in
        f
          acc
          tyIdent
      with
        (acc, tyIdent)
      in
      (acc, { x
          with
          tyIdent =
            tyIdent })
    with
      (acc, x)
    in
    (acc, ConBinder
        x)
  sem get_Binder_info =
  | ConBinder target ->
    target.info
  sem set_Binder_info val =
  | ConBinder target ->
    ConBinder
      { target
        with
        info =
          val }
end
lang RecLetBinderAst =
  MergedBaseAst
  type RecLetBinderRecord =
    {info: Info, bindings: [{body: Merged, ident: {i: Info, v: Name}, tyAnnot: Option Merged}]}
  syn Binder =
  | RecLetBinder RecLetBinderRecord
  sem smapAccumL_Binder_Merged f acc =
  | RecLetBinder x ->
    match
      match
        let bindings =
          x.bindings
        in
        mapAccumL
          (lam acc1.
             lam x1: {body: Merged, ident: {i: Info, v: Name}, tyAnnot: Option Merged}.
               match
                 let body =
                   x1.body
                 in
                 f
                   acc1
                   body
               with
                 (acc1, body)
               in
               match
                   let tyAnnot =
                     x1.tyAnnot
                   in
                   optionMapAccum
                     (lam acc2.
                        lam x2.
                          f
                            acc2
                            x2)
                     acc1
                     tyAnnot
                 with
                   (acc1, tyAnnot)
                 in
                 (acc1, { { x1
                       with
                       body =
                         body }
                     with
                     tyAnnot =
                       tyAnnot }))
          acc
          bindings
      with
        (acc, bindings)
      in
      (acc, { x
          with
          bindings =
            bindings })
    with
      (acc, x)
    in
    (acc, RecLetBinder
        x)
  sem get_Binder_info =
  | RecLetBinder target ->
    target.info
  sem set_Binder_info val =
  | RecLetBinder target ->
    RecLetBinder
      { target
        with
        info =
          val }
end
lang LetBinderAst =
  MergedBaseAst
  type LetBinderRecord =
    {body: Merged, info: Info, ident: {i: Info, v: Name}, tyAnnot: Option Merged}
  syn Binder =
  | LetBinder LetBinderRecord
  sem smapAccumL_Binder_Merged f acc =
  | LetBinder x ->
    match
      match
        let body =
          x.body
        in
        f
          acc
          body
      with
        (acc, body)
      in
      match
          let tyAnnot =
            x.tyAnnot
          in
          optionMapAccum
            (lam acc1.
               lam x1.
                 f
                   acc1
                   x1)
            acc
            tyAnnot
        with
          (acc, tyAnnot)
        in
        (acc, { { x
              with
              body =
                body }
            with
            tyAnnot =
              tyAnnot })
    with
      (acc, x)
    in
    (acc, LetBinder
        x)
  sem get_Binder_info =
  | LetBinder target ->
    target.info
  sem set_Binder_info val =
  | LetBinder target ->
    LetBinder
      { target
        with
        info =
          val }
end
lang UseBinderAst =
  MergedBaseAst
  type UseBinderRecord =
    {n: {i: Info, v: Name}, info: Info}
  syn Binder =
  | UseBinder UseBinderRecord
  sem get_Binder_info =
  | UseBinder target ->
    target.info
  sem set_Binder_info val =
  | UseBinder target ->
    UseBinder
      { target
        with
        info =
          val }
end
lang UtestBinderAst =
  MergedBaseAst
  type UtestBinderRecord =
    {info: Info, test: Merged, tusing: Option Merged, tonfail: Option Merged, expected: Merged}
  syn Binder =
  | UtestBinder UtestBinderRecord
  sem smapAccumL_Binder_Merged f acc =
  | UtestBinder x ->
    match
      match
        let test =
          x.test
        in
        f
          acc
          test
      with
        (acc, test)
      in
      match
          let tusing =
            x.tusing
          in
          optionMapAccum
            (lam acc1.
               lam x1.
                 f
                   acc1
                   x1)
            acc
            tusing
        with
          (acc, tusing)
        in
        match
            let tonfail =
              x.tonfail
            in
            optionMapAccum
              (lam acc2.
                 lam x2.
                   f
                     acc2
                     x2)
              acc
              tonfail
          with
            (acc, tonfail)
          in
          match
              let expected =
                x.expected
              in
              f
                acc
                expected
            with
              (acc, expected)
            in
            (acc, { { { { x
                      with
                      test =
                        test }
                    with
                    tusing =
                      tusing }
                  with
                  tonfail =
                    tonfail }
                with
                expected =
                  expected })
    with
      (acc, x)
    in
    (acc, UtestBinder
        x)
  sem get_Binder_info =
  | UtestBinder target ->
    target.info
  sem set_Binder_info val =
  | UtestBinder target ->
    UtestBinder
      { target
        with
        info =
          val }
end
lang ExternalBinderAst =
  MergedBaseAst
  type ExternalBinderRecord =
    {info: Info, ident: {i: Info, v: Name}, effect: Option Info, tyIdent: Merged}
  syn Binder =
  | ExternalBinder ExternalBinderRecord
  sem smapAccumL_Binder_Merged f acc =
  | ExternalBinder x ->
    match
      match
        let tyIdent =
          x.tyIdent
        in
        f
          acc
          tyIdent
      with
        (acc, tyIdent)
      in
      (acc, { x
          with
          tyIdent =
            tyIdent })
    with
      (acc, x)
    in
    (acc, ExternalBinder
        x)
  sem get_Binder_info =
  | ExternalBinder target ->
    target.info
  sem set_Binder_info val =
  | ExternalBinder target ->
    ExternalBinder
      { target
        with
        info =
          val }
end
lang ProjMergedAst =
  MergedBaseAst
  type ProjMergedRecord =
    {info: Info, left: Merged, label: {i: Info, v: String}}
  syn Merged =
  | ProjMerged ProjMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | ProjMerged x ->
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
      in
      (acc, { x
          with
          left =
            left })
    with
      (acc, x)
    in
    (acc, ProjMerged
        x)
  sem get_Merged_info =
  | ProjMerged target ->
    target.info
  sem set_Merged_info val =
  | ProjMerged target ->
    ProjMerged
      { target
        with
        info =
          val }
end
lang AppMergedAst =
  MergedBaseAst
  type AppMergedRecord =
    {info: Info, left: Merged, right: Merged}
  syn Merged =
  | AppMerged AppMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | AppMerged x ->
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
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, AppMerged
        x)
  sem get_Merged_info =
  | AppMerged target ->
    target.info
  sem set_Merged_info val =
  | AppMerged target ->
    AppMerged
      { target
        with
        info =
          val }
end
lang SemiMergedAst =
  MergedBaseAst
  type SemiMergedRecord =
    {info: Info, left: Merged, right: Merged}
  syn Merged =
  | SemiMerged SemiMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | SemiMerged x ->
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
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, SemiMerged
        x)
  sem get_Merged_info =
  | SemiMerged target ->
    target.info
  sem set_Merged_info val =
  | SemiMerged target ->
    SemiMerged
      { target
        with
        info =
          val }
end
lang RecordAddMergedAst =
  MergedBaseAst
  type RecordAddMergedRecord =
    {info: Info, left: Merged, fields: [{ty: Option Merged, label: {i: Info, v: String}, value: Option Merged}]}
  syn Merged =
  | RecordAddMerged RecordAddMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | RecordAddMerged x ->
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
      in
      match
          let fields =
            x.fields
          in
          mapAccumL
            (lam acc1.
               lam x1: {ty: Option Merged, label: {i: Info, v: String}, value: Option Merged}.
                 match
                   let ty =
                     x1.ty
                   in
                   optionMapAccum
                     (lam acc2.
                        lam x2.
                          f
                            acc2
                            x2)
                     acc1
                     ty
                 with
                   (acc1, ty)
                 in
                 match
                     let value =
                       x1.value
                     in
                     optionMapAccum
                       (lam acc3.
                          lam x3.
                            f
                              acc3
                              x3)
                       acc1
                       value
                   with
                     (acc1, value)
                   in
                   (acc1, { { x1
                         with
                         ty =
                           ty }
                       with
                       value =
                         value }))
            acc
            fields
        with
          (acc, fields)
        in
        (acc, { { x
              with
              left =
                left }
            with
            fields =
              fields })
    with
      (acc, x)
    in
    (acc, RecordAddMerged
        x)
  sem get_Merged_info =
  | RecordAddMerged target ->
    target.info
  sem set_Merged_info val =
  | RecordAddMerged target ->
    RecordAddMerged
      { target
        with
        info =
          val }
end
lang RecordSubMergedAst =
  MergedBaseAst
  type RecordSubMergedRecord =
    {info: Info, left: Merged, fields: [{i: Info, v: String}]}
  syn Merged =
  | RecordSubMerged RecordSubMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | RecordSubMerged x ->
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
      in
      (acc, { x
          with
          left =
            left })
    with
      (acc, x)
    in
    (acc, RecordSubMerged
        x)
  sem get_Merged_info =
  | RecordSubMerged target ->
    target.info
  sem set_Merged_info val =
  | RecordSubMerged target ->
    RecordSubMerged
      { target
        with
        info =
          val }
end
lang RecordChangeMergedAst =
  MergedBaseAst
  type RecordChangeMergedRecord =
    {info: Info, left: Merged, fields: [{ty: Option Merged, label: {i: Info, v: String}, value: Option Merged}]}
  syn Merged =
  | RecordChangeMerged RecordChangeMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | RecordChangeMerged x ->
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
      in
      match
          let fields =
            x.fields
          in
          mapAccumL
            (lam acc1.
               lam x1: {ty: Option Merged, label: {i: Info, v: String}, value: Option Merged}.
                 match
                   let ty =
                     x1.ty
                   in
                   optionMapAccum
                     (lam acc2.
                        lam x2.
                          f
                            acc2
                            x2)
                     acc1
                     ty
                 with
                   (acc1, ty)
                 in
                 match
                     let value =
                       x1.value
                     in
                     optionMapAccum
                       (lam acc3.
                          lam x3.
                            f
                              acc3
                              x3)
                       acc1
                       value
                   with
                     (acc1, value)
                   in
                   (acc1, { { x1
                         with
                         ty =
                           ty }
                       with
                       value =
                         value }))
            acc
            fields
        with
          (acc, fields)
        in
        (acc, { { x
              with
              left =
                left }
            with
            fields =
              fields })
    with
      (acc, x)
    in
    (acc, RecordChangeMerged
        x)
  sem get_Merged_info =
  | RecordChangeMerged target ->
    target.info
  sem set_Merged_info val =
  | RecordChangeMerged target ->
    RecordChangeMerged
      { target
        with
        info =
          val }
end
lang BindMergedAst =
  MergedBaseAst
  type BindMergedRecord =
    {info: Info, right: Merged, binder: Binder}
  syn Merged =
  | BindMerged BindMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | BindMerged x ->
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
      in
      (acc, { x
          with
          right =
            right })
    with
      (acc, x)
    in
    (acc, BindMerged
        x)
  sem smapAccumL_Merged_Binder f acc =
  | BindMerged x ->
    match
      match
        let binder =
          x.binder
        in
        f
          acc
          binder
      with
        (acc, binder)
      in
      (acc, { x
          with
          binder =
            binder })
    with
      (acc, x)
    in
    (acc, BindMerged
        x)
  sem get_Merged_info =
  | BindMerged target ->
    target.info
  sem set_Merged_info val =
  | BindMerged target ->
    BindMerged
      { target
        with
        info =
          val }
end
lang LamMergedAst =
  MergedBaseAst
  type LamMergedRecord =
    {info: Info, ident: Option {i: Info, v: Name}, right: Merged, tyAnnot: Option Merged}
  syn Merged =
  | LamMerged LamMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | LamMerged x ->
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
      in
      match
          let tyAnnot =
            x.tyAnnot
          in
          optionMapAccum
            (lam acc1.
               lam x1.
                 f
                   acc1
                   x1)
            acc
            tyAnnot
        with
          (acc, tyAnnot)
        in
        (acc, { { x
              with
              right =
                right }
            with
            tyAnnot =
              tyAnnot })
    with
      (acc, x)
    in
    (acc, LamMerged
        x)
  sem get_Merged_info =
  | LamMerged target ->
    target.info
  sem set_Merged_info val =
  | LamMerged target ->
    LamMerged
      { target
        with
        info =
          val }
end
lang MatchMergedAst =
  MergedBaseAst
  type MatchMergedRecord =
    {els: Merged, pat: Merged, thn: Merged, info: Info, target: Merged}
  syn Merged =
  | MatchMerged MatchMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | MatchMerged x ->
    match
      match
        let els =
          x.els
        in
        f
          acc
          els
      with
        (acc, els)
      in
      match
          let pat =
            x.pat
          in
          f
            acc
            pat
        with
          (acc, pat)
        in
        match
            let thn =
              x.thn
            in
            f
              acc
              thn
          with
            (acc, thn)
          in
          match
              let target =
                x.target
              in
              f
                acc
                target
            with
              (acc, target)
            in
            (acc, { { { { x
                      with
                      els =
                        els }
                    with
                    pat =
                      pat }
                  with
                  thn =
                    thn }
                with
                target =
                  target })
    with
      (acc, x)
    in
    (acc, MatchMerged
        x)
  sem get_Merged_info =
  | MatchMerged target ->
    target.info
  sem set_Merged_info val =
  | MatchMerged target ->
    MatchMerged
      { target
        with
        info =
          val }
end
lang IfMergedAst =
  MergedBaseAst
  type IfMergedRecord =
    {els: Merged, thn: Merged, info: Info, target: Merged}
  syn Merged =
  | IfMerged IfMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | IfMerged x ->
    match
      match
        let els =
          x.els
        in
        f
          acc
          els
      with
        (acc, els)
      in
      match
          let thn =
            x.thn
          in
          f
            acc
            thn
        with
          (acc, thn)
        in
        match
            let target =
              x.target
            in
            f
              acc
              target
          with
            (acc, target)
          in
          (acc, { { { x
                  with
                  els =
                    els }
                with
                thn =
                  thn }
              with
              target =
                target })
    with
      (acc, x)
    in
    (acc, IfMerged
        x)
  sem get_Merged_info =
  | IfMerged target ->
    target.info
  sem set_Merged_info val =
  | IfMerged target ->
    IfMerged
      { target
        with
        info =
          val }
end
lang SwitchMergedAst =
  MergedBaseAst
  type SwitchMergedRecord =
    {fail: Info, info: Info, cases: [{pat: Merged, thn: Merged, keyword: Info}], target: Merged}
  syn Merged =
  | SwitchMerged SwitchMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | SwitchMerged x ->
    match
      match
        let cases =
          x.cases
        in
        mapAccumL
          (lam acc1.
             lam x1: {pat: Merged, thn: Merged, keyword: Info}.
               match
                 let pat =
                   x1.pat
                 in
                 f
                   acc1
                   pat
               with
                 (acc1, pat)
               in
               match
                   let thn =
                     x1.thn
                   in
                   f
                     acc1
                     thn
                 with
                   (acc1, thn)
                 in
                 (acc1, { { x1
                       with
                       pat =
                         pat }
                     with
                     thn =
                       thn }))
          acc
          cases
      with
        (acc, cases)
      in
      match
          let target =
            x.target
          in
          f
            acc
            target
        with
          (acc, target)
        in
        (acc, { { x
              with
              cases =
                cases }
            with
            target =
              target })
    with
      (acc, x)
    in
    (acc, SwitchMerged
        x)
  sem get_Merged_info =
  | SwitchMerged target ->
    target.info
  sem set_Merged_info val =
  | SwitchMerged target ->
    SwitchMerged
      { target
        with
        info =
          val }
end
lang ConMergedAst =
  MergedBaseAst
  type ConMergedRecord =
    {info: Info, ident: {i: Info, v: Name}}
  syn Merged =
  | ConMerged ConMergedRecord
  sem get_Merged_info =
  | ConMerged target ->
    target.info
  sem set_Merged_info val =
  | ConMerged target ->
    ConMerged
      { target
        with
        info =
          val }
end
lang VarMergedAst =
  MergedBaseAst
  type VarMergedRecord =
    {info: Info, ident: {i: Info, v: Name}}
  syn Merged =
  | VarMerged VarMergedRecord
  sem get_Merged_info =
  | VarMerged target ->
    target.info
  sem set_Merged_info val =
  | VarMerged target ->
    VarMerged
      { target
        with
        info =
          val }
end
lang CharMergedAst =
  MergedBaseAst
  type CharMergedRecord =
    {val: {i: Info, v: Char}, info: Info}
  syn Merged =
  | CharMerged CharMergedRecord
  sem get_Merged_info =
  | CharMerged target ->
    target.info
  sem set_Merged_info val =
  | CharMerged target ->
    CharMerged
      { target
        with
        info =
          val }
end
lang IntMergedAst =
  MergedBaseAst
  type IntMergedRecord =
    {val: {i: Info, v: Int}, info: Info}
  syn Merged =
  | IntMerged IntMergedRecord
  sem get_Merged_info =
  | IntMerged target ->
    target.info
  sem set_Merged_info val =
  | IntMerged target ->
    IntMerged
      { target
        with
        info =
          val }
end
lang FloatMergedAst =
  MergedBaseAst
  type FloatMergedRecord =
    {val: {i: Info, v: Float}, info: Info}
  syn Merged =
  | FloatMerged FloatMergedRecord
  sem get_Merged_info =
  | FloatMerged target ->
    target.info
  sem set_Merged_info val =
  | FloatMerged target ->
    FloatMerged
      { target
        with
        info =
          val }
end
lang TrueMergedAst =
  MergedBaseAst
  type TrueMergedRecord =
    {info: Info}
  syn Merged =
  | TrueMerged TrueMergedRecord
  sem get_Merged_info =
  | TrueMerged target ->
    target.info
  sem set_Merged_info val =
  | TrueMerged target ->
    TrueMerged
      { target
        with
        info =
          val }
end
lang FalseMergedAst =
  MergedBaseAst
  type FalseMergedRecord =
    {info: Info}
  syn Merged =
  | FalseMerged FalseMergedRecord
  sem get_Merged_info =
  | FalseMerged target ->
    target.info
  sem set_Merged_info val =
  | FalseMerged target ->
    FalseMerged
      { target
        with
        info =
          val }
end
lang NeverMergedAst =
  MergedBaseAst
  type NeverMergedRecord =
    {info: Info}
  syn Merged =
  | NeverMerged NeverMergedRecord
  sem get_Merged_info =
  | NeverMerged target ->
    target.info
  sem set_Merged_info val =
  | NeverMerged target ->
    NeverMerged
      { target
        with
        info =
          val }
end
lang StringMergedAst =
  MergedBaseAst
  type StringMergedRecord =
    {val: {i: Info, v: String}, info: Info}
  syn Merged =
  | StringMerged StringMergedRecord
  sem get_Merged_info =
  | StringMerged target ->
    target.info
  sem set_Merged_info val =
  | StringMerged target ->
    StringMerged
      { target
        with
        info =
          val }
end
lang SequenceMergedAst =
  MergedBaseAst
  type SequenceMergedRecord =
    {tms: [Merged], info: Info}
  syn Merged =
  | SequenceMerged SequenceMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | SequenceMerged x ->
    match
      match
        let tms =
          x.tms
        in
        mapAccumL
          (lam acc1.
             lam x1: Merged.
               f
                 acc1
                 x1)
          acc
          tms
      with
        (acc, tms)
      in
      (acc, { x
          with
          tms =
            tms })
    with
      (acc, x)
    in
    (acc, SequenceMerged
        x)
  sem get_Merged_info =
  | SequenceMerged target ->
    target.info
  sem set_Merged_info val =
  | SequenceMerged target ->
    SequenceMerged
      { target
        with
        info =
          val }
end
lang RecordMergedAst =
  MergedBaseAst
  type RecordMergedRecord =
    {info: Info, fields: [{e: Option Merged, ty: Option Merged, label: {i: Info, v: String}}]}
  syn Merged =
  | RecordMerged RecordMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | RecordMerged x ->
    match
      match
        let fields =
          x.fields
        in
        mapAccumL
          (lam acc1.
             lam x1: {e: Option Merged, ty: Option Merged, label: {i: Info, v: String}}.
               match
                 let e =
                   x1.e
                 in
                 optionMapAccum
                   (lam acc2.
                      lam x2.
                        f
                          acc2
                          x2)
                   acc1
                   e
               with
                 (acc1, e)
               in
               match
                   let ty =
                     x1.ty
                   in
                   optionMapAccum
                     (lam acc3.
                        lam x3.
                          f
                            acc3
                            x3)
                     acc1
                     ty
                 with
                   (acc1, ty)
                 in
                 (acc1, { { x1
                       with
                       e =
                         e }
                     with
                     ty =
                       ty }))
          acc
          fields
      with
        (acc, fields)
      in
      (acc, { x
          with
          fields =
            fields })
    with
      (acc, x)
    in
    (acc, RecordMerged
        x)
  sem get_Merged_info =
  | RecordMerged target ->
    target.info
  sem set_Merged_info val =
  | RecordMerged target ->
    RecordMerged
      { target
        with
        info =
          val }
end
lang NotMergedAst =
  MergedBaseAst
  type NotMergedRecord =
    {info: Info, right: Merged}
  syn Merged =
  | NotMerged NotMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | NotMerged x ->
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
      in
      (acc, { x
          with
          right =
            right })
    with
      (acc, x)
    in
    (acc, NotMerged
        x)
  sem get_Merged_info =
  | NotMerged target ->
    target.info
  sem set_Merged_info val =
  | NotMerged target ->
    NotMerged
      { target
        with
        info =
          val }
end
lang OrMergedAst =
  MergedBaseAst
  type OrMergedRecord =
    {info: Info, left: Merged, right: Merged}
  syn Merged =
  | OrMerged OrMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | OrMerged x ->
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
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, OrMerged
        x)
  sem get_Merged_info =
  | OrMerged target ->
    target.info
  sem set_Merged_info val =
  | OrMerged target ->
    OrMerged
      { target
        with
        info =
          val }
end
lang AndMergedAst =
  MergedBaseAst
  type AndMergedRecord =
    {info: Info, left: Merged, right: Merged}
  syn Merged =
  | AndMerged AndMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | AndMerged x ->
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
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, AndMerged
        x)
  sem get_Merged_info =
  | AndMerged target ->
    target.info
  sem set_Merged_info val =
  | AndMerged target ->
    AndMerged
      { target
        with
        info =
          val }
end
lang ConcatMergedAst =
  MergedBaseAst
  type ConcatMergedRecord =
    {info: Info, left: Merged, right: Merged}
  syn Merged =
  | ConcatMerged ConcatMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | ConcatMerged x ->
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
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, ConcatMerged
        x)
  sem get_Merged_info =
  | ConcatMerged target ->
    target.info
  sem set_Merged_info val =
  | ConcatMerged target ->
    ConcatMerged
      { target
        with
        info =
          val }
end
lang WildMergedAst =
  MergedBaseAst
  type WildMergedRecord =
    {info: Info}
  syn Merged =
  | WildMerged WildMergedRecord
  sem get_Merged_info =
  | WildMerged target ->
    target.info
  sem set_Merged_info val =
  | WildMerged target ->
    WildMerged
      { target
        with
        info =
          val }
end
lang ArrowMergedAst =
  MergedBaseAst
  type ArrowMergedRecord =
    {info: Info, left: Merged, right: Merged}
  syn Merged =
  | ArrowMerged ArrowMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | ArrowMerged x ->
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
      in
      match
          let right =
            x.right
          in
          f
            acc
            right
        with
          (acc, right)
        in
        (acc, { { x
              with
              left =
                left }
            with
            right =
              right })
    with
      (acc, x)
    in
    (acc, ArrowMerged
        x)
  sem get_Merged_info =
  | ArrowMerged target ->
    target.info
  sem set_Merged_info val =
  | ArrowMerged target ->
    ArrowMerged
      { target
        with
        info =
          val }
end
lang AllMergedAst =
  MergedBaseAst
  type AllMergedRecord =
    {rec: Option Info, info: Info, ident: {i: Info, v: Name}, right: Merged}
  syn Merged =
  | AllMerged AllMergedRecord
  sem smapAccumL_Merged_Merged f acc =
  | AllMerged x ->
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
      in
      (acc, { x
          with
          right =
            right })
    with
      (acc, x)
    in
    (acc, AllMerged
        x)
  sem get_Merged_info =
  | AllMerged target ->
    target.info
  sem set_Merged_info val =
  | AllMerged target ->
    AllMerged
      { target
        with
        info =
          val }
end
lang BadMergedFileAst =
  MergedBaseAst
  type BadMergedFileRecord =
    {info: Info}
  syn MergedFile =
  | BadMergedFile BadMergedFileRecord
  sem get_MergedFile_info =
  | BadMergedFile target ->
    target.info
  sem set_MergedFile_info val =
  | BadMergedFile target ->
    BadMergedFile
      { target
        with
        info =
          val }
end
lang BadMergedTopAst =
  MergedBaseAst
  type BadMergedTopRecord =
    {info: Info}
  syn MergedTop =
  | BadMergedTop BadMergedTopRecord
  sem get_MergedTop_info =
  | BadMergedTop target ->
    target.info
  sem set_MergedTop_info val =
  | BadMergedTop target ->
    BadMergedTop
      { target
        with
        info =
          val }
end
lang BadMergedAst =
  MergedBaseAst
  type BadMergedRecord =
    {info: Info}
  syn Merged =
  | BadMerged BadMergedRecord
  sem get_Merged_info =
  | BadMerged target ->
    target.info
  sem set_Merged_info val =
  | BadMerged target ->
    BadMerged
      { target
        with
        info =
          val }
end
lang BadBinderAst =
  MergedBaseAst
  type BadBinderRecord =
    {info: Info}
  syn Binder =
  | BadBinder BadBinderRecord
  sem get_Binder_info =
  | BadBinder target ->
    target.info
  sem set_Binder_info val =
  | BadBinder target ->
    BadBinder
      { target
        with
        info =
          val }
end
lang MergedAst =
  TopsMergedFileAst
  + DefMergedTopAst
  + ExprMergedTopAst
  + IncludeMergedTopAst
  + TypeBinderAst
  + ConBinderAst
  + RecLetBinderAst
  + LetBinderAst
  + UseBinderAst
  + UtestBinderAst
  + ExternalBinderAst
  + ProjMergedAst
  + AppMergedAst
  + SemiMergedAst
  + RecordAddMergedAst
  + RecordSubMergedAst
  + RecordChangeMergedAst
  + BindMergedAst
  + LamMergedAst
  + MatchMergedAst
  + IfMergedAst
  + SwitchMergedAst
  + ConMergedAst
  + VarMergedAst
  + CharMergedAst
  + IntMergedAst
  + FloatMergedAst
  + TrueMergedAst
  + FalseMergedAst
  + NeverMergedAst
  + StringMergedAst
  + SequenceMergedAst
  + RecordMergedAst
  + NotMergedAst
  + OrMergedAst
  + AndMergedAst
  + ConcatMergedAst
  + WildMergedAst
  + ArrowMergedAst
  + AllMergedAst
  + BadMergedFileAst
  + BadMergedTopAst
  + BadMergedAst
  + BadBinderAst
end
lang MergedFileOpBase =
  MergedAst
  syn MergedFileOp lstyle rstyle =
  sem topAllowed_MergedFileOp : all lstyle. all rstyle. MergedFileOp lstyle rstyle -> Bool
sem topAllowed_MergedFileOp =
  | _ ->
    true
  sem leftAllowed_MergedFileOp : all lstyle. all style. all rstyle. {child: MergedFileOp lstyle rstyle, parent: MergedFileOp LOpen style} -> Bool
sem leftAllowed_MergedFileOp =
  | _ ->
    true
  sem rightAllowed_MergedFileOp : all style. all lstyle. all rstyle. {child: MergedFileOp lstyle rstyle, parent: MergedFileOp style ROpen} -> Bool
sem rightAllowed_MergedFileOp =
  | _ ->
    true
  sem groupingsAllowed_MergedFileOp : all lstyle. all rstyle. (MergedFileOp lstyle ROpen, MergedFileOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_MergedFileOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_MergedFileOp : all lstyle. all rstyle. MergedFileOp lstyle rstyle -> AllowedDirection
sem parenAllowed_MergedFileOp =
  | _ ->
    GEither
      {}
  sem getInfo_MergedFileOp : all lstyle. all rstyle. MergedFileOp lstyle rstyle -> Info
sem getInfo_MergedFileOp =
  sem getTerms_MergedFileOp : all lstyle. all rstyle. MergedFileOp lstyle rstyle -> [Info]
sem getTerms_MergedFileOp =
  sem unsplit_MergedFileOp : PermanentNode MergedFileOp -> (Info, MergedFile)
sem unsplit_MergedFileOp =
end
lang MergedTopOpBase =
  MergedAst
  syn MergedTopOp lstyle rstyle =
  sem topAllowed_MergedTopOp : all lstyle. all rstyle. MergedTopOp lstyle rstyle -> Bool
sem topAllowed_MergedTopOp =
  | _ ->
    true
  sem leftAllowed_MergedTopOp : all lstyle. all style. all rstyle. {child: MergedTopOp lstyle rstyle, parent: MergedTopOp LOpen style} -> Bool
sem leftAllowed_MergedTopOp =
  | _ ->
    true
  sem rightAllowed_MergedTopOp : all style. all lstyle. all rstyle. {child: MergedTopOp lstyle rstyle, parent: MergedTopOp style ROpen} -> Bool
sem rightAllowed_MergedTopOp =
  | _ ->
    true
  sem groupingsAllowed_MergedTopOp : all lstyle. all rstyle. (MergedTopOp lstyle ROpen, MergedTopOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_MergedTopOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_MergedTopOp : all lstyle. all rstyle. MergedTopOp lstyle rstyle -> AllowedDirection
sem parenAllowed_MergedTopOp =
  | _ ->
    GEither
      {}
  sem getInfo_MergedTopOp : all lstyle. all rstyle. MergedTopOp lstyle rstyle -> Info
sem getInfo_MergedTopOp =
  sem getTerms_MergedTopOp : all lstyle. all rstyle. MergedTopOp lstyle rstyle -> [Info]
sem getTerms_MergedTopOp =
  sem unsplit_MergedTopOp : PermanentNode MergedTopOp -> (Info, MergedTop)
sem unsplit_MergedTopOp =
end
lang MergedOpBase =
  MergedAst
  syn MergedOp lstyle rstyle =
  sem topAllowed_MergedOp : all lstyle. all rstyle. MergedOp lstyle rstyle -> Bool
sem topAllowed_MergedOp =
  | _ ->
    true
  sem leftAllowed_MergedOp : all lstyle. all style. all rstyle. {child: MergedOp lstyle rstyle, parent: MergedOp LOpen style} -> Bool
sem leftAllowed_MergedOp =
  | _ ->
    true
  sem rightAllowed_MergedOp : all style. all lstyle. all rstyle. {child: MergedOp lstyle rstyle, parent: MergedOp style ROpen} -> Bool
sem rightAllowed_MergedOp =
  | _ ->
    true
  sem groupingsAllowed_MergedOp : all lstyle. all rstyle. (MergedOp lstyle ROpen, MergedOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_MergedOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_MergedOp : all lstyle. all rstyle. MergedOp lstyle rstyle -> AllowedDirection
sem parenAllowed_MergedOp =
  | _ ->
    GEither
      {}
  sem getInfo_MergedOp : all lstyle. all rstyle. MergedOp lstyle rstyle -> Info
sem getInfo_MergedOp =
  sem getTerms_MergedOp : all lstyle. all rstyle. MergedOp lstyle rstyle -> [Info]
sem getTerms_MergedOp =
  sem unsplit_MergedOp : PermanentNode MergedOp -> (Info, Merged)
sem unsplit_MergedOp =
end
lang BinderOpBase =
  MergedAst
  syn BinderOp lstyle rstyle =
  sem topAllowed_BinderOp : all lstyle. all rstyle. BinderOp lstyle rstyle -> Bool
sem topAllowed_BinderOp =
  | _ ->
    true
  sem leftAllowed_BinderOp : all lstyle. all style. all rstyle. {child: BinderOp lstyle rstyle, parent: BinderOp LOpen style} -> Bool
sem leftAllowed_BinderOp =
  | _ ->
    true
  sem rightAllowed_BinderOp : all style. all lstyle. all rstyle. {child: BinderOp lstyle rstyle, parent: BinderOp style ROpen} -> Bool
sem rightAllowed_BinderOp =
  | _ ->
    true
  sem groupingsAllowed_BinderOp : all lstyle. all rstyle. (BinderOp lstyle ROpen, BinderOp LOpen rstyle) -> AllowedDirection
sem groupingsAllowed_BinderOp =
  | _ ->
    GEither
      {}
  sem parenAllowed_BinderOp : all lstyle. all rstyle. BinderOp lstyle rstyle -> AllowedDirection
sem parenAllowed_BinderOp =
  | _ ->
    GEither
      {}
  sem getInfo_BinderOp : all lstyle. all rstyle. BinderOp lstyle rstyle -> Info
sem getInfo_BinderOp =
  sem getTerms_BinderOp : all lstyle. all rstyle. BinderOp lstyle rstyle -> [Info]
sem getTerms_BinderOp =
  sem unsplit_BinderOp : PermanentNode BinderOp -> (Info, Binder)
sem unsplit_BinderOp =
end
lang TopsMergedFileOp =
  MergedFileOpBase
  + TopsMergedFileAst
  syn MergedFileOp lstyle rstyle =
  | TopsMergedFileOp {tops: [MergedTop], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedFileOp =
  | TopsMergedFileOp x ->
    x.__br_info
  sem getTerms_MergedFileOp =
  | TopsMergedFileOp x ->
    x.__br_terms
  sem unsplit_MergedFileOp =
  | AtomP {self = TopsMergedFileOp x} ->
    (x.__br_info, TopsMergedFile
      { tops =
          x.tops,
        info =
          x.__br_info })
end
lang DefMergedTopOp =
  MergedTopOpBase
  + DefMergedTopAst
  syn MergedTopOp lstyle rstyle =
  | DefMergedTopOp {b: [Binder], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedTopOp =
  | DefMergedTopOp x ->
    x.__br_info
  sem getTerms_MergedTopOp =
  | DefMergedTopOp x ->
    x.__br_terms
  sem unsplit_MergedTopOp =
  | AtomP {self = DefMergedTopOp x} ->
    (x.__br_info, DefMergedTop
      { info =
          x.__br_info,
        b =
          match
            x.b
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang ExprMergedTopOp =
  MergedTopOpBase
  + ExprMergedTopAst
  syn MergedTopOp lstyle rstyle =
  | ExprMergedTopOp {e: [Merged], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedTopOp =
  | ExprMergedTopOp x ->
    x.__br_info
  sem getTerms_MergedTopOp =
  | ExprMergedTopOp x ->
    x.__br_terms
  sem unsplit_MergedTopOp =
  | AtomP {self = ExprMergedTopOp x} ->
    (x.__br_info, ExprMergedTop
      { info =
          x.__br_info,
        e =
          match
            x.e
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang IncludeMergedTopOp =
  MergedTopOpBase
  + IncludeMergedTopAst
  syn MergedTopOp lstyle rstyle =
  | IncludeMergedTopOp {path: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedTopOp =
  | IncludeMergedTopOp x ->
    x.__br_info
  sem getTerms_MergedTopOp =
  | IncludeMergedTopOp x ->
    x.__br_terms
  sem unsplit_MergedTopOp =
  | AtomP {self = IncludeMergedTopOp x} ->
    (x.__br_info, IncludeMergedTop
      { info =
          x.__br_info,
        path =
          match
            x.path
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang TypeBinderOp =
  BinderOpBase
  + TypeBinderAst
  syn BinderOp lstyle rstyle =
  | TypeBinderOp {ident: [{i: Info, v: Name}], params: [{i: Info, v: Name}], tyIdent: [Merged], __br_info: Info, __br_terms: [Info]}
  sem getInfo_BinderOp =
  | TypeBinderOp x ->
    x.__br_info
  sem getTerms_BinderOp =
  | TypeBinderOp x ->
    x.__br_terms
  sem unsplit_BinderOp =
  | AtomP {self = TypeBinderOp x} ->
    (x.__br_info, TypeBinder
      { info =
          x.__br_info,
        params =
          x.params,
        tyIdent =
          match
            x.tyIdent
          with
            [ x1 ] ++ _
          then
            Some
              x1
          else
            None
              {},
        ident =
          match
            x.ident
          with
            [ x2 ] ++ _
          in
          x2 })
end
lang ConBinderOp =
  BinderOpBase
  + ConBinderAst
  syn BinderOp lstyle rstyle =
  | ConBinderOp {ident: [{i: Info, v: Name}], tyIdent: [Merged], __br_info: Info, __br_terms: [Info]}
  sem getInfo_BinderOp =
  | ConBinderOp x ->
    x.__br_info
  sem getTerms_BinderOp =
  | ConBinderOp x ->
    x.__br_terms
  sem unsplit_BinderOp =
  | AtomP {self = ConBinderOp x} ->
    (x.__br_info, ConBinder
      { info =
          x.__br_info,
        tyIdent =
          match
            x.tyIdent
          with
            [ x1 ] ++ _
          in
          x1,
        ident =
          match
            x.ident
          with
            [ x2 ] ++ _
          in
          x2 })
end
lang RecLetBinderOp =
  BinderOpBase
  + RecLetBinderAst
  syn BinderOp lstyle rstyle =
  | RecLetBinderOp {bindings: [{body: Merged, ident: {i: Info, v: Name}, tyAnnot: Option Merged}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_BinderOp =
  | RecLetBinderOp x ->
    x.__br_info
  sem getTerms_BinderOp =
  | RecLetBinderOp x ->
    x.__br_terms
  sem unsplit_BinderOp =
  | AtomP {self = RecLetBinderOp x} ->
    (x.__br_info, RecLetBinder
      { info =
          x.__br_info,
        bindings =
          x.bindings })
end
lang LetBinderOp =
  BinderOpBase
  + LetBinderAst
  syn BinderOp lstyle rstyle =
  | LetBinderOp {body: [Merged], ident: [{i: Info, v: Name}], tyAnnot: [Merged], __br_info: Info, __br_terms: [Info]}
  sem getInfo_BinderOp =
  | LetBinderOp x ->
    x.__br_info
  sem getTerms_BinderOp =
  | LetBinderOp x ->
    x.__br_terms
  sem unsplit_BinderOp =
  | AtomP {self = LetBinderOp x} ->
    (x.__br_info, LetBinder
      { info =
          x.__br_info,
        ident =
          match
            x.ident
          with
            [ x1 ] ++ _
          in
          x1,
        body =
          match
            x.body
          with
            [ x2 ] ++ _
          in
          x2,
        tyAnnot =
          match
            x.tyAnnot
          with
            [ x3 ] ++ _
          then
            Some
              x3
          else
            None
              {} })
end
lang UseBinderOp =
  BinderOpBase
  + UseBinderAst
  syn BinderOp lstyle rstyle =
  | UseBinderOp {n: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_BinderOp =
  | UseBinderOp x ->
    x.__br_info
  sem getTerms_BinderOp =
  | UseBinderOp x ->
    x.__br_terms
  sem unsplit_BinderOp =
  | AtomP {self = UseBinderOp x} ->
    (x.__br_info, UseBinder
      { info =
          x.__br_info,
        n =
          match
            x.n
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang UtestBinderOp =
  BinderOpBase
  + UtestBinderAst
  syn BinderOp lstyle rstyle =
  | UtestBinderOp {test: [Merged], tusing: [Merged], tonfail: [Merged], expected: [Merged], __br_info: Info, __br_terms: [Info]}
  sem getInfo_BinderOp =
  | UtestBinderOp x ->
    x.__br_info
  sem getTerms_BinderOp =
  | UtestBinderOp x ->
    x.__br_terms
  sem unsplit_BinderOp =
  | AtomP {self = UtestBinderOp x} ->
    (x.__br_info, UtestBinder
      { info =
          x.__br_info,
        tusing =
          match
            x.tusing
          with
            [ x1 ] ++ _
          then
            Some
              x1
          else
            None
              {},
        tonfail =
          match
            x.tonfail
          with
            [ x2 ] ++ _
          then
            Some
              x2
          else
            None
              {},
        test =
          match
            x.test
          with
            [ x3 ] ++ _
          in
          x3,
        expected =
          match
            x.expected
          with
            [ x4 ] ++ _
          in
          x4 })
end
lang ExternalBinderOp =
  BinderOpBase
  + ExternalBinderAst
  syn BinderOp lstyle rstyle =
  | ExternalBinderOp {ident: [{i: Info, v: Name}], effect: [Info], tyIdent: [Merged], __br_info: Info, __br_terms: [Info]}
  sem getInfo_BinderOp =
  | ExternalBinderOp x ->
    x.__br_info
  sem getTerms_BinderOp =
  | ExternalBinderOp x ->
    x.__br_terms
  sem unsplit_BinderOp =
  | AtomP {self = ExternalBinderOp x} ->
    (x.__br_info, ExternalBinder
      { info =
          x.__br_info,
        tyIdent =
          match
            x.tyIdent
          with
            [ x1 ] ++ _
          in
          x1,
        ident =
          match
            x.ident
          with
            [ x2 ] ++ _
          in
          x2,
        effect =
          match
            x.effect
          with
            [ x3 ] ++ _
          then
            Some
              x3
          else
            None
              {} })
end
lang ProjMergedOp =
  MergedOpBase
  + ProjMergedAst
  syn MergedOp lstyle rstyle =
  | ProjMergedOp {label: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | ProjMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | ProjMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | PostfixP {self = ProjMergedOp x, leftChildAlts = [ l ] ++ _} ->
    match
      unsplit_MergedOp
        l
    with
      (linfo, l)
    in
    let info =
        mergeInfo
          linfo
          x.__br_info
      in
      (info, ProjMerged
        { label =
            match
              x.label
            with
              [ x1 ] ++ _
            in
            x1,
          info =
            info,
          left =
            match
              [ l ]
            with
              [ x2 ] ++ _
            in
            x2 })
end
lang AppMergedOp =
  MergedOpBase
  + AppMergedAst
  sem groupingsAllowed_MergedOp =
  | (AppMergedOp _, AppMergedOp _) ->
    GLeft
      {}
  syn MergedOp lstyle rstyle =
  | AppMergedOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | AppMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | AppMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | InfixP {self = AppMergedOp x, leftChildAlts = [ l ] ++ _, rightChildAlts = [ r ] ++ _} ->
    match
      (unsplit_MergedOp
        l, unsplit_MergedOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, AppMerged
        { info =
            info,
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
lang SemiMergedOp =
  MergedOpBase
  + SemiMergedAst
  sem groupingsAllowed_MergedOp =
  | (SemiMergedOp _, SemiMergedOp _) ->
    GLeft
      {}
  syn MergedOp lstyle rstyle =
  | SemiMergedOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | SemiMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | SemiMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | InfixP {self = SemiMergedOp x, leftChildAlts = [ l ] ++ _, rightChildAlts = [ r ] ++ _} ->
    match
      (unsplit_MergedOp
        l, unsplit_MergedOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, SemiMerged
        { info =
            info,
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
lang RecordAddMergedOp =
  MergedOpBase
  + RecordAddMergedAst
  syn MergedOp lstyle rstyle =
  | RecordAddMergedOp {fields: [{ty: Option Merged, label: {i: Info, v: String}, value: Option Merged}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | RecordAddMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | RecordAddMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | PostfixP {self = RecordAddMergedOp x, leftChildAlts = [ l ] ++ _} ->
    match
      unsplit_MergedOp
        l
    with
      (linfo, l)
    in
    let info =
        mergeInfo
          linfo
          x.__br_info
      in
      (info, RecordAddMerged
        { info =
            info,
          fields =
            x.fields,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _
            in
            x1 })
end
lang RecordSubMergedOp =
  MergedOpBase
  + RecordSubMergedAst
  syn MergedOp lstyle rstyle =
  | RecordSubMergedOp {fields: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | RecordSubMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | RecordSubMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | PostfixP {self = RecordSubMergedOp x, leftChildAlts = [ l ] ++ _} ->
    match
      unsplit_MergedOp
        l
    with
      (linfo, l)
    in
    let info =
        mergeInfo
          linfo
          x.__br_info
      in
      (info, RecordSubMerged
        { info =
            info,
          fields =
            x.fields,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _
            in
            x1 })
end
lang RecordChangeMergedOp =
  MergedOpBase
  + RecordChangeMergedAst
  syn MergedOp lstyle rstyle =
  | RecordChangeMergedOp {fields: [{ty: Option Merged, label: {i: Info, v: String}, value: Option Merged}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | RecordChangeMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | RecordChangeMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | PostfixP {self = RecordChangeMergedOp x, leftChildAlts = [ l ] ++ _} ->
    match
      unsplit_MergedOp
        l
    with
      (linfo, l)
    in
    let info =
        mergeInfo
          linfo
          x.__br_info
      in
      (info, RecordChangeMerged
        { info =
            info,
          fields =
            x.fields,
          left =
            match
              [ l ]
            with
              [ x1 ] ++ _
            in
            x1 })
end
lang BindMergedOp =
  MergedOpBase
  + BindMergedAst
  syn MergedOp lstyle rstyle =
  | BindMergedOp {binder: [Binder], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | BindMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | BindMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | PrefixP {self = BindMergedOp x, rightChildAlts = [ r ] ++ _} ->
    match
      unsplit_MergedOp
        r
    with
      (rinfo, r)
    in
    let info =
        mergeInfo
          x.__br_info
          rinfo
      in
      (info, BindMerged
        { info =
            info,
          binder =
            match
              x.binder
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
lang LamMergedOp =
  MergedOpBase
  + LamMergedAst
  syn MergedOp lstyle rstyle =
  | LamMergedOp {ident: [{i: Info, v: Name}], tyAnnot: [Merged], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | LamMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | LamMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | PrefixP {self = LamMergedOp x, rightChildAlts = [ r ] ++ _} ->
    match
      unsplit_MergedOp
        r
    with
      (rinfo, r)
    in
    let info =
        mergeInfo
          x.__br_info
          rinfo
      in
      (info, LamMerged
        { info =
            info,
          ident =
            match
              x.ident
            with
              [ x1 ] ++ _
            then
              Some
                x1
            else
              None
                {},
          tyAnnot =
            match
              x.tyAnnot
            with
              [ x2 ] ++ _
            then
              Some
                x2
            else
              None
                {},
          right =
            match
              [ r ]
            with
              [ x3 ] ++ _
            in
            x3 })
end
lang MatchMergedOp =
  MergedOpBase
  + MatchMergedAst
  syn MergedOp lstyle rstyle =
  | MatchMergedOp {pat: [Merged], thn: [Merged], target: [Merged], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | MatchMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | MatchMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | PrefixP {self = MatchMergedOp x, rightChildAlts = [ r ] ++ _} ->
    match
      unsplit_MergedOp
        r
    with
      (rinfo, r)
    in
    let info =
        mergeInfo
          x.__br_info
          rinfo
      in
      (info, MatchMerged
        { info =
            info,
          pat =
            match
              x.pat
            with
              [ x1 ] ++ _
            in
            x1,
          thn =
            match
              x.thn
            with
              [ x2 ] ++ _
            in
            x2,
          target =
            match
              x.target
            with
              [ x3 ] ++ _
            in
            x3,
          els =
            match
              [ r ]
            with
              [ x4 ] ++ _
            in
            x4 })
end
lang IfMergedOp =
  MergedOpBase
  + IfMergedAst
  syn MergedOp lstyle rstyle =
  | IfMergedOp {thn: [Merged], target: [Merged], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | IfMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | IfMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | PrefixP {self = IfMergedOp x, rightChildAlts = [ r ] ++ _} ->
    match
      unsplit_MergedOp
        r
    with
      (rinfo, r)
    in
    let info =
        mergeInfo
          x.__br_info
          rinfo
      in
      (info, IfMerged
        { info =
            info,
          thn =
            match
              x.thn
            with
              [ x1 ] ++ _
            in
            x1,
          target =
            match
              x.target
            with
              [ x2 ] ++ _
            in
            x2,
          els =
            match
              [ r ]
            with
              [ x3 ] ++ _
            in
            x3 })
end
lang SwitchMergedOp =
  MergedOpBase
  + SwitchMergedAst
  syn MergedOp lstyle rstyle =
  | SwitchMergedOp {fail: [Info], cases: [{pat: Merged, thn: Merged, keyword: Info}], target: [Merged], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | SwitchMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | SwitchMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = SwitchMergedOp x} ->
    (x.__br_info, SwitchMerged
      { info =
          x.__br_info,
        target =
          match
            x.target
          with
            [ x1 ] ++ _
          in
          x1,
        cases =
          x.cases,
        fail =
          match
            x.fail
          with
            [ x2 ] ++ _
          in
          x2 })
end
lang ConMergedOp =
  MergedOpBase
  + ConMergedAst
  syn MergedOp lstyle rstyle =
  | ConMergedOp {ident: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | ConMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | ConMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = ConMergedOp x} ->
    (x.__br_info, ConMerged
      { info =
          x.__br_info,
        ident =
          match
            x.ident
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang VarMergedOp =
  MergedOpBase
  + VarMergedAst
  syn MergedOp lstyle rstyle =
  | VarMergedOp {ident: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | VarMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | VarMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = VarMergedOp x} ->
    (x.__br_info, VarMerged
      { info =
          x.__br_info,
        ident =
          match
            x.ident
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang CharMergedOp =
  MergedOpBase
  + CharMergedAst
  syn MergedOp lstyle rstyle =
  | CharMergedOp {val: [{i: Info, v: Char}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | CharMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | CharMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = CharMergedOp x} ->
    (x.__br_info, CharMerged
      { info =
          x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang IntMergedOp =
  MergedOpBase
  + IntMergedAst
  syn MergedOp lstyle rstyle =
  | IntMergedOp {val: [{i: Info, v: Int}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | IntMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | IntMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = IntMergedOp x} ->
    (x.__br_info, IntMerged
      { info =
          x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang FloatMergedOp =
  MergedOpBase
  + FloatMergedAst
  syn MergedOp lstyle rstyle =
  | FloatMergedOp {val: [{i: Info, v: Float}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | FloatMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | FloatMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = FloatMergedOp x} ->
    (x.__br_info, FloatMerged
      { info =
          x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang TrueMergedOp =
  MergedOpBase
  + TrueMergedAst
  syn MergedOp lstyle rstyle =
  | TrueMergedOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | TrueMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | TrueMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = TrueMergedOp x} ->
    (x.__br_info, TrueMerged
      { info =
          x.__br_info })
end
lang FalseMergedOp =
  MergedOpBase
  + FalseMergedAst
  syn MergedOp lstyle rstyle =
  | FalseMergedOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | FalseMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | FalseMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = FalseMergedOp x} ->
    (x.__br_info, FalseMerged
      { info =
          x.__br_info })
end
lang NeverMergedOp =
  MergedOpBase
  + NeverMergedAst
  syn MergedOp lstyle rstyle =
  | NeverMergedOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | NeverMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | NeverMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = NeverMergedOp x} ->
    (x.__br_info, NeverMerged
      { info =
          x.__br_info })
end
lang StringMergedOp =
  MergedOpBase
  + StringMergedAst
  syn MergedOp lstyle rstyle =
  | StringMergedOp {val: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | StringMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | StringMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = StringMergedOp x} ->
    (x.__br_info, StringMerged
      { info =
          x.__br_info,
        val =
          match
            x.val
          with
            [ x1 ] ++ _
          in
          x1 })
end
lang SequenceMergedOp =
  MergedOpBase
  + SequenceMergedAst
  syn MergedOp lstyle rstyle =
  | SequenceMergedOp {tms: [Merged], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | SequenceMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | SequenceMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = SequenceMergedOp x} ->
    (x.__br_info, SequenceMerged
      { info =
          x.__br_info,
        tms =
          x.tms })
end
lang RecordMergedOp =
  MergedOpBase
  + RecordMergedAst
  syn MergedOp lstyle rstyle =
  | RecordMergedOp {fields: [{e: Option Merged, ty: Option Merged, label: {i: Info, v: String}}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | RecordMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | RecordMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = RecordMergedOp x} ->
    (x.__br_info, RecordMerged
      { info =
          x.__br_info,
        fields =
          x.fields })
end
lang NotMergedOp =
  MergedOpBase
  + NotMergedAst
  syn MergedOp lstyle rstyle =
  | NotMergedOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | NotMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | NotMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | PrefixP {self = NotMergedOp x, rightChildAlts = [ r ] ++ _} ->
    match
      unsplit_MergedOp
        r
    with
      (rinfo, r)
    in
    let info =
        mergeInfo
          x.__br_info
          rinfo
      in
      (info, NotMerged
        { info =
            info,
          right =
            match
              [ r ]
            with
              [ x1 ] ++ _
            in
            x1 })
end
lang OrMergedOp =
  MergedOpBase
  + OrMergedAst
  sem groupingsAllowed_MergedOp =
  | (OrMergedOp _, OrMergedOp _) ->
    GLeft
      {}
  syn MergedOp lstyle rstyle =
  | OrMergedOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | OrMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | OrMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | InfixP {self = OrMergedOp x, leftChildAlts = [ l ] ++ _, rightChildAlts = [ r ] ++ _} ->
    match
      (unsplit_MergedOp
        l, unsplit_MergedOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, OrMerged
        { info =
            info,
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
lang AndMergedOp =
  MergedOpBase
  + AndMergedAst
  sem groupingsAllowed_MergedOp =
  | (AndMergedOp _, AndMergedOp _) ->
    GLeft
      {}
  syn MergedOp lstyle rstyle =
  | AndMergedOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | AndMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | AndMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | InfixP {self = AndMergedOp x, leftChildAlts = [ l ] ++ _, rightChildAlts = [ r ] ++ _} ->
    match
      (unsplit_MergedOp
        l, unsplit_MergedOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, AndMerged
        { info =
            info,
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
lang ConcatMergedOp =
  MergedOpBase
  + ConcatMergedAst
  sem groupingsAllowed_MergedOp =
  | (ConcatMergedOp _, ConcatMergedOp _) ->
    GLeft
      {}
  syn MergedOp lstyle rstyle =
  | ConcatMergedOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | ConcatMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | ConcatMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | InfixP {self = ConcatMergedOp x, leftChildAlts = [ l ] ++ _, rightChildAlts = [ r ] ++ _} ->
    match
      (unsplit_MergedOp
        l, unsplit_MergedOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, ConcatMerged
        { info =
            info,
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
lang WildMergedOp =
  MergedOpBase
  + WildMergedAst
  syn MergedOp lstyle rstyle =
  | WildMergedOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | WildMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | WildMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = WildMergedOp x} ->
    (x.__br_info, WildMerged
      { info =
          x.__br_info })
end
lang ArrowMergedOp =
  MergedOpBase
  + ArrowMergedAst
  sem groupingsAllowed_MergedOp =
  | (ArrowMergedOp _, ArrowMergedOp _) ->
    GRight
      {}
  syn MergedOp lstyle rstyle =
  | ArrowMergedOp {__br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | ArrowMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | ArrowMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | InfixP {self = ArrowMergedOp x, leftChildAlts = [ l ] ++ _, rightChildAlts = [ r ] ++ _} ->
    match
      (unsplit_MergedOp
        l, unsplit_MergedOp
        r)
    with
      ((linfo, l), (rinfo, r))
    in
    let info =
        foldl
          mergeInfo
          linfo
          [ x.__br_info,
            rinfo ]
      in
      (info, ArrowMerged
        { info =
            info,
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
lang AllMergedOp =
  MergedOpBase
  + AllMergedAst
  syn MergedOp lstyle rstyle =
  | AllMergedOp {rec: [Info], ident: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | AllMergedOp x ->
    x.__br_info
  sem getTerms_MergedOp =
  | AllMergedOp x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | PrefixP {self = AllMergedOp x, rightChildAlts = [ r ] ++ _} ->
    match
      unsplit_MergedOp
        r
    with
      (rinfo, r)
    in
    let info =
        mergeInfo
          x.__br_info
          rinfo
      in
      (info, AllMerged
        { info =
            info,
          ident =
            match
              x.ident
            with
              [ x1 ] ++ _
            in
            x1,
          rec =
            match
              x.rec
            with
              [ x2 ] ++ _
            then
              Some
                x2
            else
              None
                {},
          right =
            match
              [ r ]
            with
              [ x3 ] ++ _
            in
            x3 })
end
lang MergedGrouping =
  MergedOpBase
  syn MergedOp lstyle rstyle =
  | MergedGrouping {inner: Merged, __br_info: Info, __br_terms: [Info]}
  sem getInfo_MergedOp =
  | MergedGrouping x ->
    x.__br_info
  sem getTerms_MergedOp =
  | MergedGrouping x ->
    x.__br_terms
  sem unsplit_MergedOp =
  | AtomP {self = MergedGrouping x} ->
    (x.__br_info, x.inner)
end
lang ParseMerged =
  TopsMergedFileOp
  + DefMergedTopOp
  + ExprMergedTopOp
  + IncludeMergedTopOp
  + TypeBinderOp
  + ConBinderOp
  + RecLetBinderOp
  + LetBinderOp
  + UseBinderOp
  + UtestBinderOp
  + ExternalBinderOp
  + ProjMergedOp
  + AppMergedOp
  + SemiMergedOp
  + RecordAddMergedOp
  + RecordSubMergedOp
  + RecordChangeMergedOp
  + BindMergedOp
  + LamMergedOp
  + MatchMergedOp
  + IfMergedOp
  + SwitchMergedOp
  + ConMergedOp
  + VarMergedOp
  + CharMergedOp
  + IntMergedOp
  + FloatMergedOp
  + TrueMergedOp
  + FalseMergedOp
  + NeverMergedOp
  + StringMergedOp
  + SequenceMergedOp
  + RecordMergedOp
  + NotMergedOp
  + OrMergedOp
  + AndMergedOp
  + ConcatMergedOp
  + WildMergedOp
  + ArrowMergedOp
  + AllMergedOp
  + MergedGrouping
  + BadMergedFileAst
  + BadMergedTopAst
  + BadMergedAst
  + BadBinderAst
  + LL1Parser
  + CharTokenParser
  + UIntTokenParser
  + ErrorTokenParser
  + WhitespaceParser
  + LIdentTokenParser
  + LineCommentParser
  + StringTokenParser
  + UFloatTokenParser
  + UIdentTokenParser
  + OperatorTokenParser
  + MultilineCommentParser
  sem groupingsAllowed_MergedFileOp =
  sem groupingsAllowed_MergedTopOp =
  sem groupingsAllowed_MergedOp =
  | (AppMergedOp _, ProjMergedOp _) ->
    GRight
      {}
  | (SemiMergedOp _, ProjMergedOp _) ->
    GRight
      {}
  | (BindMergedOp _, ProjMergedOp _) ->
    GRight
      {}
  | (LamMergedOp _, ProjMergedOp _) ->
    GRight
      {}
  | (MatchMergedOp _, ProjMergedOp _) ->
    GRight
      {}
  | (IfMergedOp _, ProjMergedOp _) ->
    GRight
      {}
  | (AppMergedOp _, SemiMergedOp _) ->
    GLeft
      {}
  | (SemiMergedOp _, AppMergedOp _) ->
    GRight
      {}
  | (AppMergedOp _, RecordAddMergedOp _) ->
    GLeft
      {}
  | (AppMergedOp _, RecordSubMergedOp _) ->
    GLeft
      {}
  | (AppMergedOp _, RecordChangeMergedOp _) ->
    GLeft
      {}
  | (BindMergedOp _, AppMergedOp _) ->
    GRight
      {}
  | (LamMergedOp _, AppMergedOp _) ->
    GRight
      {}
  | (MatchMergedOp _, AppMergedOp _) ->
    GRight
      {}
  | (IfMergedOp _, AppMergedOp _) ->
    GRight
      {}
  | (AppMergedOp _, ArrowMergedOp _) ->
    GLeft
      {}
  | (ArrowMergedOp _, AppMergedOp _) ->
    GRight
      {}
  | (AllMergedOp _, AppMergedOp _) ->
    GRight
      {}
  | (SemiMergedOp _, RecordAddMergedOp _) ->
    GLeft
      {}
  | (SemiMergedOp _, RecordSubMergedOp _) ->
    GLeft
      {}
  | (SemiMergedOp _, RecordChangeMergedOp _) ->
    GLeft
      {}
  | (BindMergedOp _, SemiMergedOp _) ->
    GRight
      {}
  | (LamMergedOp _, SemiMergedOp _) ->
    GRight
      {}
  | (MatchMergedOp _, SemiMergedOp _) ->
    GRight
      {}
  | (IfMergedOp _, SemiMergedOp _) ->
    GRight
      {}
  | (BindMergedOp _, RecordAddMergedOp _) ->
    GRight
      {}
  | (LamMergedOp _, RecordAddMergedOp _) ->
    GRight
      {}
  | (MatchMergedOp _, RecordAddMergedOp _) ->
    GRight
      {}
  | (IfMergedOp _, RecordAddMergedOp _) ->
    GRight
      {}
  | (ArrowMergedOp _, RecordAddMergedOp _) ->
    GRight
      {}
  | (AllMergedOp _, RecordAddMergedOp _) ->
    GRight
      {}
  | (BindMergedOp _, RecordSubMergedOp _) ->
    GRight
      {}
  | (LamMergedOp _, RecordSubMergedOp _) ->
    GRight
      {}
  | (MatchMergedOp _, RecordSubMergedOp _) ->
    GRight
      {}
  | (IfMergedOp _, RecordSubMergedOp _) ->
    GRight
      {}
  | (BindMergedOp _, RecordChangeMergedOp _) ->
    GRight
      {}
  | (LamMergedOp _, RecordChangeMergedOp _) ->
    GRight
      {}
  | (MatchMergedOp _, RecordChangeMergedOp _) ->
    GRight
      {}
  | (IfMergedOp _, RecordChangeMergedOp _) ->
    GRight
      {}
  | (NotMergedOp _, OrMergedOp _) ->
    GLeft
      {}
  | (NotMergedOp _, AndMergedOp _) ->
    GLeft
      {}
  | (AllMergedOp _, ArrowMergedOp _) ->
    GRight
      {}
  sem groupingsAllowed_BinderOp =
end
let _table =
  use ParseMerged
  in
  let target =
    genParsingTable
      (let #var"MergedFile" =
         nameSym
           "MergedFile"
       in
       let #var"MergedTop" =
         nameSym
           "MergedTop"
       in
       let #var"Merged" =
         nameSym
           "Merged"
       in
       let #var"Binder" =
         nameSym
           "Binder"
       in
       let #var"MergedFilePostfix" =
         nameSym
           "MergedFilePostfix"
       in
       let #var"MergedFilePrefix" =
         nameSym
           "MergedFilePrefix"
       in
       let #var"MergedFileInfix" =
         nameSym
           "MergedFileInfix"
       in
       let #var"MergedFileAtom" =
         nameSym
           "MergedFileAtom"
       in
       let #var"MergedTopPostfix" =
         nameSym
           "MergedTopPostfix"
       in
       let #var"MergedTopPrefix" =
         nameSym
           "MergedTopPrefix"
       in
       let #var"MergedTopInfix" =
         nameSym
           "MergedTopInfix"
       in
       let #var"MergedTopAtom" =
         nameSym
           "MergedTopAtom"
       in
       let #var"MergedPostfix" =
         nameSym
           "MergedPostfix"
       in
       let #var"MergedPrefix" =
         nameSym
           "MergedPrefix"
       in
       let #var"MergedInfix" =
         nameSym
           "MergedInfix"
       in
       let #var"MergedAtom" =
         nameSym
           "MergedAtom"
       in
       let #var"BinderPostfix" =
         nameSym
           "BinderPostfix"
       in
       let #var"BinderPrefix" =
         nameSym
           "BinderPrefix"
       in
       let #var"BinderInfix" =
         nameSym
           "BinderInfix"
       in
       let #var"BinderAtom" =
         nameSym
           "BinderAtom"
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
       let alt2 =
         nameSym
           "alt"
       in
       let kleene2 =
         nameSym
           "kleene"
       in
       let alt3 =
         nameSym
           "alt"
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
       let alt8 =
         nameSym
           "alt"
       in
       let alt9 =
         nameSym
           "alt"
       in
       let alt10 =
         nameSym
           "alt"
       in
       let kleene3 =
         nameSym
           "kleene"
       in
       let alt11 =
         nameSym
           "alt"
       in
       let kleene4 =
         nameSym
           "kleene"
       in
       let alt12 =
         nameSym
           "alt"
       in
       let alt13 =
         nameSym
           "alt"
       in
       let alt14 =
         nameSym
           "alt"
       in
       let alt15 =
         nameSym
           "alt"
       in
       let alt16 =
         nameSym
           "alt"
       in
       let kleene5 =
         nameSym
           "kleene"
       in
       let alt17 =
         nameSym
           "alt"
       in
       let alt18 =
         nameSym
           "alt"
       in
       let kleene6 =
         nameSym
           "kleene"
       in
       let kleene7 =
         nameSym
           "kleene"
       in
       let alt19 =
         nameSym
           "alt"
       in
       let alt20 =
         nameSym
           "alt"
       in
       let alt21 =
         nameSym
           "alt"
       in
       let alt22 =
         nameSym
           "alt"
       in
       let alt23 =
         nameSym
           "alt"
       in
       let kleene8 =
         nameSym
           "kleene"
       in
       let alt24 =
         nameSym
           "alt"
       in
       let alt25 =
         nameSym
           "alt"
       in
       let #var"MergedFile_lclosed" =
         nameSym
           "MergedFile_lclosed"
       in
       let #var"MergedFile_lopen" =
         nameSym
           "MergedFile_lopen"
       in
       let #var"MergedTop_lclosed" =
         nameSym
           "MergedTop_lclosed"
       in
       let #var"MergedTop_lopen" =
         nameSym
           "MergedTop_lopen"
       in
       let #var"Merged_lclosed" =
         nameSym
           "Merged_lclosed"
       in
       let #var"Merged_lopen" =
         nameSym
           "Merged_lopen"
       in
       let #var"Binder_lclosed" =
         nameSym
           "Binder_lclosed"
       in
       let #var"Binder_lopen" =
         nameSym
           "Binder_lopen"
       in
       { start =
           #var"MergedFile",
         productions =
           let config =
             { parenAllowed =
                 #frozen"parenAllowed_MergedFileOp",
               topAllowed =
                 #frozen"topAllowed_MergedFileOp",
               leftAllowed =
                 #frozen"leftAllowed_MergedFileOp",
               rightAllowed =
                 #frozen"rightAllowed_MergedFileOp",
               groupingsAllowed =
                 #frozen"groupingsAllowed_MergedFileOp" }
           in
           let reportConfig =
             { parenAllowed =
                 #frozen"parenAllowed_MergedFileOp",
               topAllowed =
                 #frozen"topAllowed_MergedFileOp",
               terminalInfos =
                 #frozen"getTerms_MergedFileOp",
               getInfo =
                 #frozen"getInfo_MergedFileOp",
               lpar =
                 "(",
               rpar =
                 ")" }
           in
           let addMergedFileOpAtom =
             lam #var"".
               lam x57.
                 lam st.
                   optionMap
                     (breakableAddAtom
                        config
                        x57)
                     st
           in
           let addMergedFileOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x57.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddInfix
                         config
                         x57
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_MergedFileOp
                                 x57, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addMergedFileOpPrefix =
             lam #var"".
               lam x57.
                 lam st.
                   optionMap
                     (breakableAddPrefix
                        config
                        x57)
                     st
           in
           let addMergedFileOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x57.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddPostfix
                         config
                         x57
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_MergedFileOp
                                 x57, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeMergedFileOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res111 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse
                            config
                            st
                        with
                          Some (tops & ([ top ] ++ _))
                        then
                          let errs =
                            breakableDefaultHighlight
                              reportConfig
                              p.content
                              tops
                          in
                          let res111 =
                            unsplit_MergedFileOp
                              top
                          in
                          match
                            null
                              errs
                          with
                            true
                          then
                            Some
                              res111
                          else
                            (modref
                                 p.errors
                                 (concat
                                    (deref
                                       p.errors)
                                    errs))
                            ; Some
                              (res111.0, BadMergedFile
                                { info =
                                    res111.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref
                                     p.errors)
                                  (NoInfo
                                    {}, "Unfinished MergedFile")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadMergedFile
                     { info =
                         NoInfo
                           {} })
                   res111
           in
           let config1 =
             { parenAllowed =
                 #frozen"parenAllowed_MergedTopOp",
               topAllowed =
                 #frozen"topAllowed_MergedTopOp",
               leftAllowed =
                 #frozen"leftAllowed_MergedTopOp",
               rightAllowed =
                 #frozen"rightAllowed_MergedTopOp",
               groupingsAllowed =
                 #frozen"groupingsAllowed_MergedTopOp" }
           in
           let reportConfig1 =
             { parenAllowed =
                 #frozen"parenAllowed_MergedTopOp",
               topAllowed =
                 #frozen"topAllowed_MergedTopOp",
               terminalInfos =
                 #frozen"getTerms_MergedTopOp",
               getInfo =
                 #frozen"getInfo_MergedTopOp",
               lpar =
                 "(",
               rpar =
                 ")" }
           in
           let addMergedTopOpAtom =
             lam #var"".
               lam x57.
                 lam st.
                   optionMap
                     (breakableAddAtom
                        config1
                        x57)
                     st
           in
           let addMergedTopOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x57.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddInfix
                         config1
                         x57
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_MergedTopOp
                                 x57, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addMergedTopOpPrefix =
             lam #var"".
               lam x57.
                 lam st.
                   optionMap
                     (breakableAddPrefix
                        config1
                        x57)
                     st
           in
           let addMergedTopOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x57.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddPostfix
                         config1
                         x57
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_MergedTopOp
                                 x57, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeMergedTopOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res111 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse
                            config1
                            st
                        with
                          Some (tops & ([ top ] ++ _))
                        then
                          let errs =
                            breakableDefaultHighlight
                              reportConfig1
                              p.content
                              tops
                          in
                          let res111 =
                            unsplit_MergedTopOp
                              top
                          in
                          match
                            null
                              errs
                          with
                            true
                          then
                            Some
                              res111
                          else
                            (modref
                                 p.errors
                                 (concat
                                    (deref
                                       p.errors)
                                    errs))
                            ; Some
                              (res111.0, BadMergedTop
                                { info =
                                    res111.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref
                                     p.errors)
                                  (NoInfo
                                    {}, "Unfinished MergedTop")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadMergedTop
                     { info =
                         NoInfo
                           {} })
                   res111
           in
           let config2 =
             { parenAllowed =
                 #frozen"parenAllowed_MergedOp",
               topAllowed =
                 #frozen"topAllowed_MergedOp",
               leftAllowed =
                 #frozen"leftAllowed_MergedOp",
               rightAllowed =
                 #frozen"rightAllowed_MergedOp",
               groupingsAllowed =
                 #frozen"groupingsAllowed_MergedOp" }
           in
           let reportConfig2 =
             { parenAllowed =
                 #frozen"parenAllowed_MergedOp",
               topAllowed =
                 #frozen"topAllowed_MergedOp",
               terminalInfos =
                 #frozen"getTerms_MergedOp",
               getInfo =
                 #frozen"getInfo_MergedOp",
               lpar =
                 "(",
               rpar =
                 ")" }
           in
           let addMergedOpAtom =
             lam #var"".
               lam x57.
                 lam st.
                   optionMap
                     (breakableAddAtom
                        config2
                        x57)
                     st
           in
           let addMergedOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x57.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddInfix
                         config2
                         x57
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_MergedOp
                                 x57, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addMergedOpPrefix =
             lam #var"".
               lam x57.
                 lam st.
                   optionMap
                     (breakableAddPrefix
                        config2
                        x57)
                     st
           in
           let addMergedOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x57.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddPostfix
                         config2
                         x57
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_MergedOp
                                 x57, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeMergedOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res111 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse
                            config2
                            st
                        with
                          Some (tops & ([ top ] ++ _))
                        then
                          let errs =
                            breakableDefaultHighlight
                              reportConfig2
                              p.content
                              tops
                          in
                          let res111 =
                            unsplit_MergedOp
                              top
                          in
                          match
                            null
                              errs
                          with
                            true
                          then
                            Some
                              res111
                          else
                            (modref
                                 p.errors
                                 (concat
                                    (deref
                                       p.errors)
                                    errs))
                            ; Some
                              (res111.0, BadMerged
                                { info =
                                    res111.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref
                                     p.errors)
                                  (NoInfo
                                    {}, "Unfinished Merged")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadMerged
                     { info =
                         NoInfo
                           {} })
                   res111
           in
           let config3 =
             { parenAllowed =
                 #frozen"parenAllowed_BinderOp",
               topAllowed =
                 #frozen"topAllowed_BinderOp",
               leftAllowed =
                 #frozen"leftAllowed_BinderOp",
               rightAllowed =
                 #frozen"rightAllowed_BinderOp",
               groupingsAllowed =
                 #frozen"groupingsAllowed_BinderOp" }
           in
           let reportConfig3 =
             { parenAllowed =
                 #frozen"parenAllowed_BinderOp",
               topAllowed =
                 #frozen"topAllowed_BinderOp",
               terminalInfos =
                 #frozen"getTerms_BinderOp",
               getInfo =
                 #frozen"getInfo_BinderOp",
               lpar =
                 "(",
               rpar =
                 ")" }
           in
           let addBinderOpAtom =
             lam #var"".
               lam x57.
                 lam st.
                   optionMap
                     (breakableAddAtom
                        config3
                        x57)
                     st
           in
           let addBinderOpInfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x57.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddInfix
                         config3
                         x57
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_BinderOp
                                 x57, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let addBinderOpPrefix =
             lam #var"".
               lam x57.
                 lam st.
                   optionMap
                     (breakableAddPrefix
                        config3
                        x57)
                     st
           in
           let addBinderOpPostfix =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam x57.
                 lam st.
                   match
                     st
                   with
                     Some st
                   then
                     let st =
                       breakableAddPostfix
                         config3
                         x57
                         st
                     in
                     (match
                          st
                        with
                          None _
                        then
                          modref
                            p.errors
                            (snoc
                               (deref
                                  p.errors)
                               (getInfo_BinderOp
                                 x57, "Invalid input"))
                        else
                          {})
                     ; st
                   else
                     None
                       {}
           in
           let finalizeBinderOp =
             lam p: {errors: Ref [(Info, [Char])], content: String}.
               lam st.
                 let res111 =
                   optionBind
                     st
                     (lam st.
                        match
                          breakableFinalizeParse
                            config3
                            st
                        with
                          Some (tops & ([ top ] ++ _))
                        then
                          let errs =
                            breakableDefaultHighlight
                              reportConfig3
                              p.content
                              tops
                          in
                          let res111 =
                            unsplit_BinderOp
                              top
                          in
                          match
                            null
                              errs
                          with
                            true
                          then
                            Some
                              res111
                          else
                            (modref
                                 p.errors
                                 (concat
                                    (deref
                                       p.errors)
                                    errs))
                            ; Some
                              (res111.0, BadBinder
                                { info =
                                    res111.0 })
                        else
                          (modref
                               p.errors
                               (snoc
                                  (deref
                                     p.errors)
                                  (NoInfo
                                    {}, "Unfinished Binder")))
                          ; None
                            {})
                 in
                 optionGetOr
                   (NoInfo
                     {}, BadBinder
                     { info =
                         NoInfo
                           {} })
                   res111
           in
           [ { nt =
                 kleene,
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedTop",
                   ntSym
                     kleene ],
               action =
                 lam state: {errors: Ref [(Info, [Char])], content: String}.
                   lam res.
                     match
                       res
                     with
                       [ UserSym ntVal,
                         UserSym val1 ]
                     in
                     let ntVal: (Info, MergedTop) =
                         fromDyn
                           ntVal
                       in
                       let val1: {tops: [MergedTop], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val1
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               ntVal.0
                               val1.__br_info,
                           __br_terms =
                             val1.__br_terms,
                           tops =
                             concat
                               [ ntVal.1 ]
                               val1.tops } },
             { nt =
                 kleene,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state1: {errors: Ref [(Info, [Char])], content: String}.
                   lam res1.
                     match
                       res1
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           tops =
                             "" } },
             { nt =
                 #var"MergedFileAtom",
               label =
                 {},
               rhs =
                 [ ntSym
                     kleene ],
               action =
                 lam state2: {errors: Ref [(Info, [Char])], content: String}.
                   lam res2.
                     match
                       res2
                     with
                       [ UserSym val1 ]
                     in
                     let val1: {tops: [MergedTop], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val1
                       in
                       asDyn
                         (TopsMergedFileOp
                            { __br_info =
                                val1.__br_info,
                              __br_terms =
                                val1.__br_terms,
                              tops =
                                val1.tops }) },
             { nt =
                 #var"MergedTopAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "def",
                   ntSym
                     #var"Binder" ],
               action =
                 lam state3: {errors: Ref [(Info, [Char])], content: String}.
                   lam res3.
                     match
                       res3
                     with
                       [ LitParsed l,
                         UserSym ntVal1 ]
                     in
                     let ntVal1: (Info, Binder) =
                         fromDyn
                           ntVal1
                       in
                       asDyn
                         (DefMergedTopOp
                            { __br_info =
                                mergeInfo
                                  l.info
                                  ntVal1.0,
                              __br_terms =
                                [ l.info ],
                              b =
                                [ ntVal1.1 ] }) },
             { nt =
                 #var"MergedTopAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "expr",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state4: {errors: Ref [(Info, [Char])], content: String}.
                   lam res4.
                     match
                       res4
                     with
                       [ LitParsed l1,
                         UserSym ntVal2 ]
                     in
                     let ntVal2: (Info, Merged) =
                         fromDyn
                           ntVal2
                       in
                       asDyn
                         (ExprMergedTopOp
                            { __br_info =
                                mergeInfo
                                  l1.info
                                  ntVal2.0,
                              __br_terms =
                                [ l1.info ],
                              e =
                                [ ntVal2.1 ] }) },
             { nt =
                 #var"MergedTopAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "include",
                   tokSym
                     (StringRepr
                        {}) ],
               action =
                 lam state5: {errors: Ref [(Info, [Char])], content: String}.
                   lam res5.
                     match
                       res5
                     with
                       [ LitParsed l2,
                         TokParsed (StringTok x) ]
                     in
                     asDyn
                         (IncludeMergedTopOp
                            { __br_info =
                                mergeInfo
                                  l2.info
                                  x.info,
                              __br_terms =
                                concat
                                  [ l2.info ]
                                  [ x.info ],
                              path =
                                [ { v =
                                      x.val,
                                    i =
                                      x.info } ] }) },
             { nt =
                 kleene1,
               label =
                 {},
               rhs =
                 [ tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     kleene1 ],
               action =
                 lam state6: {errors: Ref [(Info, [Char])], content: String}.
                   lam res6.
                     match
                       res6
                     with
                       [ TokParsed (LIdentTok x1),
                         UserSym val2 ]
                     in
                     let val2: {params: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val2
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               x1.info
                               val2.__br_info,
                           __br_terms =
                             concat
                               [ x1.info ]
                               val2.__br_terms,
                           params =
                             concat
                               [ { v =
                                     nameNoSym
                                       x1.val,
                                   i =
                                     x1.info } ]
                               val2.params } },
             { nt =
                 kleene1,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state7: {errors: Ref [(Info, [Char])], content: String}.
                   lam res7.
                     match
                       res7
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           params =
                             "" } },
             { nt =
                 alt,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state8: {errors: Ref [(Info, [Char])], content: String}.
                   lam res8.
                     match
                       res8
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           tyIdent =
                             "" } },
             { nt =
                 alt,
               label =
                 {},
               rhs =
                 [ litSym
                     "=",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state9: {errors: Ref [(Info, [Char])], content: String}.
                   lam res9.
                     match
                       res9
                     with
                       [ LitParsed l3,
                         UserSym ntVal3 ]
                     in
                     let ntVal3: (Info, Merged) =
                         fromDyn
                           ntVal3
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l3.info
                               ntVal3.0,
                           __br_terms =
                             [ l3.info ],
                           tyIdent =
                             [ ntVal3.1 ] } },
             { nt =
                 #var"BinderAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "type",
                   tokSym
                     (UIdentRepr
                        {}),
                   ntSym
                     kleene1,
                   ntSym
                     alt ],
               action =
                 lam state10: {errors: Ref [(Info, [Char])], content: String}.
                   lam res10.
                     match
                       res10
                     with
                       [ LitParsed l4,
                         TokParsed (UIdentTok x2),
                         UserSym val2,
                         UserSym val3 ]
                     in
                     let val2: {params: [{i: Info, v: Name}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val2
                       in
                       let val3: {tyIdent: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val3
                       in
                       asDyn
                         (TypeBinderOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l4.info
                                  [ x2.info,
                                    val2.__br_info,
                                    val3.__br_info ],
                              __br_terms =
                                join
                                  [ [ l4.info ],
                                    [ x2.info ],
                                    val2.__br_terms,
                                    val3.__br_terms ],
                              params =
                                val2.params,
                              tyIdent =
                                val3.tyIdent,
                              ident =
                                [ { v =
                                      nameNoSym
                                        x2.val,
                                    i =
                                      x2.info } ] }) },
             { nt =
                 #var"BinderAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "con",
                   tokSym
                     (UIdentRepr
                        {}),
                   litSym
                     ":",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state11: {errors: Ref [(Info, [Char])], content: String}.
                   lam res11.
                     match
                       res11
                     with
                       [ LitParsed l5,
                         TokParsed (UIdentTok x3),
                         LitParsed l6,
                         UserSym ntVal4 ]
                     in
                     let ntVal4: (Info, Merged) =
                         fromDyn
                           ntVal4
                       in
                       asDyn
                         (ConBinderOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l5.info
                                  [ x3.info,
                                    l6.info,
                                    ntVal4.0 ],
                              __br_terms =
                                join
                                  [ [ l5.info ],
                                    [ x3.info ],
                                    [ l6.info ] ],
                              tyIdent =
                                [ ntVal4.1 ],
                              ident =
                                [ { v =
                                      nameNoSym
                                        x3.val,
                                    i =
                                      x3.info } ] }) },
             { nt =
                 alt1,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state12: {errors: Ref [(Info, [Char])], content: String}.
                   lam res12.
                     match
                       res12
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           tyAnnot =
                             "" } },
             { nt =
                 alt1,
               label =
                 {},
               rhs =
                 [ litSym
                     ":",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state13: {errors: Ref [(Info, [Char])], content: String}.
                   lam res13.
                     match
                       res13
                     with
                       [ LitParsed l7,
                         UserSym ntVal5 ]
                     in
                     let ntVal5: (Info, Merged) =
                         fromDyn
                           ntVal5
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l7.info
                               ntVal5.0,
                           __br_terms =
                             [ l7.info ],
                           tyAnnot =
                             [ ntVal5.1 ] } },
             { nt =
                 alt2,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state14: {errors: Ref [(Info, [Char])], content: String}.
                   lam res14.
                     match
                       res14
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           tyAnnot =
                             "" } },
             { nt =
                 alt2,
               label =
                 {},
               rhs =
                 [ litSym
                     ":",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state15: {errors: Ref [(Info, [Char])], content: String}.
                   lam res15.
                     match
                       res15
                     with
                       [ LitParsed l8,
                         UserSym ntVal6 ]
                     in
                     let ntVal6: (Info, Merged) =
                         fromDyn
                           ntVal6
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l8.info
                               ntVal6.0,
                           __br_terms =
                             [ l8.info ],
                           tyAnnot =
                             [ ntVal6.1 ] } },
             { nt =
                 kleene2,
               label =
                 {},
               rhs =
                 [ litSym
                     "letf",
                   tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     alt2,
                   litSym
                     "=",
                   ntSym
                     #var"Merged",
                   ntSym
                     kleene2 ],
               action =
                 lam state16: {errors: Ref [(Info, [Char])], content: String}.
                   lam res16.
                     match
                       res16
                     with
                       [ LitParsed l9,
                         TokParsed (LIdentTok x4),
                         UserSym val4,
                         LitParsed l10,
                         UserSym ntVal7,
                         UserSym val5 ]
                     in
                     let val4: {tyAnnot: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val4
                       in
                       let ntVal7: (Info, Merged) =
                         fromDyn
                           ntVal7
                       in
                       let val5: {bindings: [{body: Merged, ident: {i: Info, v: Name}, tyAnnot: Option Merged}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val5
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l9.info
                               [ x4.info,
                                 val4.__br_info,
                                 l10.info,
                                 ntVal7.0,
                                 val5.__br_info ],
                           __br_terms =
                             join
                               [ [ l9.info ],
                                 [ x4.info ],
                                 val4.__br_terms,
                                 [ l10.info ],
                                 val5.__br_terms ],
                           bindings =
                             concat
                               [ { ident =
                                     match
                                       [ { v =
                                             nameNoSym
                                               x4.val,
                                           i =
                                             x4.info } ]
                                     with
                                       [ x5 ] ++ _
                                     in
                                     x5,
                                   body =
                                     match
                                       [ ntVal7.1 ]
                                     with
                                       [ x6 ] ++ _
                                     in
                                     x6,
                                   tyAnnot =
                                     match
                                       val4.tyAnnot
                                     with
                                       [ x7 ] ++ _
                                     then
                                       Some
                                         x7
                                     else
                                       None
                                         {} } ]
                               val5.bindings } },
             { nt =
                 kleene2,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state17: {errors: Ref [(Info, [Char])], content: String}.
                   lam res17.
                     match
                       res17
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           bindings =
                             "" } },
             { nt =
                 #var"BinderAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "recursive",
                   litSym
                     "letf",
                   tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     alt1,
                   litSym
                     "=",
                   ntSym
                     #var"Merged",
                   ntSym
                     kleene2 ],
               action =
                 lam state18: {errors: Ref [(Info, [Char])], content: String}.
                   lam res18.
                     match
                       res18
                     with
                       [ LitParsed l11,
                         LitParsed l12,
                         TokParsed (LIdentTok x8),
                         UserSym val6,
                         LitParsed l13,
                         UserSym ntVal8,
                         UserSym val5 ]
                     in
                     let val6: {tyAnnot: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val6
                       in
                       let ntVal8: (Info, Merged) =
                         fromDyn
                           ntVal8
                       in
                       let val5: {bindings: [{body: Merged, ident: {i: Info, v: Name}, tyAnnot: Option Merged}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val5
                       in
                       asDyn
                         (RecLetBinderOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l11.info
                                  [ l12.info,
                                    x8.info,
                                    val6.__br_info,
                                    l13.info,
                                    ntVal8.0,
                                    val5.__br_info ],
                              __br_terms =
                                join
                                  [ [ l11.info ],
                                    [ l12.info ],
                                    [ x8.info ],
                                    val6.__br_terms,
                                    [ l13.info ],
                                    val5.__br_terms ],
                              bindings =
                                concat
                                  [ { ident =
                                        match
                                          [ { v =
                                                nameNoSym
                                                  x8.val,
                                              i =
                                                x8.info } ]
                                        with
                                          [ x9 ] ++ _
                                        in
                                        x9,
                                      body =
                                        match
                                          [ ntVal8.1 ]
                                        with
                                          [ x10 ] ++ _
                                        in
                                        x10,
                                      tyAnnot =
                                        match
                                          val6.tyAnnot
                                        with
                                          [ x11 ] ++ _
                                        then
                                          Some
                                            x11
                                        else
                                          None
                                            {} } ]
                                  val5.bindings }) },
             { nt =
                 alt3,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state19: {errors: Ref [(Info, [Char])], content: String}.
                   lam res19.
                     match
                       res19
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           tyAnnot =
                             "" } },
             { nt =
                 alt3,
               label =
                 {},
               rhs =
                 [ litSym
                     ":",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state20: {errors: Ref [(Info, [Char])], content: String}.
                   lam res20.
                     match
                       res20
                     with
                       [ LitParsed l14,
                         UserSym ntVal9 ]
                     in
                     let ntVal9: (Info, Merged) =
                         fromDyn
                           ntVal9
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l14.info
                               ntVal9.0,
                           __br_terms =
                             [ l14.info ],
                           tyAnnot =
                             [ ntVal9.1 ] } },
             { nt =
                 #var"BinderAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "let",
                   tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     alt3,
                   litSym
                     "=",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state21: {errors: Ref [(Info, [Char])], content: String}.
                   lam res21.
                     match
                       res21
                     with
                       [ LitParsed l15,
                         TokParsed (LIdentTok x12),
                         UserSym val7,
                         LitParsed l16,
                         UserSym ntVal10 ]
                     in
                     let val7: {tyAnnot: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val7
                       in
                       let ntVal10: (Info, Merged) =
                         fromDyn
                           ntVal10
                       in
                       asDyn
                         (LetBinderOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l15.info
                                  [ x12.info,
                                    val7.__br_info,
                                    l16.info,
                                    ntVal10.0 ],
                              __br_terms =
                                join
                                  [ [ l15.info ],
                                    [ x12.info ],
                                    val7.__br_terms,
                                    [ l16.info ] ],
                              ident =
                                [ { v =
                                      nameNoSym
                                        x12.val,
                                    i =
                                      x12.info } ],
                              body =
                                [ ntVal10.1 ],
                              tyAnnot =
                                val7.tyAnnot }) },
             { nt =
                 #var"BinderAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "use",
                   tokSym
                     (UIdentRepr
                        {}) ],
               action =
                 lam state22: {errors: Ref [(Info, [Char])], content: String}.
                   lam res22.
                     match
                       res22
                     with
                       [ LitParsed l17,
                         TokParsed (UIdentTok x13) ]
                     in
                     asDyn
                         (UseBinderOp
                            { __br_info =
                                mergeInfo
                                  l17.info
                                  x13.info,
                              __br_terms =
                                concat
                                  [ l17.info ]
                                  [ x13.info ],
                              n =
                                [ { v =
                                      nameNoSym
                                        x13.val,
                                    i =
                                      x13.info } ] }) },
             { nt =
                 alt4,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state23: {errors: Ref [(Info, [Char])], content: String}.
                   lam res23.
                     match
                       res23
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           tusing =
                             "" } },
             { nt =
                 alt4,
               label =
                 {},
               rhs =
                 [ litSym
                     "using",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state24: {errors: Ref [(Info, [Char])], content: String}.
                   lam res24.
                     match
                       res24
                     with
                       [ LitParsed l18,
                         UserSym ntVal11 ]
                     in
                     let ntVal11: (Info, Merged) =
                         fromDyn
                           ntVal11
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l18.info
                               ntVal11.0,
                           __br_terms =
                             [ l18.info ],
                           tusing =
                             [ ntVal11.1 ] } },
             { nt =
                 alt5,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state25: {errors: Ref [(Info, [Char])], content: String}.
                   lam res25.
                     match
                       res25
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           tonfail =
                             "" } },
             { nt =
                 alt5,
               label =
                 {},
               rhs =
                 [ litSym
                     "else",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state26: {errors: Ref [(Info, [Char])], content: String}.
                   lam res26.
                     match
                       res26
                     with
                       [ LitParsed l19,
                         UserSym ntVal12 ]
                     in
                     let ntVal12: (Info, Merged) =
                         fromDyn
                           ntVal12
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l19.info
                               ntVal12.0,
                           __br_terms =
                             [ l19.info ],
                           tonfail =
                             [ ntVal12.1 ] } },
             { nt =
                 #var"BinderAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "utest",
                   ntSym
                     #var"Merged",
                   litSym
                     "with",
                   ntSym
                     #var"Merged",
                   ntSym
                     alt4,
                   ntSym
                     alt5 ],
               action =
                 lam state27: {errors: Ref [(Info, [Char])], content: String}.
                   lam res27.
                     match
                       res27
                     with
                       [ LitParsed l20,
                         UserSym ntVal13,
                         LitParsed l21,
                         UserSym ntVal14,
                         UserSym val8,
                         UserSym val9 ]
                     in
                     let ntVal13: (Info, Merged) =
                         fromDyn
                           ntVal13
                       in
                       let ntVal14: (Info, Merged) =
                         fromDyn
                           ntVal14
                       in
                       let val8: {tusing: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val8
                       in
                       let val9: {tonfail: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val9
                       in
                       asDyn
                         (UtestBinderOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l20.info
                                  [ ntVal13.0,
                                    l21.info,
                                    ntVal14.0,
                                    val8.__br_info,
                                    val9.__br_info ],
                              __br_terms =
                                join
                                  [ [ l20.info ],
                                    [ l21.info ],
                                    val8.__br_terms,
                                    val9.__br_terms ],
                              tusing =
                                val8.tusing,
                              tonfail =
                                val9.tonfail,
                              test =
                                [ ntVal13.1 ],
                              expected =
                                [ ntVal14.1 ] }) },
             { nt =
                 alt6,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state28: {errors: Ref [(Info, [Char])], content: String}.
                   lam res28.
                     match
                       res28
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           effect =
                             "" } },
             { nt =
                 alt6,
               label =
                 {},
               rhs =
                 [ litSym
                     "!" ],
               action =
                 lam state29: {errors: Ref [(Info, [Char])], content: String}.
                   lam res29.
                     match
                       res29
                     with
                       [ LitParsed l22 ]
                     in
                     asDyn
                         { __br_info =
                             l22.info,
                           __br_terms =
                             [ l22.info ],
                           effect =
                             [ l22.info ] } },
             { nt =
                 #var"BinderAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "external",
                   tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     alt6,
                   litSym
                     ":",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state30: {errors: Ref [(Info, [Char])], content: String}.
                   lam res30.
                     match
                       res30
                     with
                       [ LitParsed l23,
                         TokParsed (LIdentTok x14),
                         UserSym val10,
                         LitParsed l24,
                         UserSym ntVal15 ]
                     in
                     let val10: {effect: [Info], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val10
                       in
                       let ntVal15: (Info, Merged) =
                         fromDyn
                           ntVal15
                       in
                       asDyn
                         (ExternalBinderOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l23.info
                                  [ x14.info,
                                    val10.__br_info,
                                    l24.info,
                                    ntVal15.0 ],
                              __br_terms =
                                join
                                  [ [ l23.info ],
                                    [ x14.info ],
                                    val10.__br_terms,
                                    [ l24.info ] ],
                              tyIdent =
                                [ ntVal15.1 ],
                              ident =
                                [ { v =
                                      nameNoSym
                                        x14.val,
                                    i =
                                      x14.info } ],
                              effect =
                                val10.effect }) },
             { nt =
                 #var"MergedPostfix",
               label =
                 {},
               rhs =
                 [ litSym
                     ".",
                   tokSym
                     (LIdentRepr
                        {}) ],
               action =
                 lam state31: {errors: Ref [(Info, [Char])], content: String}.
                   lam res31.
                     match
                       res31
                     with
                       [ LitParsed l25,
                         TokParsed (LIdentTok x15) ]
                     in
                     asDyn
                         (ProjMergedOp
                            { __br_info =
                                mergeInfo
                                  l25.info
                                  x15.info,
                              __br_terms =
                                concat
                                  [ l25.info ]
                                  [ x15.info ],
                              label =
                                [ { v =
                                      x15.val,
                                    i =
                                      x15.info } ] }) },
             { nt =
                 #var"MergedInfix",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state32: {errors: Ref [(Info, [Char])], content: String}.
                   lam res32.
                     match
                       res32
                     with
                       ""
                     in
                     asDyn
                         (AppMergedOp
                            { __br_info =
                                NoInfo
                                  {},
                              __br_terms =
                                "" }) },
             { nt =
                 #var"MergedInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     ";" ],
               action =
                 lam state33: {errors: Ref [(Info, [Char])], content: String}.
                   lam res33.
                     match
                       res33
                     with
                       [ LitParsed l26 ]
                     in
                     asDyn
                         (SemiMergedOp
                            { __br_info =
                                l26.info,
                              __br_terms =
                                [ l26.info ] }) },
             { nt =
                 alt7,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state34: {errors: Ref [(Info, [Char])], content: String}.
                   lam res34.
                     match
                       res34
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           ty =
                             "" } },
             { nt =
                 alt7,
               label =
                 {},
               rhs =
                 [ litSym
                     ":",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state35: {errors: Ref [(Info, [Char])], content: String}.
                   lam res35.
                     match
                       res35
                     with
                       [ LitParsed l27,
                         UserSym ntVal16 ]
                     in
                     let ntVal16: (Info, Merged) =
                         fromDyn
                           ntVal16
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l27.info
                               ntVal16.0,
                           __br_terms =
                             [ l27.info ],
                           ty =
                             [ ntVal16.1 ] } },
             { nt =
                 alt8,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state36: {errors: Ref [(Info, [Char])], content: String}.
                   lam res36.
                     match
                       res36
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           value =
                             "" } },
             { nt =
                 alt8,
               label =
                 {},
               rhs =
                 [ litSym
                     "=",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state37: {errors: Ref [(Info, [Char])], content: String}.
                   lam res37.
                     match
                       res37
                     with
                       [ LitParsed l28,
                         UserSym ntVal17 ]
                     in
                     let ntVal17: (Info, Merged) =
                         fromDyn
                           ntVal17
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l28.info
                               ntVal17.0,
                           __br_terms =
                             [ l28.info ],
                           value =
                             [ ntVal17.1 ] } },
             { nt =
                 alt9,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state38: {errors: Ref [(Info, [Char])], content: String}.
                   lam res38.
                     match
                       res38
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           ty =
                             "" } },
             { nt =
                 alt9,
               label =
                 {},
               rhs =
                 [ litSym
                     ":",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state39: {errors: Ref [(Info, [Char])], content: String}.
                   lam res39.
                     match
                       res39
                     with
                       [ LitParsed l29,
                         UserSym ntVal18 ]
                     in
                     let ntVal18: (Info, Merged) =
                         fromDyn
                           ntVal18
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l29.info
                               ntVal18.0,
                           __br_terms =
                             [ l29.info ],
                           ty =
                             [ ntVal18.1 ] } },
             { nt =
                 alt10,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state40: {errors: Ref [(Info, [Char])], content: String}.
                   lam res40.
                     match
                       res40
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           value =
                             "" } },
             { nt =
                 alt10,
               label =
                 {},
               rhs =
                 [ litSym
                     "=",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state41: {errors: Ref [(Info, [Char])], content: String}.
                   lam res41.
                     match
                       res41
                     with
                       [ LitParsed l30,
                         UserSym ntVal19 ]
                     in
                     let ntVal19: (Info, Merged) =
                         fromDyn
                           ntVal19
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l30.info
                               ntVal19.0,
                           __br_terms =
                             [ l30.info ],
                           value =
                             [ ntVal19.1 ] } },
             { nt =
                 kleene3,
               label =
                 {},
               rhs =
                 [ litSym
                     ",",
                   tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     alt9,
                   ntSym
                     alt10,
                   ntSym
                     kleene3 ],
               action =
                 lam state42: {errors: Ref [(Info, [Char])], content: String}.
                   lam res42.
                     match
                       res42
                     with
                       [ LitParsed l31,
                         TokParsed (LIdentTok x16),
                         UserSym val11,
                         UserSym val12,
                         UserSym val13 ]
                     in
                     let val11: {ty: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val11
                       in
                       let val12: {value: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val12
                       in
                       let val13: {fields: [{ty: Option Merged, label: {i: Info, v: String}, value: Option Merged}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val13
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l31.info
                               [ x16.info,
                                 val11.__br_info,
                                 val12.__br_info,
                                 val13.__br_info ],
                           __br_terms =
                             join
                               [ [ l31.info ],
                                 [ x16.info ],
                                 val11.__br_terms,
                                 val12.__br_terms,
                                 val13.__br_terms ],
                           fields =
                             concat
                               [ { label =
                                     match
                                       [ { v =
                                             x16.val,
                                           i =
                                             x16.info } ]
                                     with
                                       [ x17 ] ++ _
                                     in
                                     x17,
                                   ty =
                                     match
                                       val11.ty
                                     with
                                       [ x18 ] ++ _
                                     then
                                       Some
                                         x18
                                     else
                                       None
                                         {},
                                   value =
                                     match
                                       val12.value
                                     with
                                       [ x19 ] ++ _
                                     then
                                       Some
                                         x19
                                     else
                                       None
                                         {} } ]
                               val13.fields } },
             { nt =
                 kleene3,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state43: {errors: Ref [(Info, [Char])], content: String}.
                   lam res43.
                     match
                       res43
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           fields =
                             "" } },
             { nt =
                 alt11,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state44: {errors: Ref [(Info, [Char])], content: String}.
                   lam res44.
                     match
                       res44
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           fields =
                             "" } },
             { nt =
                 alt11,
               label =
                 {},
               rhs =
                 [ tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     alt7,
                   ntSym
                     alt8,
                   ntSym
                     kleene3 ],
               action =
                 lam state45: {errors: Ref [(Info, [Char])], content: String}.
                   lam res45.
                     match
                       res45
                     with
                       [ TokParsed (LIdentTok x20),
                         UserSym val14,
                         UserSym val15,
                         UserSym val13 ]
                     in
                     let val14: {ty: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val14
                       in
                       let val15: {value: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val15
                       in
                       let val13: {fields: [{ty: Option Merged, label: {i: Info, v: String}, value: Option Merged}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val13
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               x20.info
                               [ val14.__br_info,
                                 val15.__br_info,
                                 val13.__br_info ],
                           __br_terms =
                             join
                               [ [ x20.info ],
                                 val14.__br_terms,
                                 val15.__br_terms,
                                 val13.__br_terms ],
                           fields =
                             concat
                               [ { label =
                                     match
                                       [ { v =
                                             x20.val,
                                           i =
                                             x20.info } ]
                                     with
                                       [ x21 ] ++ _
                                     in
                                     x21,
                                   ty =
                                     match
                                       val14.ty
                                     with
                                       [ x22 ] ++ _
                                     then
                                       Some
                                         x22
                                     else
                                       None
                                         {},
                                   value =
                                     match
                                       val15.value
                                     with
                                       [ x23 ] ++ _
                                     then
                                       Some
                                         x23
                                     else
                                       None
                                         {} } ]
                               val13.fields } },
             { nt =
                 #var"MergedPostfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "+",
                   litSym
                     "{",
                   ntSym
                     alt11,
                   litSym
                     "}" ],
               action =
                 lam state46: {errors: Ref [(Info, [Char])], content: String}.
                   lam res46.
                     match
                       res46
                     with
                       [ LitParsed l32,
                         LitParsed l33,
                         UserSym val16,
                         LitParsed l34 ]
                     in
                     let val16: {fields: [{ty: Option Merged, label: {i: Info, v: String}, value: Option Merged}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val16
                       in
                       asDyn
                         (RecordAddMergedOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l32.info
                                  [ l33.info,
                                    val16.__br_info,
                                    l34.info ],
                              __br_terms =
                                join
                                  [ [ l32.info ],
                                    [ l33.info ],
                                    val16.__br_terms,
                                    [ l34.info ] ],
                              fields =
                                val16.fields }) },
             { nt =
                 kleene4,
               label =
                 {},
               rhs =
                 [ litSym
                     ",",
                   tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     kleene4 ],
               action =
                 lam state47: {errors: Ref [(Info, [Char])], content: String}.
                   lam res47.
                     match
                       res47
                     with
                       [ LitParsed l35,
                         TokParsed (LIdentTok x24),
                         UserSym val17 ]
                     in
                     let val17: {fields: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val17
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l35.info
                               [ x24.info,
                                 val17.__br_info ],
                           __br_terms =
                             join
                               [ [ l35.info ],
                                 [ x24.info ],
                                 val17.__br_terms ],
                           fields =
                             concat
                               [ { v =
                                     x24.val,
                                   i =
                                     x24.info } ]
                               val17.fields } },
             { nt =
                 kleene4,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state48: {errors: Ref [(Info, [Char])], content: String}.
                   lam res48.
                     match
                       res48
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           fields =
                             "" } },
             { nt =
                 alt12,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state49: {errors: Ref [(Info, [Char])], content: String}.
                   lam res49.
                     match
                       res49
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           fields =
                             "" } },
             { nt =
                 alt12,
               label =
                 {},
               rhs =
                 [ tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     kleene4 ],
               action =
                 lam state50: {errors: Ref [(Info, [Char])], content: String}.
                   lam res50.
                     match
                       res50
                     with
                       [ TokParsed (LIdentTok x25),
                         UserSym val17 ]
                     in
                     let val17: {fields: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val17
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               x25.info
                               val17.__br_info,
                           __br_terms =
                             concat
                               [ x25.info ]
                               val17.__br_terms,
                           fields =
                             concat
                               [ { v =
                                     x25.val,
                                   i =
                                     x25.info } ]
                               val17.fields } },
             { nt =
                 #var"MergedPostfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "-",
                   litSym
                     "{",
                   ntSym
                     alt12,
                   litSym
                     "}" ],
               action =
                 lam state51: {errors: Ref [(Info, [Char])], content: String}.
                   lam res51.
                     match
                       res51
                     with
                       [ LitParsed l36,
                         LitParsed l37,
                         UserSym val18,
                         LitParsed l38 ]
                     in
                     let val18: {fields: [{i: Info, v: String}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val18
                       in
                       asDyn
                         (RecordSubMergedOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l36.info
                                  [ l37.info,
                                    val18.__br_info,
                                    l38.info ],
                              __br_terms =
                                join
                                  [ [ l36.info ],
                                    [ l37.info ],
                                    val18.__br_terms,
                                    [ l38.info ] ],
                              fields =
                                val18.fields }) },
             { nt =
                 alt13,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state52: {errors: Ref [(Info, [Char])], content: String}.
                   lam res52.
                     match
                       res52
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           ty =
                             "" } },
             { nt =
                 alt13,
               label =
                 {},
               rhs =
                 [ litSym
                     ":",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state53: {errors: Ref [(Info, [Char])], content: String}.
                   lam res53.
                     match
                       res53
                     with
                       [ LitParsed l39,
                         UserSym ntVal20 ]
                     in
                     let ntVal20: (Info, Merged) =
                         fromDyn
                           ntVal20
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l39.info
                               ntVal20.0,
                           __br_terms =
                             [ l39.info ],
                           ty =
                             [ ntVal20.1 ] } },
             { nt =
                 alt14,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state54: {errors: Ref [(Info, [Char])], content: String}.
                   lam res54.
                     match
                       res54
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           value =
                             "" } },
             { nt =
                 alt14,
               label =
                 {},
               rhs =
                 [ litSym
                     "=",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state55: {errors: Ref [(Info, [Char])], content: String}.
                   lam res55.
                     match
                       res55
                     with
                       [ LitParsed l40,
                         UserSym ntVal21 ]
                     in
                     let ntVal21: (Info, Merged) =
                         fromDyn
                           ntVal21
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l40.info
                               ntVal21.0,
                           __br_terms =
                             [ l40.info ],
                           value =
                             [ ntVal21.1 ] } },
             { nt =
                 alt15,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state56: {errors: Ref [(Info, [Char])], content: String}.
                   lam res56.
                     match
                       res56
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           ty =
                             "" } },
             { nt =
                 alt15,
               label =
                 {},
               rhs =
                 [ litSym
                     ":",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state57: {errors: Ref [(Info, [Char])], content: String}.
                   lam res57.
                     match
                       res57
                     with
                       [ LitParsed l41,
                         UserSym ntVal22 ]
                     in
                     let ntVal22: (Info, Merged) =
                         fromDyn
                           ntVal22
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l41.info
                               ntVal22.0,
                           __br_terms =
                             [ l41.info ],
                           ty =
                             [ ntVal22.1 ] } },
             { nt =
                 alt16,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state58: {errors: Ref [(Info, [Char])], content: String}.
                   lam res58.
                     match
                       res58
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           value =
                             "" } },
             { nt =
                 alt16,
               label =
                 {},
               rhs =
                 [ litSym
                     "=",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state59: {errors: Ref [(Info, [Char])], content: String}.
                   lam res59.
                     match
                       res59
                     with
                       [ LitParsed l42,
                         UserSym ntVal23 ]
                     in
                     let ntVal23: (Info, Merged) =
                         fromDyn
                           ntVal23
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l42.info
                               ntVal23.0,
                           __br_terms =
                             [ l42.info ],
                           value =
                             [ ntVal23.1 ] } },
             { nt =
                 kleene5,
               label =
                 {},
               rhs =
                 [ litSym
                     ",",
                   tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     alt15,
                   ntSym
                     alt16,
                   ntSym
                     kleene5 ],
               action =
                 lam state60: {errors: Ref [(Info, [Char])], content: String}.
                   lam res60.
                     match
                       res60
                     with
                       [ LitParsed l43,
                         TokParsed (LIdentTok x26),
                         UserSym val19,
                         UserSym val20,
                         UserSym val21 ]
                     in
                     let val19: {ty: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val19
                       in
                       let val20: {value: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val20
                       in
                       let val21: {fields: [{ty: Option Merged, label: {i: Info, v: String}, value: Option Merged}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val21
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l43.info
                               [ x26.info,
                                 val19.__br_info,
                                 val20.__br_info,
                                 val21.__br_info ],
                           __br_terms =
                             join
                               [ [ l43.info ],
                                 [ x26.info ],
                                 val19.__br_terms,
                                 val20.__br_terms,
                                 val21.__br_terms ],
                           fields =
                             concat
                               [ { label =
                                     match
                                       [ { v =
                                             x26.val,
                                           i =
                                             x26.info } ]
                                     with
                                       [ x27 ] ++ _
                                     in
                                     x27,
                                   ty =
                                     match
                                       val19.ty
                                     with
                                       [ x28 ] ++ _
                                     then
                                       Some
                                         x28
                                     else
                                       None
                                         {},
                                   value =
                                     match
                                       val20.value
                                     with
                                       [ x29 ] ++ _
                                     then
                                       Some
                                         x29
                                     else
                                       None
                                         {} } ]
                               val21.fields } },
             { nt =
                 kleene5,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state61: {errors: Ref [(Info, [Char])], content: String}.
                   lam res61.
                     match
                       res61
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           fields =
                             "" } },
             { nt =
                 alt17,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state62: {errors: Ref [(Info, [Char])], content: String}.
                   lam res62.
                     match
                       res62
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           fields =
                             "" } },
             { nt =
                 alt17,
               label =
                 {},
               rhs =
                 [ tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     alt13,
                   ntSym
                     alt14,
                   ntSym
                     kleene5 ],
               action =
                 lam state63: {errors: Ref [(Info, [Char])], content: String}.
                   lam res63.
                     match
                       res63
                     with
                       [ TokParsed (LIdentTok x30),
                         UserSym val22,
                         UserSym val23,
                         UserSym val21 ]
                     in
                     let val22: {ty: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val22
                       in
                       let val23: {value: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val23
                       in
                       let val21: {fields: [{ty: Option Merged, label: {i: Info, v: String}, value: Option Merged}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val21
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               x30.info
                               [ val22.__br_info,
                                 val23.__br_info,
                                 val21.__br_info ],
                           __br_terms =
                             join
                               [ [ x30.info ],
                                 val22.__br_terms,
                                 val23.__br_terms,
                                 val21.__br_terms ],
                           fields =
                             concat
                               [ { label =
                                     match
                                       [ { v =
                                             x30.val,
                                           i =
                                             x30.info } ]
                                     with
                                       [ x31 ] ++ _
                                     in
                                     x31,
                                   ty =
                                     match
                                       val22.ty
                                     with
                                       [ x32 ] ++ _
                                     then
                                       Some
                                         x32
                                     else
                                       None
                                         {},
                                   value =
                                     match
                                       val23.value
                                     with
                                       [ x33 ] ++ _
                                     then
                                       Some
                                         x33
                                     else
                                       None
                                         {} } ]
                               val21.fields } },
             { nt =
                 #var"MergedPostfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "~",
                   litSym
                     "{",
                   ntSym
                     alt17,
                   litSym
                     "}" ],
               action =
                 lam state64: {errors: Ref [(Info, [Char])], content: String}.
                   lam res64.
                     match
                       res64
                     with
                       [ LitParsed l44,
                         LitParsed l45,
                         UserSym val24,
                         LitParsed l46 ]
                     in
                     let val24: {fields: [{ty: Option Merged, label: {i: Info, v: String}, value: Option Merged}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val24
                       in
                       asDyn
                         (RecordChangeMergedOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l44.info
                                  [ l45.info,
                                    val24.__br_info,
                                    l46.info ],
                              __br_terms =
                                join
                                  [ [ l44.info ],
                                    [ l45.info ],
                                    val24.__br_terms,
                                    [ l46.info ] ],
                              fields =
                                val24.fields }) },
             { nt =
                 #var"MergedPrefix",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"Binder",
                   litSym
                     "in" ],
               action =
                 lam state65: {errors: Ref [(Info, [Char])], content: String}.
                   lam res65.
                     match
                       res65
                     with
                       [ UserSym ntVal24,
                         LitParsed l47 ]
                     in
                     let ntVal24: (Info, Binder) =
                         fromDyn
                           ntVal24
                       in
                       asDyn
                         (BindMergedOp
                            { __br_info =
                                mergeInfo
                                  ntVal24.0
                                  l47.info,
                              __br_terms =
                                [ l47.info ],
                              binder =
                                [ ntVal24.1 ] }) },
             { nt =
                 alt18,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state66: {errors: Ref [(Info, [Char])], content: String}.
                   lam res66.
                     match
                       res66
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           ident =
                             "",
                           tyAnnot =
                             "" } },
             { nt =
                 alt18,
               label =
                 {},
               rhs =
                 [ tokSym
                     (LIdentRepr
                        {}) ],
               action =
                 lam state67: {errors: Ref [(Info, [Char])], content: String}.
                   lam res67.
                     match
                       res67
                     with
                       [ TokParsed (LIdentTok x34) ]
                     in
                     asDyn
                         { __br_info =
                             x34.info,
                           __br_terms =
                             [ x34.info ],
                           ident =
                             [ { v =
                                   nameNoSym
                                     x34.val,
                                 i =
                                   x34.info } ],
                           tyAnnot =
                             "" } },
             { nt =
                 alt18,
               label =
                 {},
               rhs =
                 [ litSym
                     "(",
                   tokSym
                     (LIdentRepr
                        {}),
                   litSym
                     ":",
                   ntSym
                     #var"Merged",
                   litSym
                     ")" ],
               action =
                 lam state68: {errors: Ref [(Info, [Char])], content: String}.
                   lam res68.
                     match
                       res68
                     with
                       [ LitParsed l48,
                         TokParsed (LIdentTok x35),
                         LitParsed l49,
                         UserSym ntVal25,
                         LitParsed l50 ]
                     in
                     let ntVal25: (Info, Merged) =
                         fromDyn
                           ntVal25
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l48.info
                               [ x35.info,
                                 l49.info,
                                 ntVal25.0,
                                 l50.info ],
                           __br_terms =
                             join
                               [ [ l48.info ],
                                 [ x35.info ],
                                 [ l49.info ],
                                 [ l50.info ] ],
                           ident =
                             [ { v =
                                   nameNoSym
                                     x35.val,
                                 i =
                                   x35.info } ],
                           tyAnnot =
                             [ ntVal25.1 ] } },
             { nt =
                 #var"MergedPrefix",
               label =
                 {},
               rhs =
                 [ litSym
                     "lam",
                   ntSym
                     alt18,
                   litSym
                     "." ],
               action =
                 lam state69: {errors: Ref [(Info, [Char])], content: String}.
                   lam res69.
                     match
                       res69
                     with
                       [ LitParsed l51,
                         UserSym val25,
                         LitParsed l52 ]
                     in
                     let val25: {ident: [{i: Info, v: Name}], tyAnnot: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val25
                       in
                       asDyn
                         (LamMergedOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l51.info
                                  [ val25.__br_info,
                                    l52.info ],
                              __br_terms =
                                join
                                  [ [ l51.info ],
                                    val25.__br_terms,
                                    [ l52.info ] ],
                              ident =
                                val25.ident,
                              tyAnnot =
                                val25.tyAnnot }) },
             { nt =
                 #var"MergedPrefix",
               label =
                 {},
               rhs =
                 [ litSym
                     "match",
                   ntSym
                     #var"Merged",
                   litSym
                     "with",
                   ntSym
                     #var"Merged",
                   litSym
                     "then",
                   ntSym
                     #var"Merged",
                   litSym
                     "else" ],
               action =
                 lam state70: {errors: Ref [(Info, [Char])], content: String}.
                   lam res70.
                     match
                       res70
                     with
                       [ LitParsed l53,
                         UserSym ntVal26,
                         LitParsed l54,
                         UserSym ntVal27,
                         LitParsed l55,
                         UserSym ntVal28,
                         LitParsed l56 ]
                     in
                     let ntVal26: (Info, Merged) =
                         fromDyn
                           ntVal26
                       in
                       let ntVal27: (Info, Merged) =
                         fromDyn
                           ntVal27
                       in
                       let ntVal28: (Info, Merged) =
                         fromDyn
                           ntVal28
                       in
                       asDyn
                         (MatchMergedOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l53.info
                                  [ ntVal26.0,
                                    l54.info,
                                    ntVal27.0,
                                    l55.info,
                                    ntVal28.0,
                                    l56.info ],
                              __br_terms =
                                join
                                  [ [ l53.info ],
                                    [ l54.info ],
                                    [ l55.info ],
                                    [ l56.info ] ],
                              pat =
                                [ ntVal27.1 ],
                              thn =
                                [ ntVal28.1 ],
                              target =
                                [ ntVal26.1 ] }) },
             { nt =
                 #var"MergedPrefix",
               label =
                 {},
               rhs =
                 [ litSym
                     "if",
                   ntSym
                     #var"Merged",
                   litSym
                     "then",
                   ntSym
                     #var"Merged",
                   litSym
                     "else" ],
               action =
                 lam state71: {errors: Ref [(Info, [Char])], content: String}.
                   lam res71.
                     match
                       res71
                     with
                       [ LitParsed l57,
                         UserSym ntVal29,
                         LitParsed l58,
                         UserSym ntVal30,
                         LitParsed l59 ]
                     in
                     let ntVal29: (Info, Merged) =
                         fromDyn
                           ntVal29
                       in
                       let ntVal30: (Info, Merged) =
                         fromDyn
                           ntVal30
                       in
                       asDyn
                         (IfMergedOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l57.info
                                  [ ntVal29.0,
                                    l58.info,
                                    ntVal30.0,
                                    l59.info ],
                              __br_terms =
                                join
                                  [ [ l57.info ],
                                    [ l58.info ],
                                    [ l59.info ] ],
                              thn =
                                [ ntVal30.1 ],
                              target =
                                [ ntVal29.1 ] }) },
             { nt =
                 kleene6,
               label =
                 {},
               rhs =
                 [ litSym
                     "case",
                   ntSym
                     #var"Merged",
                   litSym
                     "then",
                   ntSym
                     #var"Merged",
                   ntSym
                     kleene6 ],
               action =
                 lam state72: {errors: Ref [(Info, [Char])], content: String}.
                   lam res72.
                     match
                       res72
                     with
                       [ LitParsed l60,
                         UserSym ntVal31,
                         LitParsed l61,
                         UserSym ntVal32,
                         UserSym val26 ]
                     in
                     let ntVal31: (Info, Merged) =
                         fromDyn
                           ntVal31
                       in
                       let ntVal32: (Info, Merged) =
                         fromDyn
                           ntVal32
                       in
                       let val26: {cases: [{pat: Merged, thn: Merged, keyword: Info}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val26
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l60.info
                               [ ntVal31.0,
                                 l61.info,
                                 ntVal32.0,
                                 val26.__br_info ],
                           __br_terms =
                             join
                               [ [ l60.info ],
                                 [ l61.info ],
                                 val26.__br_terms ],
                           cases =
                             concat
                               [ { pat =
                                     match
                                       [ ntVal31.1 ]
                                     with
                                       [ x36 ] ++ _
                                     in
                                     x36,
                                   thn =
                                     match
                                       [ ntVal32.1 ]
                                     with
                                       [ x37 ] ++ _
                                     in
                                     x37,
                                   keyword =
                                     match
                                       [ l60.info ]
                                     with
                                       [ x38 ] ++ _
                                     in
                                     x38 } ]
                               val26.cases } },
             { nt =
                 kleene6,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state73: {errors: Ref [(Info, [Char])], content: String}.
                   lam res73.
                     match
                       res73
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           cases =
                             "" } },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "switch",
                   ntSym
                     #var"Merged",
                   litSym
                     "case",
                   ntSym
                     #var"Merged",
                   litSym
                     "then",
                   ntSym
                     #var"Merged",
                   ntSym
                     kleene6,
                   litSym
                     "end" ],
               action =
                 lam state74: {errors: Ref [(Info, [Char])], content: String}.
                   lam res74.
                     match
                       res74
                     with
                       [ LitParsed l62,
                         UserSym ntVal33,
                         LitParsed l63,
                         UserSym ntVal34,
                         LitParsed l64,
                         UserSym ntVal35,
                         UserSym val26,
                         LitParsed l65 ]
                     in
                     let ntVal33: (Info, Merged) =
                         fromDyn
                           ntVal33
                       in
                       let ntVal34: (Info, Merged) =
                         fromDyn
                           ntVal34
                       in
                       let ntVal35: (Info, Merged) =
                         fromDyn
                           ntVal35
                       in
                       let val26: {cases: [{pat: Merged, thn: Merged, keyword: Info}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val26
                       in
                       asDyn
                         (SwitchMergedOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l62.info
                                  [ ntVal33.0,
                                    l63.info,
                                    ntVal34.0,
                                    l64.info,
                                    ntVal35.0,
                                    val26.__br_info,
                                    l65.info ],
                              __br_terms =
                                join
                                  [ [ l62.info ],
                                    [ l63.info ],
                                    [ l64.info ],
                                    val26.__br_terms,
                                    [ l65.info ] ],
                              target =
                                [ ntVal33.1 ],
                              cases =
                                concat
                                  [ { pat =
                                        match
                                          [ ntVal34.1 ]
                                        with
                                          [ x39 ] ++ _
                                        in
                                        x39,
                                      thn =
                                        match
                                          [ ntVal35.1 ]
                                        with
                                          [ x40 ] ++ _
                                        in
                                        x40,
                                      keyword =
                                        match
                                          [ l63.info ]
                                        with
                                          [ x41 ] ++ _
                                        in
                                        x41 } ]
                                  val26.cases,
                              fail =
                                [ l65.info ] }) },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ tokSym
                     (UIdentRepr
                        {}) ],
               action =
                 lam state75: {errors: Ref [(Info, [Char])], content: String}.
                   lam res75.
                     match
                       res75
                     with
                       [ TokParsed (UIdentTok x42) ]
                     in
                     asDyn
                         (ConMergedOp
                            { __br_info =
                                x42.info,
                              __br_terms =
                                [ x42.info ],
                              ident =
                                [ { v =
                                      nameNoSym
                                        x42.val,
                                    i =
                                      x42.info } ] }) },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ tokSym
                     (LIdentRepr
                        {}) ],
               action =
                 lam state76: {errors: Ref [(Info, [Char])], content: String}.
                   lam res76.
                     match
                       res76
                     with
                       [ TokParsed (LIdentTok x43) ]
                     in
                     asDyn
                         (VarMergedOp
                            { __br_info =
                                x43.info,
                              __br_terms =
                                [ x43.info ],
                              ident =
                                [ { v =
                                      nameNoSym
                                        x43.val,
                                    i =
                                      x43.info } ] }) },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ tokSym
                     (CharRepr
                        {}) ],
               action =
                 lam state77: {errors: Ref [(Info, [Char])], content: String}.
                   lam res77.
                     match
                       res77
                     with
                       [ TokParsed (CharTok x44) ]
                     in
                     asDyn
                         (CharMergedOp
                            { __br_info =
                                x44.info,
                              __br_terms =
                                [ x44.info ],
                              val =
                                [ { v =
                                      x44.val,
                                    i =
                                      x44.info } ] }) },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ tokSym
                     (IntRepr
                        {}) ],
               action =
                 lam state78: {errors: Ref [(Info, [Char])], content: String}.
                   lam res78.
                     match
                       res78
                     with
                       [ TokParsed (IntTok x45) ]
                     in
                     asDyn
                         (IntMergedOp
                            { __br_info =
                                x45.info,
                              __br_terms =
                                [ x45.info ],
                              val =
                                [ { v =
                                      x45.val,
                                    i =
                                      x45.info } ] }) },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ tokSym
                     (FloatRepr
                        {}) ],
               action =
                 lam state79: {errors: Ref [(Info, [Char])], content: String}.
                   lam res79.
                     match
                       res79
                     with
                       [ TokParsed (FloatTok x46) ]
                     in
                     asDyn
                         (FloatMergedOp
                            { __br_info =
                                x46.info,
                              __br_terms =
                                [ x46.info ],
                              val =
                                [ { v =
                                      x46.val,
                                    i =
                                      x46.info } ] }) },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "true" ],
               action =
                 lam state80: {errors: Ref [(Info, [Char])], content: String}.
                   lam res80.
                     match
                       res80
                     with
                       [ LitParsed l66 ]
                     in
                     asDyn
                         (TrueMergedOp
                            { __br_info =
                                l66.info,
                              __br_terms =
                                [ l66.info ] }) },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "false" ],
               action =
                 lam state81: {errors: Ref [(Info, [Char])], content: String}.
                   lam res81.
                     match
                       res81
                     with
                       [ LitParsed l67 ]
                     in
                     asDyn
                         (FalseMergedOp
                            { __br_info =
                                l67.info,
                              __br_terms =
                                [ l67.info ] }) },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "never" ],
               action =
                 lam state82: {errors: Ref [(Info, [Char])], content: String}.
                   lam res82.
                     match
                       res82
                     with
                       [ LitParsed l68 ]
                     in
                     asDyn
                         (NeverMergedOp
                            { __br_info =
                                l68.info,
                              __br_terms =
                                [ l68.info ] }) },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ tokSym
                     (StringRepr
                        {}) ],
               action =
                 lam state83: {errors: Ref [(Info, [Char])], content: String}.
                   lam res83.
                     match
                       res83
                     with
                       [ TokParsed (StringTok x47) ]
                     in
                     asDyn
                         (StringMergedOp
                            { __br_info =
                                x47.info,
                              __br_terms =
                                [ x47.info ],
                              val =
                                [ { v =
                                      x47.val,
                                    i =
                                      x47.info } ] }) },
             { nt =
                 kleene7,
               label =
                 {},
               rhs =
                 [ litSym
                     ",",
                   ntSym
                     #var"Merged",
                   ntSym
                     kleene7 ],
               action =
                 lam state84: {errors: Ref [(Info, [Char])], content: String}.
                   lam res84.
                     match
                       res84
                     with
                       [ LitParsed l69,
                         UserSym ntVal36,
                         UserSym val27 ]
                     in
                     let ntVal36: (Info, Merged) =
                         fromDyn
                           ntVal36
                       in
                       let val27: {tms: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val27
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l69.info
                               [ ntVal36.0,
                                 val27.__br_info ],
                           __br_terms =
                             concat
                               [ l69.info ]
                               val27.__br_terms,
                           tms =
                             concat
                               [ ntVal36.1 ]
                               val27.tms } },
             { nt =
                 kleene7,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state85: {errors: Ref [(Info, [Char])], content: String}.
                   lam res85.
                     match
                       res85
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           tms =
                             "" } },
             { nt =
                 alt19,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state86: {errors: Ref [(Info, [Char])], content: String}.
                   lam res86.
                     match
                       res86
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           tms =
                             "" } },
             { nt =
                 alt19,
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"Merged",
                   ntSym
                     kleene7 ],
               action =
                 lam state87: {errors: Ref [(Info, [Char])], content: String}.
                   lam res87.
                     match
                       res87
                     with
                       [ UserSym ntVal37,
                         UserSym val27 ]
                     in
                     let ntVal37: (Info, Merged) =
                         fromDyn
                           ntVal37
                       in
                       let val27: {tms: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val27
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               ntVal37.0
                               val27.__br_info,
                           __br_terms =
                             val27.__br_terms,
                           tms =
                             concat
                               [ ntVal37.1 ]
                               val27.tms } },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "[",
                   ntSym
                     alt19,
                   litSym
                     "]" ],
               action =
                 lam state88: {errors: Ref [(Info, [Char])], content: String}.
                   lam res88.
                     match
                       res88
                     with
                       [ LitParsed l70,
                         UserSym val28,
                         LitParsed l71 ]
                     in
                     let val28: {tms: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val28
                       in
                       asDyn
                         (SequenceMergedOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l70.info
                                  [ val28.__br_info,
                                    l71.info ],
                              __br_terms =
                                join
                                  [ [ l70.info ],
                                    val28.__br_terms,
                                    [ l71.info ] ],
                              tms =
                                val28.tms }) },
             { nt =
                 alt20,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state89: {errors: Ref [(Info, [Char])], content: String}.
                   lam res89.
                     match
                       res89
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           ty =
                             "" } },
             { nt =
                 alt20,
               label =
                 {},
               rhs =
                 [ litSym
                     ":",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state90: {errors: Ref [(Info, [Char])], content: String}.
                   lam res90.
                     match
                       res90
                     with
                       [ LitParsed l72,
                         UserSym ntVal38 ]
                     in
                     let ntVal38: (Info, Merged) =
                         fromDyn
                           ntVal38
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l72.info
                               ntVal38.0,
                           __br_terms =
                             [ l72.info ],
                           ty =
                             [ ntVal38.1 ] } },
             { nt =
                 alt21,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state91: {errors: Ref [(Info, [Char])], content: String}.
                   lam res91.
                     match
                       res91
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           e =
                             "" } },
             { nt =
                 alt21,
               label =
                 {},
               rhs =
                 [ litSym
                     "=",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state92: {errors: Ref [(Info, [Char])], content: String}.
                   lam res92.
                     match
                       res92
                     with
                       [ LitParsed l73,
                         UserSym ntVal39 ]
                     in
                     let ntVal39: (Info, Merged) =
                         fromDyn
                           ntVal39
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l73.info
                               ntVal39.0,
                           __br_terms =
                             [ l73.info ],
                           e =
                             [ ntVal39.1 ] } },
             { nt =
                 alt22,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state93: {errors: Ref [(Info, [Char])], content: String}.
                   lam res93.
                     match
                       res93
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           ty =
                             "" } },
             { nt =
                 alt22,
               label =
                 {},
               rhs =
                 [ litSym
                     ":",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state94: {errors: Ref [(Info, [Char])], content: String}.
                   lam res94.
                     match
                       res94
                     with
                       [ LitParsed l74,
                         UserSym ntVal40 ]
                     in
                     let ntVal40: (Info, Merged) =
                         fromDyn
                           ntVal40
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l74.info
                               ntVal40.0,
                           __br_terms =
                             [ l74.info ],
                           ty =
                             [ ntVal40.1 ] } },
             { nt =
                 alt23,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state95: {errors: Ref [(Info, [Char])], content: String}.
                   lam res95.
                     match
                       res95
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           e =
                             "" } },
             { nt =
                 alt23,
               label =
                 {},
               rhs =
                 [ litSym
                     "=",
                   ntSym
                     #var"Merged" ],
               action =
                 lam state96: {errors: Ref [(Info, [Char])], content: String}.
                   lam res96.
                     match
                       res96
                     with
                       [ LitParsed l75,
                         UserSym ntVal41 ]
                     in
                     let ntVal41: (Info, Merged) =
                         fromDyn
                           ntVal41
                       in
                       asDyn
                         { __br_info =
                             mergeInfo
                               l75.info
                               ntVal41.0,
                           __br_terms =
                             [ l75.info ],
                           e =
                             [ ntVal41.1 ] } },
             { nt =
                 kleene8,
               label =
                 {},
               rhs =
                 [ litSym
                     ",",
                   tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     alt22,
                   ntSym
                     alt23,
                   ntSym
                     kleene8 ],
               action =
                 lam state97: {errors: Ref [(Info, [Char])], content: String}.
                   lam res97.
                     match
                       res97
                     with
                       [ LitParsed l76,
                         TokParsed (LIdentTok x48),
                         UserSym val29,
                         UserSym val30,
                         UserSym val31 ]
                     in
                     let val29: {ty: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val29
                       in
                       let val30: {e: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val30
                       in
                       let val31: {fields: [{e: Option Merged, ty: Option Merged, label: {i: Info, v: String}}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val31
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l76.info
                               [ x48.info,
                                 val29.__br_info,
                                 val30.__br_info,
                                 val31.__br_info ],
                           __br_terms =
                             join
                               [ [ l76.info ],
                                 [ x48.info ],
                                 val29.__br_terms,
                                 val30.__br_terms,
                                 val31.__br_terms ],
                           fields =
                             concat
                               [ { label =
                                     match
                                       [ { v =
                                             x48.val,
                                           i =
                                             x48.info } ]
                                     with
                                       [ x49 ] ++ _
                                     in
                                     x49,
                                   e =
                                     match
                                       val30.e
                                     with
                                       [ x50 ] ++ _
                                     then
                                       Some
                                         x50
                                     else
                                       None
                                         {},
                                   ty =
                                     match
                                       val29.ty
                                     with
                                       [ x51 ] ++ _
                                     then
                                       Some
                                         x51
                                     else
                                       None
                                         {} } ]
                               val31.fields } },
             { nt =
                 kleene8,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state98: {errors: Ref [(Info, [Char])], content: String}.
                   lam res98.
                     match
                       res98
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           fields =
                             "" } },
             { nt =
                 alt24,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state99: {errors: Ref [(Info, [Char])], content: String}.
                   lam res99.
                     match
                       res99
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           fields =
                             "" } },
             { nt =
                 alt24,
               label =
                 {},
               rhs =
                 [ tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     alt20,
                   ntSym
                     alt21,
                   ntSym
                     kleene8 ],
               action =
                 lam state100: {errors: Ref [(Info, [Char])], content: String}.
                   lam res100.
                     match
                       res100
                     with
                       [ TokParsed (LIdentTok x52),
                         UserSym val32,
                         UserSym val33,
                         UserSym val31 ]
                     in
                     let val32: {ty: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val32
                       in
                       let val33: {e: [Merged], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val33
                       in
                       let val31: {fields: [{e: Option Merged, ty: Option Merged, label: {i: Info, v: String}}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val31
                       in
                       asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               x52.info
                               [ val32.__br_info,
                                 val33.__br_info,
                                 val31.__br_info ],
                           __br_terms =
                             join
                               [ [ x52.info ],
                                 val32.__br_terms,
                                 val33.__br_terms,
                                 val31.__br_terms ],
                           fields =
                             concat
                               [ { label =
                                     match
                                       [ { v =
                                             x52.val,
                                           i =
                                             x52.info } ]
                                     with
                                       [ x53 ] ++ _
                                     in
                                     x53,
                                   e =
                                     match
                                       val33.e
                                     with
                                       [ x54 ] ++ _
                                     then
                                       Some
                                         x54
                                     else
                                       None
                                         {},
                                   ty =
                                     match
                                       val32.ty
                                     with
                                       [ x55 ] ++ _
                                     then
                                       Some
                                         x55
                                     else
                                       None
                                         {} } ]
                               val31.fields } },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "{",
                   ntSym
                     alt24,
                   litSym
                     "}" ],
               action =
                 lam state101: {errors: Ref [(Info, [Char])], content: String}.
                   lam res101.
                     match
                       res101
                     with
                       [ LitParsed l77,
                         UserSym val34,
                         LitParsed l78 ]
                     in
                     let val34: {fields: [{e: Option Merged, ty: Option Merged, label: {i: Info, v: String}}], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val34
                       in
                       asDyn
                         (RecordMergedOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l77.info
                                  [ val34.__br_info,
                                    l78.info ],
                              __br_terms =
                                join
                                  [ [ l77.info ],
                                    val34.__br_terms,
                                    [ l78.info ] ],
                              fields =
                                val34.fields }) },
             { nt =
                 #var"MergedPrefix",
               label =
                 {},
               rhs =
                 [ litSym
                     "!" ],
               action =
                 lam state102: {errors: Ref [(Info, [Char])], content: String}.
                   lam res102.
                     match
                       res102
                     with
                       [ LitParsed l79 ]
                     in
                     asDyn
                         (NotMergedOp
                            { __br_info =
                                l79.info,
                              __br_terms =
                                [ l79.info ] }) },
             { nt =
                 #var"MergedInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "|" ],
               action =
                 lam state103: {errors: Ref [(Info, [Char])], content: String}.
                   lam res103.
                     match
                       res103
                     with
                       [ LitParsed l80 ]
                     in
                     asDyn
                         (OrMergedOp
                            { __br_info =
                                l80.info,
                              __br_terms =
                                [ l80.info ] }) },
             { nt =
                 #var"MergedInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "&" ],
               action =
                 lam state104: {errors: Ref [(Info, [Char])], content: String}.
                   lam res104.
                     match
                       res104
                     with
                       [ LitParsed l81 ]
                     in
                     asDyn
                         (AndMergedOp
                            { __br_info =
                                l81.info,
                              __br_terms =
                                [ l81.info ] }) },
             { nt =
                 #var"MergedInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "++" ],
               action =
                 lam state105: {errors: Ref [(Info, [Char])], content: String}.
                   lam res105.
                     match
                       res105
                     with
                       [ LitParsed l82 ]
                     in
                     asDyn
                         (ConcatMergedOp
                            { __br_info =
                                l82.info,
                              __br_terms =
                                [ l82.info ] }) },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "_" ],
               action =
                 lam state106: {errors: Ref [(Info, [Char])], content: String}.
                   lam res106.
                     match
                       res106
                     with
                       [ LitParsed l83 ]
                     in
                     asDyn
                         (WildMergedOp
                            { __br_info =
                                l83.info,
                              __br_terms =
                                [ l83.info ] }) },
             { nt =
                 #var"MergedInfix",
               label =
                 {},
               rhs =
                 [ litSym
                     "->" ],
               action =
                 lam state107: {errors: Ref [(Info, [Char])], content: String}.
                   lam res107.
                     match
                       res107
                     with
                       [ LitParsed l84 ]
                     in
                     asDyn
                         (ArrowMergedOp
                            { __br_info =
                                l84.info,
                              __br_terms =
                                [ l84.info ] }) },
             { nt =
                 alt25,
               label =
                 {},
               rhs =
                 "",
               action =
                 lam state108: {errors: Ref [(Info, [Char])], content: String}.
                   lam res108.
                     match
                       res108
                     with
                       ""
                     in
                     asDyn
                         { __br_info =
                             NoInfo
                               {},
                           __br_terms =
                             "",
                           rec =
                             "" } },
             { nt =
                 alt25,
               label =
                 {},
               rhs =
                 [ litSym
                     "::",
                   litSym
                     "{",
                   litSym
                     "}" ],
               action =
                 lam state109: {errors: Ref [(Info, [Char])], content: String}.
                   lam res109.
                     match
                       res109
                     with
                       [ LitParsed l85,
                         LitParsed l86,
                         LitParsed l87 ]
                     in
                     asDyn
                         { __br_info =
                             foldl
                               mergeInfo
                               l85.info
                               [ l86.info,
                                 l87.info ],
                           __br_terms =
                             join
                               [ [ l85.info ],
                                 [ l86.info ],
                                 [ l87.info ] ],
                           rec =
                             [ l86.info ] } },
             { nt =
                 #var"MergedPrefix",
               label =
                 {},
               rhs =
                 [ litSym
                     "all",
                   tokSym
                     (LIdentRepr
                        {}),
                   ntSym
                     alt25,
                   litSym
                     "." ],
               action =
                 lam state110: {errors: Ref [(Info, [Char])], content: String}.
                   lam res110.
                     match
                       res110
                     with
                       [ LitParsed l88,
                         TokParsed (LIdentTok x56),
                         UserSym val35,
                         LitParsed l89 ]
                     in
                     let val35: {rec: [Info], __br_info: Info, __br_terms: [Info]} =
                         fromDyn
                           val35
                       in
                       asDyn
                         (AllMergedOp
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l88.info
                                  [ x56.info,
                                    val35.__br_info,
                                    l89.info ],
                              __br_terms =
                                join
                                  [ [ l88.info ],
                                    [ x56.info ],
                                    val35.__br_terms,
                                    [ l89.info ] ],
                              ident =
                                [ { v =
                                      nameNoSym
                                        x56.val,
                                    i =
                                      x56.info } ],
                              rec =
                                val35.rec }) },
             { nt =
                 #var"MergedAtom",
               label =
                 {},
               rhs =
                 [ litSym
                     "(",
                   ntSym
                     #var"Merged",
                   litSym
                     ")" ],
               action =
                 lam #var"".
                   lam seq.
                     match
                       seq
                     with
                       [ LitParsed l90,
                         UserSym ntVal42,
                         LitParsed l91 ]
                     in
                     let ntVal42: (Info, Merged) =
                         fromDyn
                           ntVal42
                       in
                       asDyn
                         (MergedGrouping
                            { __br_info =
                                foldl
                                  mergeInfo
                                  l90.info
                                  [ ntVal42.0,
                                    l91.info ],
                              __br_terms =
                                [ l90.info,
                                  l91.info ],
                              inner =
                                match
                                  [ ntVal42.1 ]
                                with
                                  [ x57 ]
                                in
                                x57 }) },
             { nt =
                 #var"MergedFile",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedFile_lclosed" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState
                               {})) },
             { nt =
                 #var"MergedFile_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedFileAtom",
                   ntSym
                     #var"MergedFile_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addMergedFileOpAtom
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"MergedFile_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedFileInfix",
                   ntSym
                     #var"MergedFile_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addMergedFileOpInfix
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"MergedFile_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedFilePrefix",
                   ntSym
                     #var"MergedFile_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addMergedFileOpPrefix
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"MergedFile_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedFilePostfix",
                   ntSym
                     #var"MergedFile_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addMergedFileOpPostfix
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"MergedFile_lopen",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam p.
                   lam #var"".
                     asDyn
                       (lam st.
                          finalizeMergedFileOp
                            p
                            st) },
             { nt =
                 #var"MergedTop",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedTop_lclosed" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState
                               {})) },
             { nt =
                 #var"MergedTop_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedTopAtom",
                   ntSym
                     #var"MergedTop_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addMergedTopOpAtom
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"MergedTop_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedTopInfix",
                   ntSym
                     #var"MergedTop_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addMergedTopOpInfix
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"MergedTop_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedTopPrefix",
                   ntSym
                     #var"MergedTop_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addMergedTopOpPrefix
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"MergedTop_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedTopPostfix",
                   ntSym
                     #var"MergedTop_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addMergedTopOpPostfix
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"MergedTop_lopen",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam p.
                   lam #var"".
                     asDyn
                       (lam st.
                          finalizeMergedTopOp
                            p
                            st) },
             { nt =
                 #var"Merged",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"Merged_lclosed" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState
                               {})) },
             { nt =
                 #var"Merged_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedAtom",
                   ntSym
                     #var"Merged_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addMergedOpAtom
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"Merged_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedInfix",
                   ntSym
                     #var"Merged_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addMergedOpInfix
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"Merged_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedPrefix",
                   ntSym
                     #var"Merged_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addMergedOpPrefix
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"Merged_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"MergedPostfix",
                   ntSym
                     #var"Merged_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addMergedOpPostfix
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"Merged_lopen",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam p.
                   lam #var"".
                     asDyn
                       (lam st.
                          finalizeMergedOp
                            p
                            st) },
             { nt =
                 #var"Binder",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"Binder_lclosed" ],
               action =
                 lam #var"".
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym cont ]
                     in
                     fromDyn
                         cont
                         (Some
                            (breakableInitState
                               {})) },
             { nt =
                 #var"Binder_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"BinderAtom",
                   ntSym
                     #var"Binder_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addBinderOpAtom
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"Binder_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"BinderInfix",
                   ntSym
                     #var"Binder_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addBinderOpInfix
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"Binder_lclosed",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"BinderPrefix",
                   ntSym
                     #var"Binder_lclosed" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addBinderOpPrefix
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"Binder_lopen",
               label =
                 {},
               rhs =
                 [ ntSym
                     #var"BinderPostfix",
                   ntSym
                     #var"Binder_lopen" ],
               action =
                 lam p.
                   lam seq1.
                     match
                       seq1
                     with
                       [ UserSym x57,
                         UserSym cont ]
                     in
                     asDyn
                         (lam st.
                            fromDyn
                              cont
                              (addBinderOpPostfix
                                 p
                                 (fromDyn
                                    x57)
                                 st)) },
             { nt =
                 #var"Binder_lopen",
               label =
                 {},
               rhs =
                 "",
               action =
                 lam p.
                   lam #var"".
                     asDyn
                       (lam st.
                          finalizeBinderOp
                            p
                            st) } ] })
  in
  match
    target
  with
    Right table
  in
  table
let parseMerged =
  lam filename.
    lam content.
      use ParseMerged
      in
      let config4 =
        { errors =
            ref
              "",
          content =
            content }
      in
      let res111 =
        parseWithTable
          _table
          filename
          config4
          content
      in
      let #var"X" =
        (res111, deref
          config4.errors)
      in
      match
        #var"X"
      with
        (Right dyn, "")
      then
        match
          fromDyn
            dyn
        with
          (_, res111)
        in
        Right
            res111
      else
        match
          #var"X"
        with
          (Left err, errors)
        then
          let err =
            ll1DefaultHighlight
              content
              (ll1ToErrorHighlightSpec
                 err)
          in
          Left
            (snoc
               errors
               err)
        else
          match
            #var"X"
          with
            (_, errors)
          in
          Left
              errors
let parseMergedExn =
  lam filename.
    lam content.
      let #var"X" =
        parseMerged
          filename
          content
      in
      match
        #var"X"
      with
        Left errors
      then
        (for_
             errors
             (lam x57.
                match
                  x57
                with
                  (info, msg)
                in
                printLn
                    (infoErrorString
                       info
                       msg)))
        ; exit
          1
      else
        match
          #var"X"
        with
          Right file
        in
        file
mexpr
{}