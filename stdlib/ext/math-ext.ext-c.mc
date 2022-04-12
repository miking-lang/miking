include "map.mc"
include "c/ast.mc"

let mathExtMap: ExtMap =
  use CExprTypeAst in
  mapFromSeq cmpString [

    ( "externalExp"
    , { ident = "exp", header = "<math.h>", ty = CTyDouble ()
      , argTypes = [CTyDouble ()] }
    ),

    ( "externalLog"
    , { ident = "log", header = "<math.h>", ty = CTyDouble ()
      , argTypes = [CTyDouble ()] }
    ),

    ( "externalPow"
    , { ident = "pow", header = "<math.h>", ty = CTyDouble ()
      , argTypes = [CTyDouble (), CTyDouble ()] }
    ),

    ( "externalSin"
    , { ident = "sin", header = "<math.h>", ty = CTyDouble ()
      , argTypes = [CTyDouble ()] }
    ),

    ( "externalCos"
    , { ident = "cos", header = "<math.h>", ty = CTyDouble ()
      , argTypes = [CTyDouble ()] }
    )

  ]
