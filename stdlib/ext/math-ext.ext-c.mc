include "map.mc"

let mathExtMap: ExtMap =
  mapFromSeq cmpString [

    ( "externalExp"
    , { ident = "exp", header = "<math.h>" }
    ),

    ( "externalLog"
    , { ident = "log", header = "<math.h>" }
    ),

    ( "externalPow"
    , { ident = "pow", header = "<math.h>" }
    ),

    ( "externalSin"
    , { ident = "sin", header = "<math.h>" }
    ),

    ( "externalCos"
    , { ident = "cos", header = "<math.h>" }
    )

  ]
