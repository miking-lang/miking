include "common.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"

mexpr

let nMatches =
  if gti (length argv) 1 then
    string2int (get argv 1)
  else
    10
in

use MExprPrettyPrint in

let ast = bindall_ [
  ulet_ "rc" (urecord_ [("y1", int_ 2), ("y2", float_ 50.25), ("y3", str_ "Why three")]),
  ulet_ "square" (ulam_ "x" (muli_ (var_ "x")
                                   (var_ "x"))),
  ulet_ "_" (appf1_ (var_ "printLn")
                   (appf1_ (var_ "int2string")
                           (appf1_ (var_ "square")
                                   (int_ 5)))),
  -- A long chained match expression
  matchall_ (
    create nMatches (lam i: Int.
      matchex_ (var_ "foo") (pand_ (pint_ i) (pvar_ "x")) (
        bindall_ [
            ulet_ "rc2" (recordupdate_ (recordupdate_ (recordupdate_ (var_ "rc")
                                                                     "y1" (int_ i))
                                                       "y2" (float_ 30.33))
                                        "y3" (str_ "in match")),
            ulet_ "x2" (appf1_ (var_ "square") (var_ "x")),
            appf1_ (var_ "printLn") (
                appf1_ (var_ "join") (seq_ [
                    str_ "foo is ",
                    appf1_ (var_ "int2string")
                           (var_ "x2")
                ])
            )
        ]
      )
    )
  )
] in

printLn (expr2str ast)
