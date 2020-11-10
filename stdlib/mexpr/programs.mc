-- Common program fragments often used for unit testing

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"

let programsOddEven =
  reclets_ [

    ("odd", tyarrow_ tyint_ tybool_,
     lam_ "x" (tyint_)
       (if_ (eqi_ (var_ "x") (int_ 1))
          true_
          (if_ (lti_ (var_ "x") (int_ 1))
             false_
             (app_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))),

    ("even", tyarrow_ tyint_ tybool_,
     lam_ "x" (tyint_)
       (if_ (eqi_ (var_ "x") (int_ 0))
          true_
          (if_ (lti_ (var_ "x") (int_ 0))
             false_
             (app_ (var_ "odd") (subi_ (var_ "x") (int_ 1))))))

  ]

let programsFactorial =
  reclet_ "factorial" (tyarrow_ tyint_ tyint_)
    (lam_ "n" (tyint_)
      (if_ (eqi_ (var_ "n") (int_ 0))
        (int_ 1)
        (muli_ (var_ "n")
           (app_ (var_ "factorial") (subi_ (var_ "n") (int_ 1))))))

