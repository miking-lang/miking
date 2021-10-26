
include "ocaml/ast.mc"


let asyncExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("asyncSleep", [
      { ident = "Lwt_unix.sleep",
        ty = tyarrows_ [tyfloat_, otyvarext_ "'a Lwt.t"],
        libraries = ["lwt.unix"],
        cLibraries = []
      }
    ]),
    ("asyncRun", [
      { ident = "Lwt_main.run",
        ty = tyarrows_ [otyvarext_ "'a Lwt.t", otyvarext_ "'a"],
        libraries = ["lwt.unix"],
        cLibraries = []
      }
    ])
  ]
