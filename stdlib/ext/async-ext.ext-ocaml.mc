
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
    ]),
    ("asyncBind", [
      { ident = "Lwt.bind",
        ty = tyarrows_ [otyvarext_ "'a Lwt.t",
                (tyarrows_ [otyvarext_ "'a", otyvarext_ "'b Lwt.t"]), otyvarext_ "'b Lwt.t"],
        libraries = ["lwt.unix"],
        cLibraries = []
      }
    ]),
    ("asyncPrint", [
      { ident = "Lwt_io.print",
        ty = tyarrows_ [otystring_ , otyvarext_ "unit Lwt.t"],
        libraries = ["lwt.unix"],
        cLibraries = []
      }
    ]),
    ("asyncReturn", [
      { ident = "Lwt.return",
        ty = tyarrows_ [otyvarext_ "'a", otyvarext_ "'a Lwt.t"],
        libraries = ["lwt.unix"],
        cLibraries = []
      }
    ])
  ]
