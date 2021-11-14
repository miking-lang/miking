
include "ocaml/ast.mc"

let fileExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("writeOpen", [
      { expr = "open_out_bin",
        ty = tyarrows_ [otystring_, otyvarext_ "out_channel"],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("writeString", [
      { expr = "output_string",
        ty = tyarrows_ [otyvarext_ "out_channel", otystring_, otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("writeFlush", [
      { expr = "flush",
        ty = tyarrows_ [otyvarext_ "out_channel", otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("writeClose", [
      { expr = "close_out_noerr",
        ty = tyarrows_ [otyvarext_ "out_channel", otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("readOpen", [
      { expr = "open_in_bin",
        ty = tyarrows_ [otystring_, otyvarext_ "in_channel"],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalReadLine", [
      { expr = "(fun rc -> try (input_line rc, false) with | End_of_file -> (\"\",true))",
        ty = tyarrows_ [otyvarext_ "in_channel", otytuple_ [otystring_, tybool_]],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("readClose", [
      { expr = "close_in_noerr",
        ty = tyarrows_ [otyvarext_ "in_channel", otyunit_],
        libraries = [],
        cLibraries = []
      }
    ])
  ]
