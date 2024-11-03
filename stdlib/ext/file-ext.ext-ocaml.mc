
include "ocaml/ast.mc"

let fileExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("externalFileExists", [
      { expr = "(fun s -> try Sys.file_exists s with _ -> false)",
        ty = tyarrows_ [otystring_, tybool_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalDeleteFile", [
      { expr = "(fun s -> try Sys.remove s with _ -> ())",
        ty = tyarrows_ [otystring_, otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalFileSize", [
      { expr = concat "(fun n -> try let f = open_in_bin n in let s = in_channel_length "
                       "f in let _ = close_in_noerr f in s with _ -> 0)",
        ty = tyarrows_ [otystring_, tyint_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalWriteOpen", [
      { expr = "(fun s -> try (open_out_bin s, true) with _ -> (stdout, false))",
        ty = tyarrows_ [otystring_, otytuple_ [otyvarext_ "out_channel" [], tybool_]],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalWriteString", [
      { expr = "output_string",
        ty = tyarrows_ [otyvarext_ "out_channel" [], otystring_, otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalWriteFlush", [
      { expr = "flush",
        ty = tyarrows_ [otyvarext_ "out_channel" [], otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalWriteClose", [
      { expr = "close_out_noerr",
        ty = tyarrows_ [otyvarext_ "out_channel" [], otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalReadOpen", [
      { expr = "(fun s -> try (open_in_bin s, true) with _ -> (stdin, false))",
        ty = tyarrows_ [otystring_, otytuple_ [otyvarext_ "in_channel" [], tybool_]],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalReadLine", [
      { expr = "(fun rc -> try (input_line rc, false) with | End_of_file -> (\"\",true))",
        ty = tyarrows_ [otyvarext_ "in_channel" [], otytuple_ [otystring_, tybool_]],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalReadString", [
      { expr = "(fun f -> try really_input_string f (in_channel_length f) with _ -> \"\")",
        ty = tyarrows_ [otyvarext_ "in_channel" [], otystring_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalReadClose", [
      { expr = "close_in_noerr",
        ty = tyarrows_ [otyvarext_ "in_channel" [], otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalStdin", [
      { expr = "stdin",
        ty = otyvarext_ "in_channel" [],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalStdout", [
      { expr = "stdout",
        ty = otyvarext_ "out_channel" [],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("externalStderr", [
      { expr = "stderr",
        ty = otyvarext_ "out_channel" [],
        libraries = [],
        cLibraries = []
      }
    ])
  ]
