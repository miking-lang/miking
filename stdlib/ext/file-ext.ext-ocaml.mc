
include "ocaml/ast.mc"

let fileExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [
    ("fileExists", [
      { expr = "(fun s -> try Sys.file_exists s with _ -> false)",
        ty = tyarrows_ [otystring_, tybool_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("deleteFile", [
      { expr = "(fun s -> try Sys.remove s with _ -> ())",
        ty = tyarrows_ [otystring_, otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("fileSize", [
      { expr = concat "(fun n -> try let f = open_in_bin n in let s = in_channel_length "
                       "f in let _ = close_in_noerr f in s with _ -> 0)",
        ty = tyarrows_ [otystring_, tyint_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("writeOpen", [
      { expr = "(fun s -> try (open_out_bin s, true) with _ -> (stdout, false))",
        ty = tyarrows_ [otystring_, otytuple_ [otyvarext_ "out_channel" [], tybool_]],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("writeString", [
      { expr = "output_string",
        ty = tyarrows_ [otyvarext_ "out_channel" [], otystring_, otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("writeFlush", [
      { expr = "flush",
        ty = tyarrows_ [otyvarext_ "out_channel" [], otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("writeClose", [
      { expr = "close_out_noerr",
        ty = tyarrows_ [otyvarext_ "out_channel" [], otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("readOpen", [
      { expr = "(fun s -> try (open_in_bin s, true) with _ -> (stdin, false))",
        ty = tyarrows_ [otystring_, otytuple_ [otyvarext_ "in_channel" [], tybool_]],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("readLine", [
      { expr = "(fun rc -> try (input_line rc, false) with | End_of_file -> (\"\",true))",
        ty = tyarrows_ [otyvarext_ "in_channel" [], otytuple_ [otystring_, tybool_]],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("readBytes", [
      { expr = "(fun rc len -> let buf = Bytes.create len in let actual_len = input rc buf 0 len in let reached_eof = actual_len < len in (Bytes.sub_string buf 0 actual_len, reached_eof))",
        ty = tyarrows_ [otyvarext_ "in_channel" [], tyint_, otytuple_ [otystring_, tybool_]],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("readString", [
      { expr = "(fun f -> try really_input_string f (in_channel_length f) with _ -> \"\")",
        ty = tyarrows_ [otyvarext_ "in_channel" [], otystring_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("readClose", [
      { expr = "close_in_noerr",
        ty = tyarrows_ [otyvarext_ "in_channel" [], otyunit_],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("stdin", [
      { expr = "stdin",
        ty = otyvarext_ "in_channel" [],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("stdout", [
      { expr = "stdout",
        ty = otyvarext_ "out_channel" [],
        libraries = [],
        cLibraries = []
      }
    ]),
    ("stderr", [
      { expr = "stderr",
        ty = otyvarext_ "out_channel" [],
        libraries = [],
        cLibraries = []
      }
    ])
  ]
