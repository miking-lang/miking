include "ocaml/ast.mc"

let intrinsicOpSeq = use OCamlAst in
  concat "Boot.Intrinsics.Mseq."

let intrinsicOpSymb = use OCamlAst in
  concat "Boot.Intrinsics.Symb."

let intrinsicOpFloat = use OCamlAst in
  concat "Boot.Intrinsics.FloatConversion."

let intrinsicOpFile = use OCamlAst in
  concat "Boot.Intrinsics.File."

let intrinsicOpIO = use OCamlAst in
  concat "Boot.Intrinsics.IO."

let intrinsicOpSys = use OCamlAst in
  concat "Boot.Intrinsics.MSys."

let intrinsicOpRand = use OCamlAst in
  concat "Boot.Intrinsics.RNG."

let intrinsicOpTime = use OCamlAst in
  concat "Boot.Intrinsics.Time."

let intrinsicOpConTag = use OCamlAst in
  concat "Boot.Intrinsics.ConTag."

let intrinsicOpTensor = use OCamlAst in
  concat "Boot.Intrinsics.T."

let intrinsicOpBootparser = use OCamlAst in
  concat "Boot.Bootparser."
