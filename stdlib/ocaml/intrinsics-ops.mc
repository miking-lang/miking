include "ocaml/ast.mc"

let intrinsicOpSeq = use OCamlAst in
  lam op. OTmVarExt {ident = concat "Boot.Intrinsics.Mseq." op}

let intrinsicOpSymb = use OCamlAst in
  lam op. OTmVarExt {ident = concat "Boot.Intrinsics.Symb." op}

let intrinsicOpFloat = use OCamlAst in
  lam op. OTmVarExt {ident = concat "Boot.Intrinsics.FloatConversion." op}

let intrinsicOpFile = use OCamlAst in
  lam op. OTmVarExt {ident = concat "Boot.Intrinsics.File." op}

let intrinsicOpIO = use OCamlAst in
  lam op. OTmVarExt {ident = concat "Boot.Intrinsics.IO." op}

let intrinsicOpSys = use OCamlAst in
  lam op. OTmVarExt {ident = concat "Boot.Intrinsics.MSys." op}

let intrinsicOpRand = use OCamlAst in
  lam op. OTmVarExt {ident = concat "Boot.Intrinsics.RNG." op}

let intrinsicOpTime = use OCamlAst in
  lam op. OTmVarExt {ident = concat "Boot.Intrinsics.Time." op}

let intrinsicOpTensor = use OCamlAst in
  lam op. OTmVarExt {ident = concat "Boot.Intrinsics.T." op}

let intrinsicOpBootparser = use OCamlAst in
  lam op. OTmVarExt {ident = concat "Boot.Bootparser." op}

let intrinsicOpMap = use OCamlAst in
  lam op. OTmVarExt {ident = concat "Boot.Intrinsics.Mmap." op}
