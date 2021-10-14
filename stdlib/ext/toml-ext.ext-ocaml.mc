include "map.mc"
include "ocaml/ast.mc"

let tyTomlTable_ = otyvarext_ "Toml.Types.table"
let tyTomlValue_ = otyvarext_ "Toml.Types.value"

let impl = lam arg : { expr : String, ty : Type }.
  { expr = arg.expr, ty = arg.ty, libraries = ["toml"], cLibraries = [] }

let tomlExtMap =
  use OCamlAst in
  mapFromSeq cmpString
  [
    ("externalTomlFromString", [
      impl { expr = "fun s -> Toml.Parser.(from_string s |> unsafe)",
      ty = tyarrows_ [otystring_, tyTomlTable_] }
    ]),
    ("externalTomlFindExn", [
      impl { expr = "fun key table -> Toml.Types.Table.find (Toml.Min.key key) table",
      ty = tyarrows_ [otystring_, tyTomlTable_, tyTomlValue_] }
    ]),
    ("externalTomlBindings", [
      impl { expr = "fun table ->
        List.map
          (fun (k, v) -> (Toml.Types.Table.Key.to_string k, v))
          (Toml.Types.Table.bindings table)
      ",
      ty = tyarrows_ [tyTomlTable_, otylist_ (otytuple_ [otystring_, tyTomlValue_])] }
    ]),
    ("externalTomlValueToInt", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TInt v -> v
         | _ -> raise (Invalid_argument \"tomlValueToInt\")
      ",
      ty = tyarrows_ [tyTomlValue_, tyint_] }
    ])

  ]
