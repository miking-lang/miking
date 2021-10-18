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
    -- Reading TOML
    ("externalTomlFromStringExn", [
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
    ("externalTomlValueToIntExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TInt v -> v
         | _ -> raise (Invalid_argument \"tomlValueToIntExn\")
      ",
      ty = tyarrows_ [tyTomlValue_, tyint_] }
    ]),
    ("externalTomlValueToStringExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TString v -> v
         | _ -> raise (Invalid_argument \"tomlValueToStringExn\")
      ",
      ty = tyarrows_ [tyTomlValue_, otystring_] }
    ]),
    ("externalTomlValueToFloatExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TFloat v -> v
         | _ -> raise (Invalid_argument \"tomlValueToFloatExn\")
      ",
      ty = tyarrows_ [tyTomlValue_, tyfloat_] }
    ]),
    ("externalTomlValueToTableExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TTable v -> v
         | _ -> raise (Invalid_argument \"tomlValueToTableExn\")
      ",
      ty = tyarrows_ [tyTomlValue_, tyTomlTable_] }
    ]),
    ("externalTomlValueToIntSeqExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TArray (Toml.Types.NodeInt v) -> v
         | _ -> raise (Invalid_argument \"tomlValueToIntSeqExn\")
      ",
      ty = tyarrows_ [tyTomlValue_, otylist_ tyint_] }
    ]),
    ("externalTomlValueToStringSeqExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TArray (Toml.Types.NodeString v) -> v
         | _ -> raise (Invalid_argument \"tomlValueToStringSeqExn\")
      ",
      ty = tyarrows_ [tyTomlValue_, otylist_ otystring_] }
    ]),
    ("externalTomlValueToFloatSeqExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TArray (Toml.Types.NodeFloat v) -> v
         | _ -> raise (Invalid_argument \"tomlValueToFloatSeqExn\")
      ",
      ty = tyarrows_ [tyTomlValue_, otylist_ tyfloat_] }
    ]),
    ("externalTomlValueToTableSeqExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TArray (Toml.Types.NodeTable v) -> v
         | _ -> raise (Invalid_argument \"tomlValueToTableSeqExn\")
      ",
      ty = tyarrows_ [tyTomlValue_, otylist_ tyTomlTable_] }
    ]),

    -- Writing TOML
    ("externalTomlToString", [
      impl { expr = "Toml.Printer.string_of_table",
      ty = tyarrows_ [tyTomlTable_, otystring_] }
    ]),
    ("externalTomlFromBindings", [
      impl { expr =
      "fun binds ->
         Toml.Types.Table.of_key_values
           (List.map (fun (k, v) -> (Toml.Types.Table.Key.of_string k, v)) binds)",
      ty = tyarrows_ [otylist_ (otytuple_ [otystring_, tyTomlValue_]), tyTomlTable_] }
    ]),
    ("externalTomlIntToValue", [
      impl { expr = "fun x -> Toml.Types.TInt x",
      ty = tyarrows_ [tyint_, tyTomlValue_] }
    ]),
    ("externalTomlStringToValue", [
      impl { expr = "fun x -> Toml.Types.TString x",
      ty = tyarrows_ [otystring_, tyTomlValue_] }
    ]),
    ("externalTomlFloatToValue", [
      impl { expr = "fun x -> Toml.Types.TFloat x",
      ty = tyarrows_ [tyfloat_, tyTomlValue_] }
    ]),
    ("externalTomlTableToValue", [
      impl { expr = "fun x -> Toml.Types.TTable x",
      ty = tyarrows_ [tyTomlTable_, tyTomlValue_] }
    ]),
    ("externalTomlIntSeqToValue", [
      impl { expr = "fun x -> Toml.Types.TArray (Toml.Types.NodeInt x)",
      ty = tyarrows_ [otylist_ tyint_, tyTomlValue_] }
    ]),
    ("externalTomlStringSeqToValue", [
      impl { expr = "fun x -> Toml.Types.TArray (Toml.Types.NodeString x)",
      ty = tyarrows_ [otylist_ otystring_, tyTomlValue_] }
    ]),
    ("externalTomlFloatSeqToValue", [
      impl { expr = "fun x -> Toml.Types.TArray (Toml.Types.NodeFloat x)",
      ty = tyarrows_ [otylist_ tyfloat_, tyTomlValue_] }
    ]),
    ("externalTomlTableSeqToValue", [
      impl { expr = "fun x -> Toml.Types.TArray (Toml.Types.NodeTable x)",
      ty = tyarrows_ [otylist_ tyTomlTable_, tyTomlValue_] }
    ])
  ]
