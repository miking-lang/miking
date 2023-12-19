include "map.mc"
include "ocaml/ast.mc"

let tyTomlTable_ = otyvarext_ "Toml.Types.table" []
let tyTomlValue_ = otyvarext_ "Toml.Types.value" []

let impl = lam arg : { expr : String, ty : use Ast in Type }.
  { expr = arg.expr, ty = arg.ty, libraries = ["toml"], cLibraries = [] }

let tomlExtMap =
  use OCamlAst in
  mapFromSeq cmpString
  [
    -- Reading TOML
    ("externalTomlFromStringExn", [
      impl { expr = "fun s ->
        match Toml.Parser.from_string s with
        | `Ok table -> table
        | `Error (str, loc) ->
          raise (Invalid_argument (\"tomlFromStringExn: \"
            ^ str ^ \" when parsing: \"
            ^ s))",
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
         | _ -> raise (Invalid_argument (\"tomlValueToIntExn: \" ^ (Toml.Printer.string_of_value v)))
      ",
      ty = tyarrows_ [tyTomlValue_, tyint_] }
    ]),
    ("externalTomlValueToStringExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TString v -> v
         | _ -> raise (Invalid_argument (\"tomlValueToStringExn: \" ^ (Toml.Printer.string_of_value v)))
      ",
      ty = tyarrows_ [tyTomlValue_, otystring_] }
    ]),
    ("externalTomlValueToFloatExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TFloat v -> v
         | _ -> raise (Invalid_argument (\"tomlValueToFloatExn: \" ^ (Toml.Printer.string_of_value v)))
      ",
      ty = tyarrows_ [tyTomlValue_, tyfloat_] }
    ]),
    ("externalTomlValueToBoolExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TBool v -> v
         | _ -> raise (Invalid_argument (\"tomlValueToBoolExn: \" ^ (Toml.Printer.string_of_value v)))
      ",
      ty = tyarrows_ [tyTomlValue_, tybool_] }
    ]),
    ("externalTomlValueToTableExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TTable v -> v
         | _ -> raise (Invalid_argument (\"tomlValueToTableExn: \" ^ (Toml.Printer.string_of_value v)))
      ",
      ty = tyarrows_ [tyTomlValue_, tyTomlTable_] }
    ]),
    ("externalTomlValueToIntSeqExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TArray (Toml.Types.NodeInt v) -> v
         | Toml.Types.TArray Toml.Types.NodeEmpty -> []
         | _ -> raise (Invalid_argument (\"tomlValueToIntSeqExn: \" ^ (Toml.Printer.string_of_value v)))
      ",
      ty = tyarrows_ [tyTomlValue_, otylist_ tyint_] }
    ]),
    ("externalTomlValueToStringSeqExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TArray (Toml.Types.NodeString v) -> v
         | Toml.Types.TArray Toml.Types.NodeEmpty -> []
         | _ ->
           raise (Invalid_argument (\"tomlValueToStringSeqExn: \" ^ (Toml.Printer.string_of_value v)))
      ",
      ty = tyarrows_ [tyTomlValue_, otylist_ otystring_] }
    ]),
    ("externalTomlValueToFloatSeqExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TArray (Toml.Types.NodeFloat v) -> v
         | Toml.Types.TArray Toml.Types.NodeEmpty -> []
         | _ -> raise (Invalid_argument (\"tomlValueToFloatSeqExn: \" ^ (Toml.Printer.string_of_value v)))
      ",
      ty = tyarrows_ [tyTomlValue_, otylist_ tyfloat_] }
    ]),
    ("externalTomlValueToTableSeqExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TArray (Toml.Types.NodeTable v) -> v
         | Toml.Types.TArray Toml.Types.NodeEmpty -> []
         | _ -> raise (Invalid_argument (\"tomlValueToTableSeqExn: \" ^ (Toml.Printer.string_of_value v)))
      ",
      ty = tyarrows_ [tyTomlValue_, otylist_ tyTomlTable_] }
    ]),
    ("externalTomlValueToSeqSeqExn", [
      impl { expr =
      "fun v -> match v with
         | Toml.Types.TArray (Toml.Types.NodeArray a) ->
           List.map (fun e -> Toml.Types.TArray e) a
         | _ -> raise (Invalid_argument (\"tomlValueToSeqSeqExn: \" ^ (Toml.Printer.string_of_value v)))
      ",
      ty = tyarrows_ [tyTomlValue_, otylist_ tyTomlValue_] }
    ]),
    ("externalTomlValueToString", [
      impl { expr = "Toml.Printer.string_of_value",
      ty = tyarrows_ [tyTomlValue_, otystring_] }
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
    ]),
    ("externalTomlSeqSeqToValue", [
      impl { expr =
      "fun x ->
         let a = List.map (fun e -> match e with
           | Toml.Types.TArray a -> a
           | _ ->
             raise (Invalid_argument (\"tomlSeqSeqToValue: \"
                                     ^ (Toml.Printer.string_of_value e)))) x in
         Toml.Types.TArray (Toml.Types.NodeArray a)
      ",
      ty = tyarrows_ [otylist_ tyTomlValue_, tyTomlValue_] }
    ])

  ]
