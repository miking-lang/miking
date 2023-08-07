open Ustring.Op
open Intrinsics
open Ast

module SymbOrd = struct
  type t = Symb.t

  let compare = Symb.compare
end

module SymbSet = Set.Make (SymbOrd)
module SymbMap = Map.Make (SymbOrd)

(* From a term, create the map from symbols to text strings *)
let symbmap t =
  let rec work acc = function
    | TmVar (_, x, s, _, _) ->
        SymbMap.add s x acc
    | TmLam (_, x, s, _, _, t)
    | TmConDef (_, x, s, _, t)
    | TmConApp (_, x, s, t) ->
        work (SymbMap.add s x acc) t
    | TmLet (_, x, s, _, t1, t2) ->
        work (work (SymbMap.add s x acc) t1) t2
    | TmRecLets (_, lst, t1) ->
        work
          (List.fold_left
             (fun acc (_, x, s, _, t) -> work (SymbMap.add s x acc) t)
             acc lst )
          t1
    | TmExt (_, x, s, _, _, t) ->
        work (SymbMap.add s x acc) t
    | t ->
        sfold_tm_tm work acc t
  in
  work SymbMap.empty t

let pprint_symb s = us (Printf.sprintf "%d" (Symb.hash s))

let pprint_named_symb symbmap s = SymbMap.find s symbmap

let pprint_symbset ss =
  us "{"
  ^. ( ss |> SymbSet.elements |> List.map pprint_symb
     |> Ustring.concat (us ", ") )
  ^. us "}"

let pprint_named_symbset symbmap ss =
  us "{"
  ^. ( ss |> SymbSet.elements
     |> List.map (fun s -> SymbMap.find s symbmap)
     |> Ustring.concat (us ", ") )
  ^. us "}"

let pprint_symbmap symbmap =
  let f k x acc = acc ^. x ^. us " -> " ^. pprint_symb k in
  SymbMap.fold f symbmap (us "")
