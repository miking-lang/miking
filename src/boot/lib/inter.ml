module type PLUG =
  sig
    val residual : unit -> 'a 
  end

let registry : (string, (module PLUG)) Hashtbl.t = Hashtbl.create 1024

let register id m = Hashtbl.add registry id m

let get_plugin id =
  match Hashtbl.find_opt registry id with
  | Some s -> s
  | None -> failwith "No plugin loaded"
