open Repl
open Jupyter_kernel

let init () =
  Lwt.return (Py.initialize ())

let exec ~count:_ code =
  try
    let ast = parse_prog_or_mexpr code in
    let result = ast |> repl_eval_ast |> Pprint.ustring_of_tm |> Ustring.to_utf8 in
    Lwt.return (Ok { Client.Kernel.msg=Some(result)
                   ; Client.Kernel.actions=[]})
  with e -> Lwt.return (Error (Printexc.to_string e))

let main =
  let mcore_kernel =
    Client.Kernel.make
      ~language:"MCore"
      ~language_version:[0; 1]
      ~file_extension:".mc"
      ~codemirror_mode:"ocaml"
      ~banner:"The core language of Miking - a meta language system
for creating embedded domain-specific and general-purpose languages"
      ~init:init
      ~exec:exec
      () in
      let config = Client_main.mk_config ~usage:"Usage: hello" () in
      let newstdout = open_out "redirected" in
      Unix.dup2 (Unix.descr_of_out_channel newstdout) Unix.stdout;
      Lwt_main.run (Client_main.main ~config:config ~kernel:mcore_kernel);
      flush stdout;
