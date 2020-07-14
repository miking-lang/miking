open Repl
open Jupyter_kernel

let current_output = ref (BatIO.output_string ())

let text_data_of_string str =
  Client.Kernel.mime ~ty:"text/plain" str

let init () =
  let kernel_output_string str = BatIO.nwrite !current_output str in
  let kernel_output_ustring ustr = ustr |> Ustring.to_utf8 |> kernel_output_string in
  Mexpr.program_output := kernel_output_ustring;
  Py.initialize ~version:3 ();
  let py_init_print = "
import sys
from ocaml import ocaml_print
class OCamlPrint:
    def write(self, str):
        ocaml_print(str)

sys.stdout = OCamlPrint()
" in
  let m = Py.Import.add_module "ocaml" in
  let py_ocaml_print args =
    kernel_output_string (Py.String.to_string args.(0));
    Py.none
  in
  Py.Module.set_function m "ocaml_print" py_ocaml_print;
  ignore (Py.Run.eval ~start:Py.File py_init_print);
  Lwt.return ()

let exec ~count:_ code =
  try
    let ast = parse_prog_or_mexpr code in
    let result = ast |> repl_eval_ast |> Pprint.ustring_of_tm |> Ustring.to_utf8 in
    let actions = [text_data_of_string result] in
    let new_actions =
      match BatIO.close_out !current_output with
      | "" -> actions
      | s -> text_data_of_string s :: actions
    in
    current_output := BatIO.output_string ();
    Lwt.return (Ok { Client.Kernel.msg=None
                   ; Client.Kernel.actions=new_actions})
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
