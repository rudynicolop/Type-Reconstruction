open Core
open Vtr

(** Command flags. *)
let mono_flag = "-mono"
let eval_flag = "-eval"
let type_flag = "-type"

(** Command summaries. *)
let eval_summary = "execute a (typeable) program under cbn"
let type_summary = "only type a program"


let cmd_skel f msg run =
  Command.basic ~summary:msg
    Command.Param.(
      map
        (anon ("filename" %: string))
        ~f:(fun filename _ -> f filename run))

(** Commands for monomorphic type-reconstruction. *)
let mono_cmd =
  Command.group
    ~summary:"monomorphic type-reconstruction"
    [eval_flag, cmd_skel Run.pipeline eval_summary true;
     type_flag, cmd_skel Run.pipeline eval_summary false]

let cmd =
  Command.group
    ~summary:"type-reconstruction"
    [mono_flag, mono_cmd]

let () = Command.run ~version:"1.0" cmd
