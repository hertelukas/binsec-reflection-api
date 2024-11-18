open Binsec
open Libsse
open Types

include Cli.Make (struct
  let name = "Symbolic Reflection API"

  let shortname = "reflection"
end)

let () =
  Exec.register_plugin
    ( module struct
      let name = "reflection"

      let grammar_extension = []

      let instruction_printer = None

      let declaration_printer = None

      let extension :
          type a b.
             (module EXPLORATION_STATISTICS)
          -> (module Path.S with type t = a)
          -> (module STATE with type t = b)
          -> (module Exec.EXTENSION with type path = a and type state = b)
             option =
       fun _stats path state ->
        if is_enabled () then
          Some
            ( module struct
              module P = (val path)

              module S = (val state)

              type path = P.t

              and state = S.t

              let initialization_callback = None

              let declaration_callback = None

              let instruction_callback = None

              let process_callback = None

              let builtin_callback = None

              let builtin_printer = None

              let at_exit_callback = None
            end )
        else None
    end : Exec.PLUGIN )
