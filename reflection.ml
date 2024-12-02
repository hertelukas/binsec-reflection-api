open Binsec
open Libsse
open Types
open Ir

include Cli.Make (struct
  let name = "Symbolic Reflection API"

  let shortname = "reflection"
end)

type Ast.Instr.t += IsSymbolic of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc

type builtin += IsSymbolicBuiltin of Dba.LValue.t * Dba.Expr.t

let () =
  Exec.register_plugin
    ( module struct
      let name = "reflection"

      (* sse/plugin/checkct

           in sse/types, check if get_value raises excpetion -> symbolic

            rule fallthrough
            Token("lvalue")
            String(":=")
            String("is_symbolic")
            char('(')
            Toke("arg")
            char(')')

         type Ast.Instr.t += ...Will call script function IsSymbolic of Lvalue.t.loc * Expr.t loc <- loc is to identify which line caused the error

         type builtin += IsSymbolic of Dba.Lvalue * Dba.Expr.t
      *)
      let grammar_extension =
        [ Dyp.Add_rules
            [ ( ( "fallthrough"
                , [ Dyp.Non_ter ("loc", No_priority)
                  ; Dyp.Regexp (RE_String ":=")
                  ; Dyp.Regexp (RE_String "is_symbolic")
                  ; Dyp.Regexp (RE_Char '(')
                  ; Dyp.Non_ter ("expr", No_priority)
                  ; Dyp.Regexp (RE_Char ')') ]
                , "default_priority"
                , [] )
              , fun _ -> function
                  | [ Libparser.Syntax.Loc lval
                    ; _
                    ; _
                    ; _
                    ; Libparser.Syntax.Expr exp
                    ; _ ] ->
                      (Libparser.Syntax.Instr (IsSymbolic (lval, exp)), [])
                  | _ ->
                      assert false ) ] ]

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

              (* translate the Ast.Instr.t to the builtin *)
              let instruction_callback =
                Some
                  (fun inst env ->
                    match inst with IsSymbolic (lval, expr) -> [] | _ -> [] )

              let process_callback = None

              (* Perform action of builtin, so here call get_value *)
              let builtin_callback = None

              let builtin_printer = None

              let at_exit_callback = None
            end )
        else None
    end : Exec.PLUGIN )
