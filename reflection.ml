open Binsec
open Libsse
open Types
open Ir

include Cli.Make (struct
  let name = "Symbolic Reflection API"

  let shortname = "reflection"
end)

type Ast.Instr.t +=
  | IsSymbolic of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc

type builtin += IsSymbolicBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t

module Reflection (P : Path.S) (S : STATE) :
  Exec.EXTENSION with type path = P.t and type state = S.t = struct
  type path = P.t

  and state = S.t

  let initialization_callback = None

  let declaration_callback = None

  (* translate the Ast.Instr.t to the builtin *)
  (* (Ast.Instr.t -> Script.env -> Ir.fallthrough list) option *)
  let instruction_callback =
    Some
      (fun inst env ->
        match inst with
        | IsSymbolic (lval, sym_var, length) -> (
          match Script.eval_loc ~size:1 lval env with
          | Var var ->
              [ Builtin
                  (IsSymbolicBuiltin
                     ( var
                     , Script.eval_expr sym_var env
                     , Script.eval_expr length env ) ) ]
          | Restrict (var, {hi; lo}) ->
              [] (* TODO *)
          | Store (bytes, dir, addr, base) ->
              [] (* TODO *) )
        | _ ->
            [] )

  let process_callback = None

  (* Perform action of builtin, so here call get_value *)
  (* (Ir.builtin ->
     (Virtual_address.t ->
     path ->
     int ->
     state ->
     (state, Types.status) Result.t)
     option)
     option
  *)
  let builtin_callback =
    Some
      (function IsSymbolicBuiltin (lval, sym_var, length) -> None | _ -> None)

  let builtin_printer = None

  let at_exit_callback = None
end

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
                  ; Dyp.Regexp (RE_Char ',')
                  ; Dyp.Non_ter ("expr", No_priority)
                  ; Dyp.Regexp (RE_Char ')') ]
                , "default_priority"
                , [] )
              , fun _ -> function
                  | [ Libparser.Syntax.Loc lval
                    ; _
                    ; _
                    ; _
                    ; Libparser.Syntax.Expr sym_var
                    ; _
                    ; Libparser.Syntax.Expr length
                    ; _ ] ->
                      ( Libparser.Syntax.Instr
                          (IsSymbolic (lval, sym_var, length))
                      , [] )
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
        if is_enabled () then Some (module Reflection ((val path)) ((val state)))
        else None
    end : Exec.PLUGIN )
