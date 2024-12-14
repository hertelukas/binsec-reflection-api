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
  | Maximize of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | Minimize of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | NewSymVar of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc

type builtin +=
  | IsSymbolicBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t
  | NewSymVarBuiltin of Dba.Var.t * Dba.Expr.t

module Reflection (P : Path.S) (S : STATE) :
  Exec.EXTENSION with type path = P.t and type state = S.t = struct
  type path = P.t

  and state = S.t

  module Eval = Eval.Make (P) (S)

  let initialization_callback = None

  let declaration_callback = None

  (* translate the Ast.Instr.t to the builtin *)
  (* (Ast.Instr.t -> Script.env -> Ir.fallthrough list) option *)
  let instruction_callback =
    let symbolic = Printf.sprintf "%%symbolic%%%d" in
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
              let size' = hi - lo + 1 in
              let name' = symbolic size' in
              let var' = Dba.Var.temporary name' (Size.Bit.create size') in
              let rval =
                Dba_utils.Expr.complement (Dba.Expr.v var') ~lo ~hi var
              in
              [ Builtin
                  (IsSymbolicBuiltin
                     ( var'
                     , Script.eval_expr sym_var env
                     , Script.eval_expr length env ) )
              ; Assign {var; rval} ]
          | Store (bytes, dir, addr, base) ->
              let size' = 8 * bytes in
              let name' = symbolic size' in
              let var' = Dba.Var.temporary name' (Size.Bit.create size') in
              let rval = Dba.Expr.v var' in
              [ Builtin
                  (IsSymbolicBuiltin
                     ( var'
                     , Script.eval_expr sym_var env
                     , Script.eval_expr length env ) )
              ; Store {base; dir; addr; rval} ] )
        | NewSymVar (lval, length) -> (
          match Script.eval_loc lval env with
          | Var var ->
              [Builtin (NewSymVarBuiltin (var, Script.eval_expr length env))]
          | Restrict (var, {hi; lo}) ->
              [] (* TODO *)
          | Store (bytes, dir, addr, base) ->
              [] (* TODO *) )
        | _ ->
            [] )

  let process_callback = None

  let is_symbolic dst_var sym_var length _ path _ state : (S.t, status) Result.t
      =
    let sym_var, state = Eval.safe_eval sym_var state path in
    let length, state = Eval.safe_eval length state path in
    let length = Bitvector.to_uint (S.get_value length state) in
    (* TODO assert length % 8 == 0 *)
    let sym_var, state =
      S.read ~addr:sym_var (length / 8) Machine.LittleEndian state
    in
    match S.get_value sym_var state with
    | exception Non_unique ->
        (* Value is concrete *)
        let new_state =
          S.assign dst_var
            (S.Value.constant (Bitvector.ones dst_var.size))
            state
        in
        Ok new_state
    | _ ->
        (* Value is symbolic *)
        let new_state =
          S.assign dst_var
            (S.Value.constant (Bitvector.zeros dst_var.size))
            state
        in
        Ok new_state

  let new_sym_var dst_var length _ path _ state : (S.t, status) Result.t =
    let length, state = Eval.safe_eval length state path in
    let length = Bitvector.to_uint (S.get_value length state) in
    let state =
      (* TODO probably wrong, as I don't want to create a constant *)
      S.assign dst_var (S.Value.constant (Bitvector.ones length)) state
    in
    Ok state

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
      (function
      | IsSymbolicBuiltin (lval, sym_var, length) ->
          Some (is_symbolic lval sym_var length)
      | NewSymVarBuiltin (lval, length) ->
          Some (new_sym_var lval length)
      | _ ->
          None )

  let builtin_printer = None

  let at_exit_callback = None
end

let () =
  Exec.register_plugin
    ( module struct
      let name = "reflection"

      (* Build parser for l:=func(arg1, arg2) *)
      let loc_expr_expr_parser func_name =
        ( "fallthrough"
        , [ Dyp.Non_ter ("loc", No_priority)
          ; Dyp.Regexp (RE_String ":=")
          ; Dyp.Regexp (RE_String func_name)
          ; Dyp.Regexp (RE_Char '(')
          ; Dyp.Non_ter ("expr", No_priority)
          ; Dyp.Regexp (RE_Char ',')
          ; Dyp.Non_ter ("expr", No_priority)
          ; Dyp.Regexp (RE_Char ')') ]
        , "default_priority"
        , [] )

      (* Applies instr to l = (arg1, arg2) *)
      let loc_expr_expr_instr instr = function
        | [ Libparser.Syntax.Loc lval
          ; _
          ; _
          ; _
          ; Libparser.Syntax.Expr arg1
          ; _
          ; Libparser.Syntax.Expr arg2
          ; _ ] ->
            (Libparser.Syntax.Instr (instr (lval, arg1, arg2)), [])
        | _ ->
            assert false

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
            [ ( loc_expr_expr_parser "maximize"
              , fun _ ->
                  loc_expr_expr_instr (fun (lval, sym_var, length) ->
                      Maximize (lval, sym_var, length) ) )
            ; ( loc_expr_expr_parser "minimize"
              , fun _ ->
                  loc_expr_expr_instr (fun (lval, sym_var, length) ->
                      Minimize (lval, sym_var, length) ) )
            ; ( loc_expr_expr_parser "is_symbolic"
              , fun _ ->
                  loc_expr_expr_instr (fun (lval, sym_var, length) ->
                      IsSymbolic (lval, sym_var, length) ) )
            ; ( ( "fallthrough"
                , [ Dyp.Non_ter ("loc", No_priority)
                  ; Dyp.Regexp (RE_String ":=")
                  ; Dyp.Regexp (RE_String "new_sym_var")
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
                    ; Libparser.Syntax.Expr length
                    ; _ ] ->
                      (Libparser.Syntax.Instr (NewSymVar (lval, length)), [])
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
