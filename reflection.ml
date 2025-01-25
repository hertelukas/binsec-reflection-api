open Binsec
open Libsse
open Types
open Ir

include Cli.Make (struct
  let name = "Symbolic Reflection API"

  let shortname = "reflection"
end)

type Ast.Instr.t +=
  | IsSat of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc
  | IsSymbolic of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | Maximize of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | Minimize of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | NewSymVar of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc
  | PrintConstaint of Ast.Expr.t Ast.loc
  | SolverOr of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | SolverAnd of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | SolverGeneric of
      Ast.Loc.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * binary operator
  | SolverIte of
      Ast.Loc.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
  | SolverIte_Var of
      Ast.Loc.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc

type builtin +=
  | IsSatBuiltin of Dba.Var.t * Dba.Expr.t
  | IsSymbolicBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t
  | MaximizeBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t
  | MinimizeBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t
  | NewSymVarBuiltin of Dba.Var.t * Dba.Expr.t
  | PrintConstaintBuiltin of Dba.Expr.t
  | SolverGenericBuiltin of
      Dba.Var.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t * binary operator

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
        | IsSat (lval, cnstr) -> (
          match Script.eval_loc ~size:1 lval env with
          | Var var ->
              [Builtin (IsSatBuiltin (var, Script.eval_expr cnstr env))]
              (* TODO *)
          | _ ->
              [] )
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
        | Maximize (lval, sym_var, length) -> (
          match Script.eval_loc lval env with
          | Var var ->
              [ Builtin
                  (MaximizeBuiltin
                     ( var
                     , Script.eval_expr sym_var env
                     , Script.eval_expr length env ) ) ]
              (* TODO handle other cases *)
          | _ ->
              [] )
        | Minimize (lval, sym_var, length) -> (
          match Script.eval_loc lval env with
          | Var var ->
              [ Builtin
                  (MinimizeBuiltin
                     ( var
                     , Script.eval_expr sym_var env
                     , Script.eval_expr length env ) ) ]
              (* TODO handle other cases *)
          | _ ->
              [] )
        | NewSymVar (lval, length) -> (
          match Script.eval_loc ~size:env.wordsize lval env with
          | Var var ->
              [Builtin (NewSymVarBuiltin (var, Script.eval_expr length env))]
          | Restrict (var, {hi; lo}) ->
              [] (* TODO *)
          | Store (bytes, dir, addr, base) ->
              [] (* TODO *) )
        | PrintConstaint cnstr ->
            [Builtin (PrintConstaintBuiltin (Script.eval_expr cnstr env))]
        | SolverGeneric (lval, sym_var, sym_var2, length, op) -> (
          match Script.eval_loc lval env with
          | Var var ->
              [ Builtin
                  (SolverGenericBuiltin
                     ( var
                     , Script.eval_expr sym_var env
                     , Script.eval_expr sym_var2 env
                     , Script.eval_expr length env
                     , op ) ) ]
          | _ ->
              (* TODO *)
              [] )
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

  let max_min (max : bool) dst_var sym_var length _ path _ state :
      (S.t, status) Result.t =
    let sym_var, state = Eval.safe_eval sym_var state path in
    let length, state = Eval.safe_eval length state path in
    let length = Bitvector.to_uint (S.get_value length state) in
    (* TODO assert length % 8 == 0 *)
    let sym_var, state =
      S.read ~addr:sym_var (length / 8) Machine.LittleEndian state
    in
    Logger.debug "Length is %d" length ;
    let l = Bitvector.zeros length in
    let r = Bitvector.fill length in
    let cmp = if max then Uge else Ule in
    let rec binary_search (l : Bitvector.t) (r : Bitvector.t) state
        (sym_var : S.Value.t) =
      Logger.debug "l: %s, r: %s" (Bitvector.to_hexstring l)
        (Bitvector.to_hexstring r) ;
      if Bitvector.ugt l r then (
        Logger.error "No value found" ;
        state )
      else if Bitvector.equal l r then (
        Logger.debug "Found value: %s" (Bitvector.to_hexstring l) ;
        (* max: found max value, however, can be the one or one lower *)
        (* min: found min value, however, can be the one or one higher *)
        let assumed_bigger = S.Value.binary cmp sym_var (S.Value.constant l) in
        match S.assume assumed_bigger state with
        | Some _ ->
            S.assign dst_var (S.Value.constant l) state
        | None ->
            S.assign dst_var
              ( if max then
                  S.Value.constant (Bitvector.sub l (Bitvector.ones length))
                else S.Value.constant (Bitvector.add_int l 1) )
              state )
      else
        let mid =
          (* Doing it this way avoids overflows, but is just (l + r) / 2 *)
          Bitvector.add (Bitvector.shift_right l 1) (Bitvector.shift_right r 1)
        in
        (* max: assume that sym_var bigger than our current mid exists *)
        (* min: assume that sym_var smaller than our current mid exists *)
        let assumed_bigger =
          S.Value.binary cmp sym_var (S.Value.constant mid)
        in
        match S.assume assumed_bigger state with
        | Some _ ->
            if max then (
              Logger.debug "Mid too small" ;
              (* We found something, so we can go higher *)
              binary_search (Bitvector.add_int mid 1) r state sym_var )
            else (
              Logger.debug "" ;
              (* We found something, so our mid is too high *)
              binary_search l
                (Bitvector.sub mid (Bitvector.ones length))
                state sym_var )
        | None ->
            if max then (
              Logger.debug "Mid too high" ;
              (* We found nothing, so our mid is too high *)
              binary_search l
                (Bitvector.sub mid (Bitvector.ones length))
                state sym_var )
            else binary_search (Bitvector.add_int mid 1) r state sym_var
    in
    let state = binary_search l r state sym_var in
    Ok state

  let new_sym_var (dst_var : Dba.Var.t) length _ path _ state :
      (S.t, status) Result.t =
    let length, state = Eval.safe_eval length state path in
    let length_int = Bitvector.to_uint (S.get_value length state) in
    let length = Size.Bit.create length_int in
    (* 1. create symbolic variable; use src/dba/dba.mli Var temporary with bitsize*)
    let tmp = Var.temp length in
    (* 2 use Eval.fresh with this temp to create a new symbolic value *)
    let state = Eval.fresh tmp state path in
    (* 3. extend it to 64 bit, if lower, if greater warn and truncate *)
    let sym_var = S.lookup tmp state in
    let sym_var =
      if length_int < dst_var.size then
        S.Value.unary (Uext (dst_var.size - length_int)) sym_var (*extend*)
      else if length_int > dst_var.size then (
        Logger.warning
          "Destination variable cannot hold new variable with that size. \
           Trunacting..." ;
        S.Value.unary (Restrict {hi= dst_var.size - 1; lo= 0}) sym_var )
      else sym_var
    in
    (* 4. assign intermediate to dst_var *)
    let state = S.assign dst_var sym_var state in
    Ok state

  let is_sat (dst_var : Dba.Var.t) cnstr _ path _ state : (S.t, status) Result.t
      =
    let cnstr, state = Eval.safe_eval cnstr state path in
    let assume_true =
      (* Not sure if I can compare unequally sized values though *)
      S.Value.binary Eq cnstr (S.Value.constant Bitvector.one)
    in
    match S.assume assume_true state with
    | Some s ->
        (* Value is_satisfiable *)
        Ok
          (S.assign dst_var
             (S.Value.constant (Bitvector.ones dst_var.size))
             state )
    | _ ->
        Ok
          (S.assign dst_var
             (S.Value.constant (Bitvector.zeros dst_var.size))
             state )

  let print_constraint cnstr _ path _ state : (S.t, status) Result.t =
    let cnstr, state = Eval.safe_eval cnstr state path in
    Logger.info "%a" (S.pp_smt (Some [(cnstr, "my_constaint")])) state ;
    Ok state

  let solver_generic (dst_var : Dba.Var.t) sym_var sym_var2 length op _ path _
      state : (S.t, status) Result.t =
    let sym_var, state = Eval.safe_eval sym_var state path in
    let sym_var2, state = Eval.safe_eval sym_var2 state path in
    let length, state = Eval.safe_eval length state path in
    let length = Bitvector.to_uint (S.get_value length state) in
    let sym_var, state =
      S.read ~addr:sym_var (length / 8) Machine.LittleEndian state
    in
    let sym_var2, state =
      S.read ~addr:sym_var2 (length / 8) Machine.LittleEndian state
    in
    let assumption = S.Value.binary op sym_var sym_var2 in
    (* TODO check if this is correct *)
    match S.assume assumption state with
    | Some state ->
        Ok
          (S.assign dst_var
             (S.Value.constant (Bitvector.ones dst_var.size))
             state )
    | None ->
        Ok
          (S.assign dst_var
             (S.Value.constant (Bitvector.zeros dst_var.size))
             state )

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
      | IsSatBuiltin (lval, cnstr) ->
          Some (is_sat lval cnstr)
      | IsSymbolicBuiltin (lval, sym_var, length) ->
          Some (is_symbolic lval sym_var length)
      | MaximizeBuiltin (lval, sym_var, length) ->
          Some (max_min true lval sym_var length)
      | MinimizeBuiltin (lval, sym_var, length) ->
          Some (max_min false lval sym_var length)
      | NewSymVarBuiltin (lval, length) ->
          Some (new_sym_var lval length)
      | PrintConstaintBuiltin cnstr ->
          Some (print_constraint cnstr)
      | SolverGenericBuiltin (lval, sym_var, sym_var2, length, op) ->
          Some (solver_generic lval sym_var sym_var2 length op)
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

      (* Build parser for l:=func(arg1, arg2, arg3) *)
      let loc_expr_expr_expr_parser func_name =
        ( "fallthrough"
        , [ Dyp.Non_ter ("loc", No_priority)
          ; Dyp.Regexp (RE_String ":=")
          ; Dyp.Regexp (RE_String func_name)
          ; Dyp.Regexp (RE_Char '(')
          ; Dyp.Non_ter ("expr", No_priority)
          ; Dyp.Regexp (RE_Char ',')
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

      (* Applies instr to l = (arg1, arg2, arg3) *)
      let loc_expr_expr_expr_instr instr = function
        | [ Libparser.Syntax.Loc lval
          ; _
          ; _
          ; _
          ; Libparser.Syntax.Expr arg1
          ; _
          ; Libparser.Syntax.Expr arg2
          ; _
          ; Libparser.Syntax.Expr arg3
          ; _ ] ->
            (Libparser.Syntax.Instr (instr (lval, arg1, arg2, arg3)), [])
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
            cha')')

         type Ast.Instr.t += ...Will call script function IsSymbolic of Lvalue.t.loc * Expr.t loc <- loc is to identify which line caused the error

         type builtin += IsSymbolic of Dba.Lvalue * Dba.Expr.t
      *)
      let grammar_extension =
        [ Dyp.Add_rules
            [ (* Core Reflection Primitives *)
              ( loc_expr_expr_parser "maximize"
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
                      assert false )
            ; ( ( "fallthrough"
                , [ Dyp.Non_ter ("loc", No_priority)
                  ; Dyp.Regexp (RE_String ":=")
                  ; Dyp.Regexp (RE_String "is_sat")
                  ; Dyp.Regexp (RE_Char '(')
                  ; Dyp.Non_ter ("expr", No_priority)
                  ; Dyp.Regexp (RE_Char ')') ]
                , "default_priority"
                , [] )
              , fun _ -> function
                  | [ Libparser.Syntax.Loc lval
                    ; __
                    ; _
                    ; Libparser.Syntax.Expr cnstr
                    ; _ ] ->
                      (Libparser.Syntax.Instr (IsSat (lval, cnstr)), [])
                  | _ ->
                      assert false )
            ; ( ( "fallthrough"
                , [ Dyp.Regexp (RE_String "print_constraint")
                  ; Dyp.Regexp (RE_Char '(')
                  ; Dyp.Non_ter ("expr", No_priority)
                  ; Dyp.Regexp (RE_Char ')') ]
                , "default_priority"
                , [] )
              , fun _ -> function
                  | [_; Libparser.Syntax.Expr cnstr; _] ->
                      (Libparser.Syntax.Instr (PrintConstaint cnstr), [])
                  | _ ->
                      assert false )
              (* Constraint primitives *)
            ; ( ( "fallthrough"
                , [ Dyp.Non_ter ("loc", No_priority)
                  ; Dyp.Regexp (RE_String ":=")
                  ; Dyp.Regexp (RE_String "_solver_NOT")
                  ; Dyp.Regexp (RE_Char '(')
                  ; Dyp.Non_ter ("expr", No_priority)
                  ; Dyp.Regexp (RE_Char ')') ]
                , "default_priority"
                , [] )
              , fun _ -> function
                  | [ Libparser.Syntax.Loc lval
                    ; __
                    ; _
                    ; Libparser.Syntax.Expr cnstr
                    ; _ ] ->
                      (Libparser.Syntax.Instr (IsSat (lval, cnstr)), [])
                  | _ ->
                      assert false )
            ; ( loc_expr_expr_parser "_solver_OR"
              , fun _ ->
                  loc_expr_expr_instr (fun (lval, cnstr1, cnstr2) ->
                      SolverOr (lval, cnstr1, cnstr2) ) )
            ; ( loc_expr_expr_parser "_solver_AND"
              , fun _ ->
                  loc_expr_expr_instr (fun (lval, cnstr1, cnstr2) ->
                      SolverAnd (lval, cnstr1, cnstr2) ) )
            ; ( loc_expr_expr_expr_parser "_solver_EQ"
              , fun _ ->
                  loc_expr_expr_expr_instr
                    (fun (lval, sym_var, sym_var2, length) ->
                      SolverGeneric (lval, sym_var, sym_var2, length, Eq) ) )
              (* TODO, this currently just does equals *)
            ; ( loc_expr_expr_expr_parser "_solver_NEQ"
              , fun _ ->
                  loc_expr_expr_expr_instr
                    (fun (lval, sym_var, sym_var2, length) ->
                      SolverGeneric (lval, sym_var, sym_var2, length, Eq) ) )
            ; ( loc_expr_expr_expr_parser "_solver_LT"
              , fun _ ->
                  loc_expr_expr_expr_instr
                    (fun (lval, sym_var, sym_var2, length) ->
                      SolverGeneric (lval, sym_var, sym_var2, length, Ult) ) )
            ; ( loc_expr_expr_expr_parser "_solver_LE"
              , fun _ ->
                  loc_expr_expr_expr_instr
                    (fun (lval, sym_var, sym_var2, length) ->
                      SolverGeneric (lval, sym_var, sym_var2, length, Ule) ) )
            ; ( loc_expr_expr_expr_parser "_solver_SLT"
              , fun _ ->
                  loc_expr_expr_expr_instr
                    (fun (lval, sym_var, sym_var2, length) ->
                      SolverGeneric (lval, sym_var, sym_var2, length, Slt) ) )
            ; ( loc_expr_expr_expr_parser "_solver_SLE"
              , fun _ ->
                  loc_expr_expr_expr_instr
                    (fun (lval, sym_var, sym_var2, length) ->
                      SolverGeneric (lval, sym_var, sym_var2, length, Sle) ) )
            ; ( loc_expr_expr_expr_parser "_solver_ITE"
              , fun _ ->
                  loc_expr_expr_expr_instr (fun (lval, cond, cnstr1, cnstr2) ->
                      SolverIte (lval, cond, cnstr1, cnstr2) ) )
            ; ( ( "fallthrough"
                , [ Dyp.Non_ter ("loc", No_priority)
                  ; Dyp.Regexp (RE_String ":=")
                  ; Dyp.Regexp (RE_String "_solver_ITE_VAR")
                  ; Dyp.Regexp (RE_Char '(')
                  ; Dyp.Non_ter ("expr", No_priority)
                  ; Dyp.Regexp (RE_Char ',')
                  ; Dyp.Non_ter ("expr", No_priority)
                  ; Dyp.Regexp (RE_Char ',')
                  ; Dyp.Non_ter ("expr", No_priority)
                  ; Dyp.Regexp (RE_Char ',')
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
                    ; Libparser.Syntax.Expr cond
                    ; _
                    ; Libparser.Syntax.Expr sym_var
                    ; _
                    ; Libparser.Syntax.Expr sym_var2
                    ; _
                    ; Libparser.Syntax.Expr length1
                    ; _
                    ; Libparser.Syntax.Expr length2
                    ; _ ] ->
                      ( Libparser.Syntax.Instr
                          (SolverIte_Var
                             (lval, cond, sym_var, sym_var2, length1, length2)
                          )
                      , [] )
                  | _ ->
                      assert false ) ] ]

      let instruction_printer = None

      let declaration_printer = None

      let extension : type a b.
             (module EXPLORATION_STATISTICS)
          -> (module Path.S with type t = a)
          -> (module STATE with type t = b)
          -> (module Exec.EXTENSION with type path = a and type state = b)
             option =
       fun _stats path state ->
        if is_enabled () then Some (module Reflection ((val path)) ((val state)))
        else None
    end : Exec.PLUGIN )
