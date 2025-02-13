open Binsec
open Libsse
open Types
open Ir

include Cli.Make (struct
  let name = "Symbolic Reflection API"

  let shortname = "reflection"
end)

type Ast.Instr.t +=
  | Eval of
      Ast.Loc.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
  | IsSat of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc
  | IsSymbolic of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | Maximize of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | MemAlloc of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc
  | MemBytes of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc
  | MemFree of Ast.Expr.t Ast.loc
  | Minimize of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | NewSymVar of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc
  | NewSymVarNamed of
      Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | PrintByte of Ast.Expr.t Ast.loc
  | PrintConstaint of Ast.Expr.t Ast.loc
  | PrintError of Ast.Expr.t Ast.loc
  | SolverAnd of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | SolverConcat of
      Ast.Loc.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
  | SolverExtract of
      Ast.Loc.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
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
  | SolverIteVar of
      Ast.Loc.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
  | SolverOr of Ast.Loc.t Ast.loc * Ast.Expr.t Ast.loc * Ast.Expr.t Ast.loc
  | SolverSignExt of
      Ast.Loc.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
  | SolverZeroExt of
      Ast.Loc.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
      * Ast.Expr.t Ast.loc
  | StateConstraints of Ast.Loc.t Ast.loc

type builtin +=
  | EvalBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t
  | ErrorBuiltin of Dba.Expr.t
  | IsSatBuiltin of Dba.Var.t * Dba.Expr.t
  | IsSymbolicBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t
  | MaximizeBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t
  | MemAllocBuiltin of Dba.Var.t * Dba.Expr.t
  | MemBytesBuiltin of Dba.Var.t * Dba.Expr.t
  | MemFreeBuiltin of Dba.Expr.t
  | MinimizeBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t
  | NewSymVarBuiltin of Dba.Var.t * Dba.Expr.t
  | NewSymVarNamedBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t
  | PrintByteBuiltin of Dba.Expr.t
  | PrintConstaintBuiltin of Dba.Expr.t
  | SolverAndBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t
  | SolverConcatBuiltin of
      Dba.Var.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t
  | SolverExtractBuiltin of
      Dba.Var.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t
  | SolverGenericBuiltin of
      Dba.Var.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t * binary operator
  | SolverIteBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t
  | SolverIteVarBuiltin of
      Dba.Var.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t
  | SolverOrBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t
  | SolverSignExtBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t
  | SolverZeroExtBuiltin of Dba.Var.t * Dba.Expr.t * Dba.Expr.t * Dba.Expr.t
  | StateConstraintsBuiltin of Dba.Var.t

(* TODO replace with actual map *)
type my_heap = (Bitvector.t * Bitvector.t) list

module Reflection (P : Path.S) (S : STATE) :
  Exec.EXTENSION with type path = P.t and type state = S.t = struct
  type path = P.t

  and state = S.t

  module Eval = Eval.Make (P) (S)

  let key_id = P.register_key []

  let initialization_callback = None

  let declaration_callback = None

  (* translate the Ast.Instr.t to the builtin *)
  (* (Ast.Instr.t -> Script.env -> Ir.fallthrough list) option *)
  let instruction_callback =
    let symbolic = Printf.sprintf "%%symbolic%%%d" in
    Some
      (fun inst env ->
        match inst with
        | PrintError msg ->
            [Builtin (ErrorBuiltin (Script.eval_expr msg env))]
        | Eval (lval, sym_var, length, extra) -> (
          match Script.eval_loc lval env with
          | Var var ->
              [ Builtin
                  (EvalBuiltin
                     ( var
                     , Script.eval_expr sym_var env
                     , Script.eval_expr length env
                     , Script.eval_expr extra env ) ) ]
              (* TODO *)
          | _ ->
              [] )
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
        | MemAlloc (lval, size) -> (
          match Script.eval_loc ~size:env.wordsize lval env with
          | Var var ->
              [Builtin (MemAllocBuiltin (var, Script.eval_expr size env))]
              (* TODO other cases *)
          | _ ->
              [] )
        | MemBytes (lval, ptr) -> (
          match Script.eval_loc lval env with
          | Var var ->
              [Builtin (MemBytesBuiltin (var, Script.eval_expr ptr env))]
              (* TODO other cases *)
          | _ ->
              [] )
        | MemFree size ->
            [Builtin (MemFreeBuiltin (Script.eval_expr size env))]
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
          | _ ->
              [] (* TODO *) )
        | NewSymVarNamed (lval, name, length) -> (
          match Script.eval_loc ~size:env.wordsize lval env with
          | Var var ->
              [ Builtin
                  (NewSymVarNamedBuiltin
                     ( var
                     , Script.eval_expr name env
                     , Script.eval_expr length env ) ) ]
          | _ ->
              [] (* TODO *) )
        | PrintConstaint cnstr ->
            [Builtin (PrintConstaintBuiltin (Script.eval_expr cnstr env))]
        | PrintByte byte ->
            [Builtin (PrintByteBuiltin (Script.eval_expr byte env))]
        | SolverAnd (lval, cnstr1, cnstr2) -> (
          match Script.eval_loc ~size:1 lval env with
          | Var var ->
              [ Builtin
                  (SolverAndBuiltin
                     ( var
                     , Script.eval_expr cnstr1 env
                     , Script.eval_expr cnstr2 env ) ) ]
              (* TODO*)
          | _ ->
              [] )
        | SolverConcat (lval, sym_var, sym_var2, length1, length2) -> (
          match Script.eval_loc ~size:env.wordsize lval env with
          | Var var ->
              [ Builtin
                  (SolverConcatBuiltin
                     ( var
                     , Script.eval_expr sym_var env
                     , Script.eval_expr sym_var2 env
                     , Script.eval_expr length1 env
                     , Script.eval_expr length2 env ) ) ]
          | _ ->
              [] )
        | SolverExtract (lval, sym_var, start, end_var, length) -> (
          match Script.eval_loc ~size:env.wordsize lval env with
          | Var var ->
              [ Builtin
                  (SolverExtractBuiltin
                     ( var
                     , Script.eval_expr sym_var env
                     , Script.eval_expr start env
                     , Script.eval_expr end_var env
                     , Script.eval_expr length env ) ) ]
          | _ ->
              [] )
        | SolverOr (lval, cnstr1, cnstr2) -> (
          match Script.eval_loc ~size:1 lval env with
          | Var var ->
              [ Builtin
                  (SolverOrBuiltin
                     ( var
                     , Script.eval_expr cnstr1 env
                     , Script.eval_expr cnstr2 env ) ) ]
              (* TODO*)
          | _ ->
              [] )
        | SolverGeneric (lval, sym_var, sym_var2, length, op) -> (
          match Script.eval_loc ~size:1 lval env with
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
        | SolverIte (lval, cond, cnstr1, cnstr2) -> (
          match Script.eval_loc ~size:1 lval env with
          | Var var ->
              [ Builtin
                  (SolverIteBuiltin
                     ( var
                     , Script.eval_expr cond env
                     , Script.eval_expr cnstr1 env
                     , Script.eval_expr cnstr2 env ) ) ]
              (* TODO *)
          | _ ->
              [] )
        | SolverIteVar (lval, cond, sym_var, sym_var2, length1, length2) -> (
          match Script.eval_loc ~size:env.wordsize lval env with
          | Var var ->
              [ Builtin
                  (SolverIteVarBuiltin
                     ( var
                     , Script.eval_expr cond env
                     , Script.eval_expr sym_var env
                     , Script.eval_expr sym_var2 env
                     , Script.eval_expr length1 env
                     , Script.eval_expr length2 env ) ) ]
              (* TODO *)
          | _ ->
              [] )
        | SolverSignExt (lval, sym_var, to_extend, length) -> (
          match Script.eval_loc ~size:env.wordsize lval env with
          | Var var ->
              [ Builtin
                  (SolverSignExtBuiltin
                     ( var
                     , Script.eval_expr sym_var env
                     , Script.eval_expr to_extend env
                     , Script.eval_expr length env ) ) ]
          | _ ->
              [] )
        | SolverZeroExt (lval, sym_var, to_extend, length) -> (
          match Script.eval_loc ~size:env.wordsize lval env with
          | Var var ->
              [ Builtin
                  (SolverZeroExtBuiltin
                     ( var
                     , Script.eval_expr sym_var env
                     , Script.eval_expr to_extend env
                     , Script.eval_expr length env ) ) ]
          | _ ->
              [] )
        | StateConstraints lval -> (
          match Script.eval_loc ~size:1 lval env with
          | Var var ->
              [Builtin (StateConstraintsBuiltin var)]
          | _ ->
              (* TODO *)
              [] )
        | _ ->
            [] )

  let process_callback = None

  let get_string (str_addr : S.Value.t) state =
    try
      let buf = Buffer.create 16 in
      let rec iter (addr : Bitvector.t) =
        let byte =
          S.get_a_value
            (fst (S.read ~addr:(S.Value.constant addr) 1 LittleEndian state))
            state
        in
        if Bitvector.is_zeros byte then Buffer.contents buf
        else (
          Buffer.add_char buf (Bitvector.to_char byte) ;
          iter (Bitvector.succ addr) )
      in
      iter (S.get_value str_addr state)
    with Uninterp _ -> ""

  let error msg _ path _ state : (S.t, status) Result.t =
    let msg, state = Eval.safe_eval msg state path in
    let s = get_string msg state in
    Logger.error "%s" s ; Error Halt

  let eval dst_var sym_var length extra _ path _ state : (S.t, status) Result.t
      =
    let extra, state = Eval.safe_eval extra state path in
    match S.assume extra state with
    | Some state_extra ->
        let sym_var, state_extra = Eval.safe_eval sym_var state_extra path in
        let length, state_extra = Eval.safe_eval length state_extra path in
        let length = Bitvector.to_uint (S.get_value length state_extra) in
        (* TODO assert length % 8 == 0 *)
        let sym_var, state_extra =
          S.read ~addr:sym_var (length / 8) Machine.LittleEndian state_extra
        in
        Ok
          (S.assign dst_var
             (S.Value.constant (S.get_a_value sym_var state_extra))
             state )
    | None ->
        Logger.warning "Extra constraint could not be fulfilled in evaluation" ;
        Ok state

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

  let new_sym_var_from_tmp (dst_var : Dba.Var.t) tmp length_int state path :
      (S.t, status) Result.t =
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

  let new_sym_var (dst_var : Dba.Var.t) length _ path _ state :
      (S.t, status) Result.t =
    let length, state = Eval.safe_eval length state path in
    let length_int = Bitvector.to_uint (S.get_value length state) in
    let length = Size.Bit.create length_int in
    (* 1. create symbolic variable; use src/dba/dba.mli Var temporary with bitsize*)
    let tmp = Var.temp length in
    new_sym_var_from_tmp dst_var tmp length_int state path

  let new_sym_var_named (dst_var : Dba.Var.t) name length _ path _ state :
      (S.t, status) Result.t =
    let length, state = Eval.safe_eval length state path in
    let length_int = Bitvector.to_uint (S.get_value length state) in
    let length = Size.Bit.create length_int in
    let name, state = Eval.safe_eval name state path in
    let name = get_string name state in
    (* 1. create symbolic variable; use src/dba/dba.mli Var temporary with bitsize*)
    let tmp = Var.temporary name length in
    new_sym_var_from_tmp dst_var tmp length_int state path

  let is_sat (dst_var : Dba.Var.t) cnstr _ path _ state : (S.t, status) Result.t
      =
    let cnstr, state = Eval.safe_eval cnstr state path in
    let assume_true =
      (* Not sure if I can compare unequally sized values though *)
      S.Value.binary Eq cnstr (S.Value.constant Bitvector.one)
    in
    match S.assume assume_true state with
    | Some _ ->
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

  let print_byte byte _ path _ state : (S.t, status) Result.t =
    let byte, state = Eval.safe_eval byte state path in
    Logger.info "%a" (S.pp_smt (Some [(byte, "my_byte")])) state ;
    Ok state

  let solver_and_or (dst_var : Dba.Var.t) cnstr1 cnstr2 op _ path _ state :
      (S.t, status) Result.t =
    let cnstr1, state = Eval.safe_eval cnstr1 state path in
    let cnstr2, state = Eval.safe_eval cnstr2 state path in
    let assumption = S.Value.binary op cnstr1 cnstr2 in
    Ok (S.assign dst_var assumption state)

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
    Ok (S.assign dst_var assumption state)

  let solver_ite dst_var cond cnstr1 cnstr2 _ path _ state :
      (S.t, status) Result.t =
    let cond, state = Eval.safe_eval cond state path in
    let cnstr1, state = Eval.safe_eval cnstr1 state path in
    let cnstr2, state = Eval.safe_eval cnstr2 state path in
    let assumption = S.Value.ite cond cnstr1 cnstr2 in
    Ok (S.assign dst_var assumption state)

  let extend_with_warning sym_var current_length (dst_var : Dba.Var.t) =
    if current_length < dst_var.size then
      S.Value.unary (Uext (dst_var.size - current_length)) sym_var
    else if current_length > dst_var.size then (
      Logger.warning
        "Destination variable cannot hold new variable with that size. \
         Truncating..." ;
      S.Value.unary (Restrict {hi= dst_var.size - 1; lo= 0}) sym_var )
    else sym_var

  let solver_ite_var dst_var cond sym_var sym_var2 length1 length2 _ path _
      state : (S.t, status) Result.t =
    let cond, state = Eval.safe_eval cond state path in
    let sym_var, state = Eval.safe_eval sym_var state path in
    let sym_var2, state = Eval.safe_eval sym_var2 state path in
    let length1, state = Eval.safe_eval length1 state path in
    let length1 = Bitvector.to_uint (S.get_value length1 state) in
    let length2, state = Eval.safe_eval length2 state path in
    let length2 = Bitvector.to_uint (S.get_value length2 state) in
    (* TODO assert length % 8 == 0 *)
    let sym_var, state =
      S.read ~addr:sym_var (length1 / 8) Machine.LittleEndian state
    in
    let sym_var2, state =
      S.read ~addr:sym_var2 (length2 / 8) Machine.LittleEndian state
    in
    let sym_var = extend_with_warning sym_var length1 dst_var in
    let sym_var2 = extend_with_warning sym_var2 length2 dst_var in
    let assumption = S.Value.ite cond sym_var sym_var2 in
    Ok (S.assign dst_var assumption state)

  let state_constraints (dst_var : Dba.Var.t) _ _ _ state :
      (S.t, status) Result.t =
    let cnstr =
      List.fold_left (S.Value.binary And)
        (S.Value.constant Bitvector.zero)
        (S.assertions state)
    in
    let cnstr = extend_with_warning cnstr 1 dst_var in
    Ok (S.assign dst_var cnstr state)

  let solver_concat dst_var sym_var sym_var2 length1 length2 _ path _ state :
      (S.t, status) Result.t =
    let sym_var, state = Eval.safe_eval sym_var state path in
    let sym_var2, state = Eval.safe_eval sym_var2 state path in
    let length1, state = Eval.safe_eval length1 state path in
    let length1 = Bitvector.to_uint (S.get_value length1 state) in
    let length2, state = Eval.safe_eval length2 state path in
    let length2 = Bitvector.to_uint (S.get_value length2 state) in
    let sym_var, state =
      S.read ~addr:sym_var (length1 / 8) Machine.LittleEndian state
    in
    let sym_var2, state =
      S.read ~addr:sym_var2 (length2 / 8) Machine.LittleEndian state
    in
    let sym_var = S.Value.binary Concat sym_var sym_var2 in
    let sym_var = extend_with_warning sym_var (length1 + length2) dst_var in
    Ok (S.assign dst_var sym_var state)

  let solver_extract dst_var sym_var start end_var length _ path _ state :
      (S.t, status) Result.t =
    let sym_var, state = Eval.safe_eval sym_var state path in
    let length, state = Eval.safe_eval length state path in
    let length = Bitvector.to_uint (S.get_value length state) in
    let sym_var, state =
      S.read ~addr:sym_var (length / 8) Machine.LittleEndian state
    in
    let start, state = Eval.safe_eval start state path in
    let start = Bitvector.to_uint (S.get_value start state) in
    let end_var, state = Eval.safe_eval end_var state path in
    let end_var = Bitvector.to_uint (S.get_value end_var state) in
    (* start 0 means starting from first bit *)
    let hi = length - 1 - start in
    let lo = length - 1 - end_var in
    let sym_var = S.Value.unary (Restrict {hi; lo}) sym_var in
    let sym_var = extend_with_warning sym_var (end_var - start) dst_var in
    Ok (S.assign dst_var sym_var state)

  (* _solver_ZeroExt - Extends symbolic varible <sym_var> with <to_extend> bits *)
  let solver_zero_ext dst_var sym_var to_extend length _ path _ state :
      (S.t, status) Result.t =
    let sym_var, state = Eval.safe_eval sym_var state path in
    let to_extend, state = Eval.safe_eval to_extend state path in
    let to_extend = Bitvector.to_uint (S.get_value to_extend state) in
    let length, state = Eval.safe_eval length state path in
    let length = Bitvector.to_uint (S.get_value length state) in
    let sym_var, state =
      S.read ~addr:sym_var (length / 8) Machine.LittleEndian state
    in
    let sym_var = S.Value.unary (Uext to_extend) sym_var in
    let sym_var = extend_with_warning sym_var (length + to_extend) dst_var in
    Ok (S.assign dst_var sym_var state)

  let solver_sign_ext dst_var sym_var to_extend length _ path _ state :
      (S.t, status) Result.t =
    let sym_var, state = Eval.safe_eval sym_var state path in
    let to_extend, state = Eval.safe_eval to_extend state path in
    let to_extend = Bitvector.to_uint (S.get_value to_extend state) in
    let length, state = Eval.safe_eval length state path in
    let length = Bitvector.to_uint (S.get_value length state) in
    let sym_var, state =
      S.read ~addr:sym_var (length / 8) Machine.LittleEndian state
    in
    let sym_var = S.Value.unary (Sext to_extend) sym_var in
    let sym_var = extend_with_warning sym_var (length + to_extend) dst_var in
    Ok (S.assign dst_var sym_var state)

  (* Use map between constant address and metadata *)
  let mem_alloc dst_var size _ path _ state : (S.t, status) Result.t =
    let heap : my_heap = P.get key_id path in
    let size, state = Eval.safe_eval size state path in
    (* TODO maximize if not concrete*)
    let size = S.get_value size state in
    let start : Bitvector.t =
      match List.rev heap with
      | [] ->
          Bitvector.of_int ~size:64 0x40000
      | (base_ptr, len) :: _ ->
          Bitvector.add base_ptr len
    in
    P.set key_id (heap @ [(start, size)]) path ;
    Ok (S.assign dst_var (S.Value.constant start) state)

  let mem_bytes dst_var ptr _ path _ state : (S.t, status) Result.t =
    let ptr, state = Eval.safe_eval ptr state path in
    let ptr = S.get_value ptr state in
    let heap : my_heap = P.get key_id path in
    let base_ptr, len =
      List.find (fun (list_ptr, _) -> Bitvector.compare list_ptr ptr > 0) heap
    in
    if Bitvector.compare (Bitvector.add base_ptr len) ptr > 0 then
      Logger.error "Getting mem_bytes of freed chunk!" ;
    if Bitvector.compare ptr base_ptr != 0 then
      Logger.warning "mem_bytes called into the middle of a chunk!" ;
    Ok (S.assign dst_var (S.Value.constant len) state)

  let mem_free ptr _ path _ state : (S.t, status) Result.t =
    let ptr, state = Eval.safe_eval ptr state path in
    let ptr = S.get_value ptr state in
    let heap : my_heap = P.get key_id path in
    let base_ptr, len =
      List.find (fun (list_ptr, _) -> Bitvector.compare list_ptr ptr > 0) heap
    in
    if Bitvector.compare (Bitvector.add base_ptr len) ptr > 0 then
      Logger.error "Freeing unallocated chunk!" ;
    if Bitvector.compare ptr base_ptr != 0 then
      Logger.warning "mem_free called into the middle of a chunk!" ;
    P.set key_id
      (List.filter
         (fun (list_ptr, _) -> Bitvector.compare list_ptr ptr != 0)
         heap )
      path ;
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
      | EvalBuiltin (lval, sym_var, length, extra) ->
          Some (eval lval sym_var length extra)
      | ErrorBuiltin msg ->
          Some (error msg)
      | IsSatBuiltin (lval, cnstr) ->
          Some (is_sat lval cnstr)
      | IsSymbolicBuiltin (lval, sym_var, length) ->
          Some (is_symbolic lval sym_var length)
      | MaximizeBuiltin (lval, sym_var, length) ->
          Some (max_min true lval sym_var length)
      | MemAllocBuiltin (lval, size) ->
          Some (mem_alloc lval size)
      | MemBytesBuiltin (lval, ptr) ->
          Some (mem_bytes lval ptr)
      | MemFreeBuiltin ptr ->
          Some (mem_free ptr)
      | MinimizeBuiltin (lval, sym_var, length) ->
          Some (max_min false lval sym_var length)
      | NewSymVarBuiltin (lval, length) ->
          Some (new_sym_var lval length)
      | NewSymVarNamedBuiltin (lval, name, length) ->
          Some (new_sym_var_named lval name length)
      | PrintConstaintBuiltin cnstr ->
          Some (print_constraint cnstr)
      | PrintByteBuiltin byte ->
          Some (print_byte byte)
      | SolverAndBuiltin (lval, cnstr1, cnstr2) ->
          Some (solver_and_or lval cnstr1 cnstr2 And)
      | SolverConcatBuiltin (lval, sym_var, sym_var2, length1, length2) ->
          Some (solver_concat lval sym_var sym_var2 length1 length2)
      | SolverExtractBuiltin (lval, sym_var, start, end_var, length) ->
          Some (solver_extract lval sym_var start end_var length)
      | SolverOrBuiltin (lval, cnstr1, cnstr2) ->
          Some (solver_and_or lval cnstr1 cnstr2 Or)
      | SolverGenericBuiltin (lval, sym_var, sym_var2, length, op) ->
          Some (solver_generic lval sym_var sym_var2 length op)
      | SolverIteBuiltin (lval, cond, cnstr1, cnstr2) ->
          Some (solver_ite lval cond cnstr1 cnstr2)
      | SolverIteVarBuiltin (lval, cond, sym_var, sym_var2, length1, length2) ->
          Some (solver_ite_var lval cond sym_var sym_var2 length1 length2)
      | SolverSignExtBuiltin (lval, sym_var, to_extend, length) ->
          Some (solver_sign_ext lval sym_var to_extend length)
      | SolverZeroExtBuiltin (lval, sym_var, to_extend, length) ->
          Some (solver_zero_ext lval sym_var to_extend length)
      | StateConstraintsBuiltin lval ->
          Some (state_constraints lval)
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
              ( ( "fallthrough"
                , [ Dyp.Regexp (RE_String "error")
                  ; Dyp.Regexp (RE_Char '(')
                  ; Dyp.Non_ter ("expr", No_priority)
                  ; Dyp.Regexp (RE_Char ')') ]
                , "default_priority"
                , [] )
              , fun _ -> function
                  | [_; _; Libparser.Syntax.Expr msg; _] ->
                      (Libparser.Syntax.Instr (PrintError msg), [])
                  | _ ->
                      assert false )
            ; ( ( "fallthrough"
                , [ Dyp.Non_ter ("loc", No_priority)
                  ; Dyp.Regexp (RE_String ":=")
                  ; Dyp.Regexp (RE_String "state_constraints")
                  ; Dyp.Regexp (RE_Char '(')
                  ; Dyp.Regexp (RE_Char ')') ]
                , "default_priority"
                , [] )
              , fun _ -> function
                  | [Libparser.Syntax.Loc lval; _; _; _; _] ->
                      (Libparser.Syntax.Instr (StateConstraints lval), [])
                  | _ ->
                      assert false )
            ; ( loc_expr_expr_parser "maximize"
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
            ; ( loc_expr_expr_parser "new_sym_var_named"
              , fun _ ->
                  loc_expr_expr_instr (fun (lval, name, length) ->
                      NewSymVarNamed (lval, name, length) ) )
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
                    ; _
                    ; _
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
                  | [_; _; Libparser.Syntax.Expr cnstr; _] ->
                      (Libparser.Syntax.Instr (PrintConstaint cnstr), [])
                  | _ ->
                      assert false )
            ; ( ( "fallthrough"
                , [ Dyp.Regexp (RE_String "print_byte")
                  ; Dyp.Regexp (RE_Char '(')
                  ; Dyp.Non_ter ("expr", No_priority)
                  ; Dyp.Regexp (RE_Char ')') ]
                , "default_priority"
                , [] )
              , fun _ -> function
                  | [_; _; Libparser.Syntax.Expr byte; _] ->
                      (Libparser.Syntax.Instr (PrintByte byte), [])
                  | _ ->
                      assert false )
            ; ( loc_expr_expr_expr_parser "eval"
              , fun _ ->
                  loc_expr_expr_expr_instr
                    (fun (lval, sym_var, length, extra) ->
                      Eval (lval, sym_var, length, extra) ) )
              (* Memory primitives *)
            ; ( ( "fallthrough"
                , [ Dyp.Non_ter ("loc", No_priority)
                  ; Dyp.Regexp (RE_String ":=")
                  ; Dyp.Regexp (RE_String "mem_alloc")
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
                    ; Libparser.Syntax.Expr size
                    ; _ ] ->
                      (Libparser.Syntax.Instr (MemAlloc (lval, size)), [])
                  | _ ->
                      assert false )
            ; ( ( "fallthrough"
                , [ Dyp.Non_ter ("loc", No_priority)
                  ; Dyp.Regexp (RE_String ":=")
                  ; Dyp.Regexp (RE_String "mem_bytes")
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
                    ; Libparser.Syntax.Expr ptr
                    ; _ ] ->
                      (Libparser.Syntax.Instr (MemBytes (lval, ptr)), [])
                  | _ ->
                      assert false )
            ; ( ( "fallthrough"
                , [ Dyp.Regexp (RE_String "mem_free")
                  ; Dyp.Regexp (RE_Char '(')
                  ; Dyp.Non_ter ("expr", No_priority)
                  ; Dyp.Regexp (RE_Char ')') ]
                , "default_priority"
                , [] )
              , fun _ -> function
                  | [_; _; Libparser.Syntax.Expr ptr; _] ->
                      (Libparser.Syntax.Instr (MemFree ptr), [])
                  | _ ->
                      assert false )
              (* Symbolic value primitives *)
            ; ( ( "fallthrough"
                , [ Dyp.Non_ter ("loc", No_priority)
                  ; Dyp.Regexp (RE_String ":=")
                  ; Dyp.Regexp (RE_String "_solver_Concat")
                  ; Dyp.Regexp (RE_Char '(')
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
                    ; Libparser.Syntax.Expr sym_var
                    ; _
                    ; Libparser.Syntax.Expr sym_var2
                    ; _
                    ; Libparser.Syntax.Expr length1
                    ; _
                    ; Libparser.Syntax.Expr length2
                    ; _ ] ->
                      ( Libparser.Syntax.Instr
                          (SolverConcat
                             (lval, sym_var, sym_var2, length1, length2) )
                      , [] )
                  | _ ->
                      assert false )
            ; ( ( "fallthrough"
                , [ Dyp.Non_ter ("loc", No_priority)
                  ; Dyp.Regexp (RE_String ":=")
                  ; Dyp.Regexp (RE_String "_solver_Extract")
                  ; Dyp.Regexp (RE_Char '(')
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
                    ; Libparser.Syntax.Expr sym_var
                    ; _
                    ; Libparser.Syntax.Expr start
                    ; _
                    ; Libparser.Syntax.Expr end_val
                    ; _
                    ; Libparser.Syntax.Expr length
                    ; _ ] ->
                      ( Libparser.Syntax.Instr
                          (SolverExtract (lval, sym_var, start, end_val, length))
                      , [] )
                  | _ ->
                      assert false )
            ; ( loc_expr_expr_expr_parser "_solver_ZeroExt"
              , fun _ ->
                  loc_expr_expr_expr_instr
                    (fun (lval, sym_var, to_extend, length) ->
                      SolverZeroExt (lval, sym_var, to_extend, length) ) )
            ; ( loc_expr_expr_expr_parser "_solver_SignExt"
              , fun _ ->
                  loc_expr_expr_expr_instr
                    (fun (lval, sym_var, to_extend, length) ->
                      SolverSignExt (lval, sym_var, to_extend, length) ) )
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
                    ; _
                    ; _
                    ; _
                    ; Libparser.Syntax.Expr cnstr
                    ; _ ] ->
                      (Libparser.Syntax.Instr (IsSat (lval, cnstr)), [])
                  | _ ->
                      assert false )
            ; ( loc_expr_expr_parser "_solver_Or"
              , fun _ ->
                  loc_expr_expr_instr (fun (lval, cnstr1, cnstr2) ->
                      SolverOr (lval, cnstr1, cnstr2) ) )
            ; ( loc_expr_expr_parser "_solver_And"
              , fun _ ->
                  loc_expr_expr_instr (fun (lval, cnstr1, cnstr2) ->
                      SolverAnd (lval, cnstr1, cnstr2) ) )
            ; ( loc_expr_expr_expr_parser "_solver_EQ"
              , fun _ ->
                  loc_expr_expr_expr_instr
                    (fun (lval, sym_var, sym_var2, length) ->
                      SolverGeneric (lval, sym_var, sym_var2, length, Eq) ) )
            ; ( loc_expr_expr_expr_parser "_solver_NEQ"
              , fun _ ->
                  loc_expr_expr_expr_instr
                    (fun (lval, sym_var, sym_var2, length) ->
                      SolverGeneric (lval, sym_var, sym_var2, length, Diff) ) )
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
                          (SolverIteVar
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
