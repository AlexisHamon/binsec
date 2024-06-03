(**************************************************************************)
(*  This file is part of BINSEC.                                          *)
(*                                                                        *)
(*  Copyright (C) 2016-2024                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

open Types

module Raw (State : RAW_STATE) = struct
  let uop e (o : Dba.Unary_op.t) : Term.unary Term.operator =
    match o with
    | Not -> Not
    | UMinus -> Minus
    | Sext n -> Sext (n - Dba.Expr.size_of e)
    | Uext n -> Uext (n - Dba.Expr.size_of e)
    | Restrict interval -> Restrict interval

  let bop (op : Dba.Binary_op.t) : Term.binary Term.operator =
    match op with
    | Plus -> Plus
    | Minus -> Minus
    | Mult -> Mul
    | DivU -> Udiv
    | DivS -> Sdiv
    | ModU -> Umod
    | ModS -> Smod
    | Eq -> Eq
    | Diff -> Diff
    | LeqU -> Ule
    | LtU -> Ult
    | GeqU -> Uge
    | GtU -> Ugt
    | LeqS -> Sle
    | LtS -> Slt
    | GeqS -> Sge
    | GtS -> Sgt
    | Xor -> Xor
    | And -> And
    | Or -> Or
    | Concat -> Concat
    | LShift -> Lsl
    | RShiftU -> Lsr
    | RShiftS -> Asr
    | LeftRotate -> Rol
    | RightRotate -> Ror
end

module Make (Path : Path.S) (State : STATE) = struct
  include Raw (State)

  let rec eval (e : Types.Expr.t) state =
    match e with
    | Cst bv | Var { info = Symbol (_, (lazy bv)); _ } ->
        (State.Value.constant bv, state)
    | Var var -> 
        (State.lookup var state, state)
    | Load (len, dir, addr, None) ->
        let addrv, state = eval addr state in
        (State.read ~addr:addrv len dir state)
    | Load (len, dir, addr, Some name) ->
        let addrv, state = eval addr state in
        (State.select name ~addr:addrv len dir state)
    | Unary (f, x) -> 
        let xv, state = eval x state in
        (State.Value.unary (uop x f) xv, state)
    | Binary (f, x, y) ->
      let xv, state = eval x state in
      let yv, state = eval y state in
        (State.Value.binary (bop f) xv yv, state)
    | Ite (c, r, e) ->
      let cv, state = eval c state in
      match State.test cv state with
        | exception Unknown | Both _ ->
            let rv, state = eval r state in
            let ev, state = eval e state in
            (State.Value.ite cv rv ev, state)
        | True state ->
          (eval r state)
        | False state ->
          (eval e state)
      
  let fresh (var : Dba.Var.t) state path =
    let id = Path.get State.id path in
    Path.set State.id (State.Uid.succ id) path;
    let value = State.Value.var id var.name var.size in
    let symbols = Path.get State.symbols path in
    let stream = try S.Map.find var.name symbols with Not_found -> [] in
    Path.set State.symbols (S.Map.add var.name (value :: stream) symbols) path;
    State.assign var value state

  let rec safe_eval e state path =
    try (eval e state) with
    | Undef var -> safe_eval e (fresh var state path) path
    | Uninterp array -> safe_eval e (State.alloc ~array state) path

  (*TODO also return state*)
  let rec get_value e state path = 
    try
    let ev, state = eval e state in
      State.get_value ev state with
    | Undef var -> get_value e (fresh var state path) path
    | Uninterp array -> get_value e (State.alloc ~array state) path

  let rec assume e state path =
    try
    let ev, state = eval e state in
      State.assume ev state with
    | Undef var -> assume e (fresh var state path) path
    | Uninterp array -> assume e (State.alloc ~array state) path

  let rec test e state path =
    Format.fprintf Format.std_formatter "@[<v 0>AAA %a@]\n" Dba_printer.Ascii.pp_expr e ;
    try
    let ev, state = eval e state in
      State.test ev state with
    | Undef var -> test e (fresh var state path) path
    | Uninterp array -> test e (State.alloc ~array state) path
  
  let rec split_on e ?n ?except state path =
    try
    let ev, state = eval e state in
      State.enumerate ev ?n ?except state with
    | Undef var -> split_on e ?n ?except (fresh var state path) path
    | Uninterp array -> split_on e ?n ?except (State.alloc ~array state) path

  let rec assign name e state path =
    try
    let ev, state = eval e state in
      State.assign name ev state with
    | Undef var -> assign name e (fresh var state path) path
    | Uninterp array -> assign name e (State.alloc ~array state) path

  let rec read ~addr bytes dir state path =
    try
    let addrv, state = eval addr state in
      State.read ~addr:addrv bytes dir state with
    | Undef var -> read ~addr bytes dir (fresh var state path) path
    | Uninterp array -> read ~addr bytes dir (State.alloc ~array state) path

  let rec write ~addr value dir state path =
    try
    let addrv, state = eval addr state in
    let valuv, state = eval value state in
      State.write ~addr:addrv valuv dir state with
    | Undef var -> write ~addr value dir (fresh var state path) path
    | Uninterp array -> write ~addr value dir (State.alloc ~array state) path

  let rec select name ~addr bytes dir state path =
    try
    let addrv, state = eval addr state in
      State.select name ~addr:addrv bytes dir state with
    | Undef var -> select name ~addr bytes dir (fresh var state path) path
    | Uninterp array ->
        select name ~addr bytes dir (State.alloc ~array state) path

  let rec store name ~addr value dir state path =
    try
    let addrv, state = eval addr state in
    let valuv, state = eval value state in
      State.store name ~addr:addrv valuv dir state with
    | Undef var -> store name ~addr value dir (fresh var state path) path
    | Uninterp array ->
        store name ~addr value dir (State.alloc ~array state) path
end
