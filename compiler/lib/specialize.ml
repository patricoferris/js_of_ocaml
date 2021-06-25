(* Js_of_ocaml compiler
 * http://www.ocsigen.org/js_of_ocaml/
 * Copyright (C) 2010 Jérôme Vouillon
 * Laboratoire PPS - CNRS Université Paris Diderot
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, with linking exception;
 * either version 2.1 of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *)
open! Stdlib
open Code
open Flow

let rec function_cardinality info x acc =
  get_approx
    info
    (fun x ->
      match info.info_defs.(Var.idx x) with
      | Expr (Closure (l, _)) -> Some (List.length l)
      | Expr (Prim (Extern "%closure", [ Pc (NativeString prim) ])) -> (
          try Some (Primitive.arity prim) with Not_found -> None)
      | Expr (Apply (f, l, _)) -> (
          if List.mem f ~set:acc
          then None
          else
            match function_cardinality info f (f :: acc) with
            | Some n ->
                let diff = n - List.length l in
                if diff > 0 then Some diff else None
            | None -> None)
      | _ -> None)
    None
    (fun u v ->
      match u, v with
      | Some n, Some m when n = m -> u
      | _ -> None)
    x

let specialize_instr info (acc, free_pc, extra) i =
  match i with
  | Let (x, Apply (f, l, _)) when Config.Flag.optcall () -> (
      let n' = List.length l in
      match function_cardinality info f [] with
      | None -> i :: acc, free_pc, extra
      | Some n when n = n' -> Let (x, Apply (f, l, true)) :: acc, free_pc, extra
      | Some n when n < n' ->
        assert (n >= 4);
        let k', f' = Code.Var.(fresh (), fresh ()) in
        let k = List.nth l 0 in
        let kx = List.nth l 1 in
        let kf = List.nth l 2 in
        let args, rest = List.take n l in
        let args, rest = k' :: (List.tl args), k :: kx :: kf :: rest in

        let block =
          let g = Code.Var.fresh () in
          let ret = Code.Var.fresh () in
          { params = [g];
            body = [Let (ret, Apply (g, rest, false))];
            branch = Return ret;
            handler = None;
          } in
        (Let (k', Closure ([f'], (free_pc, [f']))))
        ::(Let (x, Apply (f, args, true)))
        ::acc, (free_pc + 1), (free_pc, block) :: extra
      | Some n when n > n' ->
        assert (n >= 4);
        let f' = Code.Var.fresh () in
        let k = List.nth l 0 in
        let _, l_rest = List.take 3 l in
        let missing = Array.init (n - n' + 3) ~f:(fun _ -> Code.Var.fresh ()) in
        let missing = Array.to_list missing in
        let block =
          let params' = Array.init (n - n' + 3) ~f:(fun _ -> Code.Var.fresh ()) in
          let params' = Array.to_list params' in
          let return' = Code.Var.fresh () in
          let params_k, params_rest = List.take 3 params' in
          let args = params_k @ l_rest @ params_rest in
          { params = params';
            body = [Let(return',Apply(f,args,true))];
            branch = Return return';
            handler = None;
          } in
        (Let(f', Closure(missing,(free_pc,missing))))
        ::(Let(x, Apply(k, [f'], true)))
        ::acc,(free_pc + 1),(free_pc,block)::extra
      | _ -> i :: acc, free_pc, extra)
  | _ -> i :: acc, free_pc, extra

let specialize_instrs info p =
  let blocks, free_pc =
    Addr.Map.fold
      (fun pc block (blocks, free_pc) ->
        let body, free_pc, extra =
          List.fold_right block.body ~init:([], free_pc, []) ~f:(fun i acc ->
              specialize_instr info acc i)
        in
        let blocks =
          List.fold_left extra ~init:blocks ~f:(fun blocks (pc, b) ->
              Addr.Map.add pc b blocks)
        in
        Addr.Map.add pc { block with Code.body } blocks, free_pc)
      p.blocks
      (Addr.Map.empty, p.free_pc)
  in
  { p with blocks; free_pc }

let f info p = specialize_instrs info p
