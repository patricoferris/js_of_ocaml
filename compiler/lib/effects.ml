open Code

let debug = Debug.find "eff"

type graph =
  { root : Addr.t
  ; succs : Addr.Set.t Addr.Map.t
  ; backs : Addr.Set.t Addr.Map.t
  ; preds : Addr.Set.t Addr.Map.t
  ; loops : Addr.Set.t
  ; handler_succ : Addr.t Addr.Map.t
  }

let get_values k map = try Addr.Map.find k map with Not_found -> Addr.Set.empty

let add_value k v map =
  let vs = get_values k map in
  Addr.Map.add k (Addr.Set.add v vs) map

let build_graph (blocks : block Addr.Map.t) (pc : Addr.t) : graph =
  let rec loop (g : graph) (pc : Addr.t) (visited : Addr.Set.t) (anc : Addr.Set.t) =
    if not (Addr.Set.mem pc visited)
    then
      let visited = Addr.Set.add pc visited in
      let anc = Addr.Set.add pc anc in
      let s = Code.fold_children blocks pc Addr.Set.add Addr.Set.empty in
      let backs = Addr.Set.inter s anc in

      let succs = Addr.Set.filter (fun pc -> not (Addr.Set.mem pc anc)) s in
      let preds =
        Addr.Set.fold (fun succ preds -> add_value succ pc preds) succs g.preds
        |> Addr.Set.fold (fun back preds -> add_value back pc preds) backs
      in
      let loops = Addr.Set.fold Addr.Set.add backs g.loops in
      let handler_succ =
        match (Addr.Map.find pc blocks).handler with
        | None -> g.handler_succ
        | Some (_, (handler_addr, _)) -> Addr.Map.add pc handler_addr g.handler_succ
      in

      let g =
        { g with
          backs = Addr.Map.add pc backs g.backs
        ; succs = Addr.Map.add pc succs g.succs
        ; preds
        ; loops
        ; handler_succ
        }
      in
      Addr.Set.fold (fun pc' (g, visited) -> loop g pc' visited anc) succs (g, visited)
    else g, visited
  in

  let g, _ =
    loop
      { root = pc
      ; succs = Addr.Map.empty
      ; backs = Addr.Map.empty
      ; preds = Addr.Map.empty
      ; loops = Addr.Set.empty
      ; handler_succ = Addr.Map.empty
      }
      pc
      Addr.Set.empty
      Addr.Set.empty
  in
  g

let print_graph blocks (g : graph) =
  if (not @@ debug ())
  then ()
  else begin
    let is_handler_succ v v' =
      match (Addr.Map.find v blocks).handler with
      | None -> false
      | Some (_, (pc, _)) -> pc = v'
    in

    Printf.eprintf "digraph G {\n";
    Addr.Map.iter
      (fun k s ->
        Addr.Set.iter
          (fun v ->
            if is_handler_succ k v
            then Printf.eprintf "%d -> %d [style=dashed,color=green];\n" k v
            else Printf.eprintf "%d -> %d;\n" k v)
          s)
      g.succs;

    Addr.Map.iter
      (fun k s ->
        Addr.Set.iter
          (fun v -> Printf.eprintf "%d -> %d [style=dashed,color=red];\n" k v)
          s)
      g.backs;

    (* Addr.Map.iter (fun k s -> *)
    (*   Addr.Set.iter (fun v -> *)
    (*     Printf.eprintf "%d -> %d [style=dashed,color=blue];\n" k v *)
    (*   ) s *)
    (* ) g.preds; *)
    Printf.eprintf "}\n"
      end

let dominated_by_node (g : graph) : Addr.Set.t Addr.Map.t =
  let explore_avoiding v =
    let rec loop node visited =
      let visited = Addr.Set.add node visited in
      try
        let succs = Addr.Set.diff (Addr.Map.find node g.succs) visited in
        Addr.Set.fold loop succs visited
      with Not_found -> visited
    in
    loop g.root (Addr.Set.singleton v)
  in

  let all_nodes =
    Addr.Map.fold (fun v _ s -> Addr.Set.add v s) g.preds (Addr.Set.singleton g.root)
  in

  Addr.Set.fold
    (fun v dominated_by ->
      let not_dominated = explore_avoiding v in
      Addr.Map.fold
        (fun v' _ dominated_by ->
          if not (Addr.Set.mem v' not_dominated)
          then add_value v v' dominated_by
          else dominated_by)
        g.preds
        dominated_by)
    all_nodes
    (Addr.Map.singleton g.root all_nodes)

let dominance_frontier (g : graph) dominated_by node0 =
  let dom_by_node0 =
    try Addr.Map.find node0 dominated_by with Not_found -> Addr.Set.empty
  in
  let rec loop node frontier =
    try
      let succs =
        Addr.Map.find node g.succs
        |> fun succs ->
        try Addr.Set.remove (Addr.Map.find node g.handler_succ) succs
        with Not_found -> succs
      in
      Addr.Set.fold
        (fun node' frontier ->
          if Addr.Set.mem node' dom_by_node0
          then loop node' frontier
          else Addr.Set.add node' frontier)
        succs
        frontier
    with Not_found -> frontier
  in
  loop node0 Addr.Set.empty

type trywith_exit_nodes =
  { entry_of_exit : Addr.Set.t Addr.Map.t
  ; exit_of_entry : Addr.t option Addr.Map.t
  }

let empty_exit_nodes = { entry_of_exit = Addr.Map.empty; exit_of_entry = Addr.Map.empty }

let trywith_exit_nodes (blocks : block Addr.Map.t) (g : graph) dominated_by :
    trywith_exit_nodes =
  let rec loop node (entry_of_exit, exit_of_entry, visited) =
    let add_entry exit entry entry_of_exit =
      let entries =
        try Addr.Map.find exit entry_of_exit with Not_found -> Addr.Set.empty
      in
      Addr.Map.add exit (Addr.Set.add entry entries) entry_of_exit
    in
    let visited = Addr.Set.add node visited in
    try
      let succs = Addr.Set.diff (Addr.Map.find node g.succs) visited in
      match (Addr.Map.find node blocks).branch with
      | Pushtrap ((_, _), _, (pc2, _), _) ->
          (if not @@ debug ()
          then ()
          else Printf.eprintf "%d ==> dominance frontier of %d\n" node pc2);
          let frontier = dominance_frontier g dominated_by pc2 in
          (if not @@ debug ()
          then ()
          else (
            Printf.eprintf "frontier:";
            Addr.Set.iter (fun node -> Printf.eprintf " %d" node) frontier;
            Printf.eprintf "\n");
          assert (Addr.Set.cardinal frontier <= 1));
          let entry_of_exit, exit_of_entry =
            if Addr.Set.is_empty frontier
            then entry_of_exit, Addr.Map.add node None exit_of_entry
            else
              let exit = Addr.Set.choose frontier in
              ( add_entry exit node entry_of_exit
              , Addr.Map.add node (Some exit) exit_of_entry )
          in
          Addr.Set.fold loop succs (entry_of_exit, exit_of_entry, visited)
      | _ -> Addr.Set.fold loop succs (entry_of_exit, exit_of_entry, visited)
    with Not_found -> entry_of_exit, exit_of_entry, visited
  in

  let entry_of_exit, exit_of_entry, _ =
    loop g.root (Addr.Map.empty, Addr.Map.empty, Addr.Set.empty)
  in
  { entry_of_exit; exit_of_entry }

let merge_exit_nodes en1 en2 =
  let m _ a b =
    match a, b with
    | Some x, None | None, Some x -> Some x
    | _ -> assert false
  in
  { entry_of_exit = Addr.Map.merge m en1.entry_of_exit en2.entry_of_exit
  ; exit_of_entry = Addr.Map.merge m en1.exit_of_entry en2.exit_of_entry
  }

let delimited_by blocks g exit_nodes : Addr.Set.t Addr.Map.t =
  let rec loop
      (pc : Addr.t)
      (visited : Addr.Set.t)
      (delimited_by_acc : Addr.Set.t)
      (delimited_by : Addr.Set.t Addr.Map.t) =
    if not (Addr.Set.mem pc visited)
    then
      let visited = Addr.Set.add pc visited in
      let delimited_by_acc = Addr.Set.remove pc delimited_by_acc in
      let delimited_by = Addr.Map.add pc delimited_by_acc delimited_by in

      let block = Addr.Map.find pc blocks in
      let delimited_by_acc =
        match block.branch with
        | Pushtrap _ -> (
            match Addr.Map.find pc exit_nodes.exit_of_entry with
            | None -> delimited_by_acc
            | Some exit_node -> Addr.Set.add exit_node delimited_by_acc)
        | _ -> delimited_by_acc
      in
      Addr.Set.fold
        (fun pc' (visited, delimited_by) ->
          loop pc' visited delimited_by_acc delimited_by)
        (Addr.Map.find pc g.succs)
        (visited, delimited_by)
    else visited, delimited_by
  in
  let _, d = loop g.root Addr.Set.empty Addr.Set.empty Addr.Map.empty in
  d

let merge_delimited_by d1 d2 =
  let m _ a b =
    match a, b with
    | Some x, None | None, Some x -> Some x
    | _ -> assert false
  in
  Addr.Map.merge m d1 d2

let defs_of_exit_scope blocks g exit_nodes : (Flow.def array * Var.t Var.Map.t) Addr.Map.t
    =
  let rec loop
      (pc : Addr.t)
      (visited : Addr.Set.t)
      accs_of_open_scopes
      (defs_of_exit_scopes : (Flow.def array * Var.t Var.Map.t) Addr.Map.t) =
    let accs_of_open_scopes, defs_of_exit_scopes =
      try
        let (_, _, d), entry_defs = Addr.Map.find pc accs_of_open_scopes in
        ( Addr.Map.remove pc accs_of_open_scopes
        , Addr.Map.add pc (d, entry_defs) defs_of_exit_scopes )
      with Not_found -> accs_of_open_scopes, defs_of_exit_scopes
    in

    if not (Addr.Set.mem pc visited)
    then
      let visited = Addr.Set.add pc visited in
      let block = Addr.Map.find pc blocks in

      let accs_of_open_scopes =
        Addr.Map.map
          (fun (acc, d) -> Flow.f_block ~acc blocks block, d)
          accs_of_open_scopes
      in

      let accs_of_open_scopes =
        match block.branch with
        | Pushtrap ((pc1, params1), _, (pc2, params2), _) -> (
            match Addr.Map.find pc exit_nodes.exit_of_entry with
            | None -> accs_of_open_scopes
            | Some exit_node ->
                let block1 = Addr.Map.find pc1 blocks in
                let block2 = Addr.Map.find pc2 blocks in
                let defsl =
                  List.combine block1.params params1 @ List.combine block2.params params2
                in
                let entry_defs =
                  List.fold_left (fun m (k, v) -> Var.Map.add k v m) Var.Map.empty defsl
                in

                (* todo: fixme: ugly *)
                let empty_acc =
                  let nv = Var.count () in
                  ( Var.ISet.empty ()
                  , Array.make nv Var.Set.empty
                  , Array.make nv (Flow.Phi Var.Set.empty) )
                in

                Addr.Map.add exit_node (empty_acc, entry_defs) accs_of_open_scopes)
        | _ -> accs_of_open_scopes
      in

      Addr.Set.fold
        (fun pc' (visited, defs_of_exit_scopes) ->
          loop pc' visited accs_of_open_scopes defs_of_exit_scopes)
        (Addr.Map.find pc g.succs)
        (visited, defs_of_exit_scopes)
    else visited, defs_of_exit_scopes
  in
  let _, d = loop g.root Addr.Set.empty Addr.Map.empty Addr.Map.empty in
  d

let merge_defs_of_exit_scope d1 d2 =
  let m _ a b =
    match a, b with
    | Some x, None | None, Some x -> Some x
    | _ -> assert false
  in
  Addr.Map.merge m d1 d2

let rec in_this_scope scope_defs v =
  let v = Var.idx v in
  match scope_defs.(v) with
  | Flow.Phi s -> Var.Set.exists (in_this_scope scope_defs) s
  | Flow.Expr _ | Flow.FromOtherStack -> true
  | Flow.Param -> assert false

let rec entry_def_of scope_defs entry_defs v =
  try Var.Map.find v entry_defs
  with Not_found -> (
    let id = Var.idx v in
    match scope_defs.(id) with
    | Flow.Phi s ->
        let s' =
          Var.Set.fold
            (fun v' s' -> Var.Set.add (entry_def_of scope_defs entry_defs v') s')
            s
            Var.Set.empty
        in
        assert (Var.Set.cardinal s' = 1);
        Var.Set.choose s'
    | _ -> assert false)

let immediate_dominator_of_node (g : graph) dominated_by : Addr.t Addr.Map.t =
  let dom_by node = get_values node dominated_by in

  let rec loop node (idom : Addr.t Addr.Map.t) =
    let dom = dom_by node |> Addr.Set.remove node in
    let dom_dom =
      Addr.Set.fold
        (fun node' dom_dom ->
          dom_by node' |> Addr.Set.remove node' |> Addr.Set.union dom_dom)
        dom
        Addr.Set.empty
    in
    let idom_node = Addr.Set.diff dom dom_dom in
    let idom =
      Addr.Set.fold (fun node' idom -> Addr.Map.add node' node idom) idom_node idom
    in
    Addr.Set.fold loop idom_node idom
  in
  loop g.root Addr.Map.empty

type jump_closures =
  { closure_of_jump : Var.t Addr.Map.t
  ; closure_of_alloc_site : (Var.t * Addr.t) list Addr.Map.t
  ; allocated_call_blocks : (Var.t, Addr.t) Hashtbl.t
  }

let empty_jump_closures =
  { closure_of_jump = Addr.Map.empty
  ; closure_of_alloc_site = Addr.Map.empty
  ; allocated_call_blocks = Hashtbl.create 3
  }

let jump_closures (g : graph) dominated_by : jump_closures =
  let idom = immediate_dominator_of_node g dominated_by in
  let closure_of_jump, closure_of_alloc_site =
    let non_handler_jumps node preds =
      Addr.Set.cardinal
      @@ Addr.Set.filter
           (fun pred ->
             try Addr.Map.find pred g.handler_succ <> node with Not_found -> true)
           preds
    in

    Addr.Map.fold
      (fun node preds (c_o_j, c_o_a_s) ->
        if non_handler_jumps node preds >= 2
        then
          let cname = Var.fresh () in
          let idom_node = Addr.Map.find node idom in
          let closures_to_allocate =
            try Addr.Map.find idom_node c_o_a_s with Not_found -> []
          in
          let c_o_j = Addr.Map.add node cname c_o_j in
          let c_o_a_s =
            Addr.Map.add idom_node ((cname, node) :: closures_to_allocate) c_o_a_s
          in
          c_o_j, c_o_a_s
        else c_o_j, c_o_a_s)
      g.preds
      (Addr.Map.empty, Addr.Map.empty)
  in

  { closure_of_jump; closure_of_alloc_site; allocated_call_blocks = Hashtbl.create 37 }

let merge_jump_closures jc1 jc2 =
  let m _ a b =
    match a, b with
    | Some x, None | None, Some x -> Some x
    | _ -> assert false
  in
  { closure_of_jump = Addr.Map.merge m jc1.closure_of_jump jc2.closure_of_jump
  ; closure_of_alloc_site =
      Addr.Map.merge m jc1.closure_of_alloc_site jc2.closure_of_alloc_site
  ; allocated_call_blocks = (* TODO *)
                            Hashtbl.create 3
  }

(******************************************************************************)

let cont_closures = ref Var.Set.empty

let is_cont_closure v = Var.Set.mem v !cont_closures

(******************************************************************************)

type st =
  { mutable new_blocks : Code.block Addr.Map.t * Code.Addr.t
  ; blocks : Code.block Addr.Map.t
  ; jc : jump_closures
  ; en : trywith_exit_nodes
  ; delimited_by : Addr.Set.t Addr.Map.t
  ; defs_of_exit_node : (Flow.def array * Var.t Var.Map.t) Addr.Map.t
  ; mutable kx_of_poptrap : Var.t Addr.Map.t
  }

let fresh2 () = Var.fresh (), Var.fresh ()

let fresh3 () = Var.fresh (), Var.fresh (), Var.fresh ()

let fresh4 () = Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh ()

(* let fresh5 () =
   Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh () *)
let fresh6 () =
  Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh (), Var.fresh ()

let add_block st block =
  let blocks, free_pc = st.new_blocks in
  st.new_blocks <- Addr.Map.add free_pc block blocks, free_pc + 1;
  free_pc

let filter_cont_params st cont =
  let block = Addr.Map.find (fst cont) st.blocks in
  let cont_params = snd cont in
  let block_params = block.params in
  let rec loop = function
    | x :: xs, _y :: ys -> x :: loop (xs, ys)
    | _, [] -> []
    | [], _ -> assert false
  in
  fst cont, loop (cont_params, block_params)

let add_call_block st cname params =
  let fresh_params = List.map (fun _ -> Var.fresh ()) params in
  let ret = Var.fresh () in
  let addr =
    add_block
      st
      { params = fresh_params
      ; handler = None
      ; body = [ Let (ret, Apply (cname, params, false)) ]
      ; branch = Return ret
      }
  in
  Hashtbl.add st.jc.allocated_call_blocks cname addr;
  addr

let cps_branch st pc k kx kf cont =
  let cont = filter_cont_params st cont in
  let caddr = fst cont in
  let params = k :: kx :: kf :: snd cont in
  try
    let delim_by = Addr.Map.find pc st.delimited_by in
    if not (Addr.Set.mem caddr delim_by) then raise Not_found;
    (if not @@ debug ()
    then ()
    else Printf.eprintf "Translated a jump frow %d to %d into a return\n" pc caddr);
    let scope_defs, _ = Addr.Map.find caddr st.defs_of_exit_node in
    let l = List.filter (in_this_scope scope_defs) (snd cont) in
    assert (List.length l = 1);
    let interesting_param = List.hd l in
    [], Return interesting_param
  with Not_found -> (
    try
      let cname = Addr.Map.find caddr st.jc.closure_of_jump in
      (if not @@ debug ()
      then ()
      else (
        Printf.eprintf "cps_branch: %d ~> call v%d params:" caddr (Var.idx cname);
        List.iter (fun v -> Printf.eprintf " v%d" (Var.idx v)) params;
        Printf.eprintf "\n\n"));
      let ret = Var.fresh () in
      [ Let (ret, Apply (cname, params, false)) ], Return ret
    with Not_found -> [], Branch (caddr, params))

let closure_of_cont st pc params k kx kf cont =
  let name = Var.fresh () in
  cont_closures := Var.Set.add name !cont_closures;
  let fresh_params = List.map (fun v -> v, Var.fresh ()) params in
  let fresh_of v = try List.assoc v fresh_params with Not_found -> v in

  let body, branch = cps_branch st pc k kx kf (fst cont, List.map fresh_of (snd cont)) in

  let addr =
    add_block st { params = List.map fresh_of params; handler = None; body; branch }
  in
  name, Closure (params, (addr, params))

let identity () =
  let x = Var.fresh () in
  { params = [ x ]; handler = None; body = []; branch = Return x }

let toplevel_k () = identity ()

let toplevel_kx () =
  let x = Var.fresh () in
  { params = [ x ]; handler = None; body = []; branch = Raise (x, `Normal) (* ? *) }

let toplevel_kf () =
  let x, x' = Var.fresh (), Var.fresh () in
  let ret = Var.fresh () in
  { params = [ x; x' ]
  ; handler = None
  ; body = [ Let (ret, Prim (Extern "caml_unhandled_effect", [ Pv x ])) ]
  ; branch = Return ret
  }

let alloc_stack_k hv k kx kf =
  let v, ret = Var.fresh (), Var.fresh () in
  { params = [ v ]
  ; handler = None
  ; body = [ Let (ret, Apply (hv, [ k; kx; kf; v ], true)) ]
  ; branch = Return ret
  }

let alloc_stack_kx hx k kx kf = alloc_stack_k hx k kx kf

let alloc_stack_kf hf k kx kf =
  let v, v', ret = Var.fresh (), Var.fresh (), Var.fresh () in
  { params = [ v; v' ]
  ; handler = None
  ; body = [ Let (ret, Apply (hf, [ k; kx; kf; v; v' ], true)) ]
  ; branch = Return ret
  }

let alloc_stack k kx kf =
  let f, x, ret = Var.fresh (), Var.fresh (), Var.fresh () in
  { params = [ f; x ]
  ; handler = None
  ; body = [ Let (ret, Apply (f, [ k; kx; kf; x ], true)) ]
  ; branch = Return ret
  }

let cps_alloc_stack
    st
    (ret : Var.t)
    (kx : Var.t)
    (kf : Var.t)
    (hv : Var.t)
    (hx : Var.t)
    (hf : Var.t) =
  let id, stack_k, stack_kx, stack_kf = fresh4 () in
  let f = Var.fresh () in
  let v1, v2, v3, v4, v5, v6 = fresh6 () in
  let id_addr = add_block st (identity ()) in
  let stack_k_addr = add_block st (alloc_stack_k hv id kx kf) in
  let stack_kx_addr = add_block st (alloc_stack_kx hx id kx kf) in
  let stack_kf_addr = add_block st (alloc_stack_kf hf id kx kf) in
  let stack_addr = add_block st (alloc_stack stack_k stack_kx stack_kf) in
  [ Let (id, Closure ([ v1 ], (id_addr, [ v1 ])))
  ; Let (stack_k, Closure ([ v2 ], (stack_k_addr, [ v2 ])))
  ; Let (stack_kx, Closure ([ v3 ], (stack_kx_addr, [ v3 ])))
  ; Let (stack_kf, Closure ([ v4; v5 ], (stack_kf_addr, [ v4; v5 ])))
  ; Let (ret, Closure ([ f; v6 ], (stack_addr, [ f; v6 ])))
  ]

let cps_last st (k : Var.t) (kx : Var.t) (kf : Var.t) (block_addr : Addr.t) (last : last)
    : instr list * last =
  let ( @> ) instrs1 (instrs2, last) = instrs1 @ instrs2, last in
  let cps_jump_cont cont =
    let pc, args = filter_cont_params st cont in
    let args = k :: kx :: kf :: args in
    try
      let cname = Addr.Map.find pc st.jc.closure_of_jump in
      let call_block = add_call_block st cname args in
      call_block, args
    with Not_found -> pc, args
  in

  let cps_return x =
    let kret = Var.fresh () in
    [ Let (kret, Apply (k, [ x ], true)) ], Return kret
  in

  let cps_branch' = cps_branch st block_addr k kx kf in
  let closure_of_cont' params = closure_of_cont st block_addr params k kx kf in

  match last with
  | Return x -> cps_return x
  | Raise (x, _) ->
      let kxret = Var.fresh () in
      [ Let (kxret, Apply (kx, [ x ], true)) ], Return kxret
  | Stop ->
      (* ??? *)
      [], Stop
  | Branch cont -> cps_branch' cont
  | Cond (x, cont1, cont2) -> [], Cond (x, cps_jump_cont cont1, cps_jump_cont cont2)
  | Switch (x, c1, c2) ->
      [], Switch (x, Array.map cps_jump_cont c1, Array.map cps_jump_cont c2)
  | Pushtrap (cont1, x, cont2, pcs) -> (
      Addr.Set.iter
        (fun pc -> st.kx_of_poptrap <- Addr.Map.add pc kx st.kx_of_poptrap)
        pcs;

      let id_addr = add_block st (identity ()) in
      let id_k, v = fresh2 () in

      (if not @@ debug ()
      then ()
      else Printf.eprintf "=>>>>> handler addr: %d\n" (fst cont2));
      let handler, handler_closure =
        closure_of_cont st block_addr [ x ] id_k kx kf cont2
      in

      (if not @@ debug () then () else Printf.eprintf "<== %d\n" block_addr);
      match Addr.Map.find block_addr st.en.exit_of_entry with
      | None ->
          [ Let (id_k, Closure ([ v ], (id_addr, [ v ])))
          ; Let (handler, handler_closure)
          ]
          @> cps_branch st block_addr id_k handler kf cont1
      | Some cont_addr ->
          let cont_block = Addr.Map.find cont_addr st.blocks in
          let dummy, dummy_v, body_ret = fresh3 () in
          let body, body_closure =
            closure_of_cont st block_addr [ dummy ] id_k handler kf cont1
          in

          let continue_instrs, last =
            if Addr.Set.mem cont_addr (Addr.Map.find block_addr st.delimited_by)
            then [], Return body_ret
            else (
              (if not @@ debug ()
              then ()
              else Printf.eprintf "<> find defs of exit node: %d\n" cont_addr);
              let scope_defs, entry_defs = Addr.Map.find cont_addr st.defs_of_exit_node in
              let l = List.filter (in_this_scope scope_defs) cont_block.params in
              (if not @@ debug ()
              then ()
              else Printf.eprintf "length: %d\n" (List.length l));
              assert (List.length l = 1);
              let interesting_param = List.hd l in
              let interesting_arg = Var.fresh () in
              let args =
                List.map
                  (fun v ->
                    if v = interesting_param
                    then interesting_arg
                    else entry_def_of scope_defs entry_defs v)
                  cont_block.params
              in

              let call_cont_block =
                { params = [ interesting_arg ]
                ; handler = None
                ; body = []
                ; branch = Branch (cont_addr, k :: kx :: kf :: args)
                }
              in
              let call_cont_addr = add_block st call_cont_block in

              let cont, cont_ret, v' = fresh3 () in
              ( [ Let (cont, Closure ([ v' ], (call_cont_addr, [ v' ])))
                ; Let (cont_ret, Apply (cont, [ body_ret ], true))
                ]
              , Return cont_ret ))
          in

          ( [ Let (id_k, Closure ([ v ], (id_addr, [ v ])))
            ; Let (handler, handler_closure)
            ; Let (body, body_closure)
            ; Let (dummy_v, Constant (Int 0l))
            ; Let (body_ret, Apply (body, [ dummy_v ], true))
            ]
            @ continue_instrs
          , last ))
  | Poptrap (cont, _) ->
      let old_kx = Addr.Map.find (fst cont) st.kx_of_poptrap in
      cps_branch st block_addr k old_kx kf cont
  | Resume (ret, (stack, func, args), cont_opt) -> (
      [ Let (ret, Apply (stack, [ func; args ], true)) ]
      @>
      match cont_opt with
      | None -> cps_return ret
      | Some cont -> cps_branch' cont)
  | Perform (ret, eff, cont) ->
      let cur_stack = Var.fresh () in
      let f, v = fresh2 () in
      let kfret = Var.fresh () in
      let cur_k, cur_k_closure = closure_of_cont' [ ret ] cont in
      let stack = add_block st (alloc_stack cur_k kx kf) in
      ( [ Let (cur_k, cur_k_closure)
        ; Let (cur_stack, Closure ([ f; v ], (stack, [ f; v ])))
        ; Let (kfret, Apply (kf, [ eff; cur_stack ], true))
        ]
      , Return kfret )
  | Reperform (eff, stack) ->
      let kfret = Var.fresh () in
      [ Let (kfret, Apply (kf, [ eff; stack ], true)) ], Return kfret
  | LastApply (ret, (f, args, full), cont_opt) -> (
      match cont_opt with
      | None -> [ Let (ret, Apply (f, k :: kx :: kf :: args, full)) ], Return ret
      | Some cont ->
          let cur_k, cur_k_closure = closure_of_cont' [ ret ] cont in
          let ret' = Var.fresh () in
          ( [ Let (cur_k, cur_k_closure)
            ; Let (ret', Apply (f, cur_k :: kx :: kf :: args, full))
            ]
          , Return ret' ))

let cps_instr st (kx : Var.t) (kf : Var.t) (instr : instr) : instr list =
  match instr with
  | Let (x, Prim (Extern "caml_alloc_stack", [ Pv hv; Pv hx; Pv hf ])) ->
      cps_alloc_stack st x kx kf hv hx hf
  | Let (x, Prim (Extern "caml_bvar_create", [ Pv y ]))
  | Let (x, Prim (Extern "caml_bvar_take", [ Pv y ])) ->
      (* TODO *)
      let id, v = fresh2 () in
      let id_addr = add_block st (identity ()) in
      [ Let (id, Closure ([ v ], (id_addr, [ v ]))); Let (x, Apply (id, [ y ], true)) ]
  | Let (x, Closure (params, (pc, args))) ->
      let k, kx, kf = fresh3 () in
      [ Let (x, Closure (k :: kx :: kf :: params, (pc, k :: kx :: kf :: args))) ]
  | Let (_, Apply _) -> assert false
  | _ -> [ instr ]

let cps_block st block_addr block =
  let k, kx, kf = fresh3 () in

  let alloc_jump_closure =
    try
      let to_allocate = Addr.Map.find block_addr st.jc.closure_of_alloc_site in
      List.map
        (fun (cname, jump_addr) ->
          let jump_block = Addr.Map.find jump_addr st.blocks in
          let k, kx, kf = fresh3 () in
          let fresh_params =
            k :: kx :: kf :: List.map (fun _ -> Var.fresh ()) jump_block.params
          in
          Let (cname, Closure (fresh_params, (jump_addr, fresh_params))))
        to_allocate
    with Not_found -> []
  in

  let last_instrs, last = cps_last st k kx kf block_addr block.branch in

  let body =
    (List.map (cps_instr st kx kf) block.body |> List.flatten)
    @ alloc_jump_closure
    @ last_instrs
  in

  { params = k :: kx :: kf :: block.params; handler = None; body; branch = last }

let cps_blocks st = Addr.Map.mapi (cps_block st) st.blocks

let nop_block block =
  let nop_last = function
    | LastApply (ret, (f, args, full), cont_opt) -> (
        ( [ Let (ret, Apply (f, args, full)) ]
        , match cont_opt with
          | None -> Return ret
          | Some cont -> Branch cont ))
    | last -> [], last
  in
  let add_instr, branch = nop_last block.branch in
  { block with branch; body = block.body @ add_instr }

let nop { start; blocks; free_pc } =
  let g = build_graph blocks start in
  let dom_by = dominated_by_node g in
  print_graph blocks g;

  (if not @@ debug () then () else Printf.eprintf "\nidom:\n");

  let idom = immediate_dominator_of_node g dom_by in
  (if not @@ debug ()
  then ()
  else (
    Addr.Map.iter (fun node dom -> Printf.eprintf "%d -> %d\n" node dom) idom;

    Printf.eprintf "\n"));

  let blocks = Addr.Map.map nop_block blocks in
  { start; blocks; free_pc }

let pr_graph ({ start; blocks; _ } as p) =
  let g = build_graph blocks start in
  print_graph blocks g;
  p

let f ({ start; blocks; free_pc } : Code.program) : Code.program =
  let (jc, en, db, does)
        : jump_closures
          * trywith_exit_nodes
          * Addr.Set.t Addr.Map.t
          * (Flow.def array * Var.t Var.Map.t) Addr.Map.t =
    Code.fold_closures
      { start; blocks; free_pc }
      (fun _ _ (start, _) (jc, en, db, does) ->
        (if not @@ debug () then () else Printf.eprintf ">> Start: %d\n\n" start);
        let cfg = build_graph blocks start in
        let dom_by = dominated_by_node cfg in

        (if not @@ debug ()
        then ()
        else (
          Printf.eprintf "dominated_by: \n";
          Addr.Map.iter
            (fun node dom ->
              Printf.eprintf "%d ->" node;
              Addr.Set.iter (fun node' -> Printf.eprintf " %d" node') dom;
              Printf.eprintf "\n")
            dom_by;
          Printf.eprintf "\n";
          print_graph blocks cfg;
          Printf.eprintf "%!"));

        let closure_jc = jump_closures cfg dom_by in
        let closure_en = trywith_exit_nodes blocks cfg dom_by in
        let closure_db = delimited_by blocks cfg closure_en in
        let closure_does = defs_of_exit_scope blocks cfg closure_en in

        ( merge_jump_closures closure_jc jc
        , merge_exit_nodes closure_en en
        , merge_delimited_by closure_db db
        , merge_defs_of_exit_scope closure_does does ))
      (empty_jump_closures, empty_exit_nodes, Addr.Map.empty, Addr.Map.empty)
  in

  let st =
    { new_blocks = Addr.Map.empty, free_pc
    ; blocks
    ; jc
    ; en
    ; delimited_by = db
    ; defs_of_exit_node = does
    ; kx_of_poptrap = Addr.Map.empty
    }
  in
  let blocks = cps_blocks st in

  (if not @@ debug ()
  then ()
  else (
    Printf.eprintf "Cont closures:";
    Var.Set.iter (fun c -> Printf.eprintf " v%d" (Var.idx c)) !cont_closures;
    Printf.eprintf "\n\n%!"));

  let k, kx, kf = fresh3 () in
  let v1, v2, v3, v4 = fresh4 () in
  let toplevel_k_addr = add_block st (toplevel_k ()) in
  let toplevel_kx_addr = add_block st (toplevel_kx ()) in
  let toplevel_kf_addr = add_block st (toplevel_kf ()) in
  let new_start =
    add_block
      st
      { params = []
      ; handler = None
      ; body =
          [ Let (k, Closure ([ v1 ], (toplevel_k_addr, [ v1 ])))
          ; Let (kx, Closure ([ v2 ], (toplevel_kx_addr, [ v2 ])))
          ; Let (kf, Closure ([ v3; v4 ], (toplevel_kf_addr, [ v3; v4 ])))
          ]
      ; branch = Branch (start, [ k; kx; kf ])
      }
  in
  let new_blocks, free_pc = st.new_blocks in
  let blocks =
    Addr.Map.merge
      (fun _ b b' ->
        match b, b' with
        | None, None -> None
        | Some b, None | None, Some b -> Some b
        | _ -> assert false)
      blocks
      new_blocks
  in
  { start = new_start; blocks; free_pc }
