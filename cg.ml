open Cil
module E = Errormsg

type callNode = {
   (* functions called by this node *)
   mutable called : string list;
   (* functions that call this node *)
   mutable called_by : string list;

   mutable can_collect : bool;

   mutable defined : bool;
}

let makeNode () =
   {called = []; called_by = []; can_collect = false; defined = false}

class cgCompute hash flagger = object(self)
   inherit nopCilVisitor

   val mutable current_function : fundec option = None

   method vfunc (f:fundec) =
      current_function <- Some f;
      let current =
         match current_function with
         | Some f -> f.svar.vname
         | None -> "??"
      in
      let this_node = self#find_node current in
      DoChildren

   method find_node name : callNode =
      try
         Hashtbl.find hash name
      with Not_found ->
         let node = makeNode () in
         Hashtbl.add hash name node;
         node

   method vexpr (e: exp) = 
    (match e with 
      AddrOf (Var fv, NoOffset) when Cil.isFunctionType fv.vtype -> 
         let indirect = self#find_node "<indirect>" in
         (* let func = self#find_node fv.vname in *)
         indirect.called <- fv.vname :: indirect.called;
         DoChildren
    | _ -> DoChildren);

   method vinst inst =
      let current =
         match current_function with
         | Some f -> f.svar.vname
         | None -> "??"
      in
      let this_node = self#find_node current in
      this_node.defined <- true;
      (* E.log "Added node %s\n" current; *)
      match inst with
      | Call(_, Lval(Var func,b), _, _) ->
            (* E.log "%s calls %s\n" current func.vname; *)
            if flagger func.vname then begin
               (* E.log "%s can directly collect\n" func.vname; *)
               this_node.can_collect <- true;
               DoChildren
            end else begin
               let other = self#find_node func.vname in
               this_node.called <- func.vname :: this_node.called;
               other.called_by <- current :: other.called_by;
               DoChildren
            end
      | Call _ ->
            let indirect = self#find_node "<indirect>" in
            (*
            E.log "In %s " current;
            E.log "Call to indirect\n";
            *)
            this_node.called <- "<indirect>" :: this_node.called;
            indirect.called_by <- current :: indirect.called_by;
            DoChildren
      (* Set the 'can_called' field. This test is almost arbitrary *)
            (*
      | Set(_,Const(CInt64(n,_,_)),_) ->
            if n = Int64.of_int 1 then begin
               this_node.can_collect <- true;
               DoChildren
            end else
               DoChildren
               *)
      | _ -> DoChildren

end

let rec can_collect graph name seen =
   (*
   if (List.length seen = 0) then
      E.log "Can collect %s\n" name;
      *)
   if List.mem name seen then
      false
   else begin
      (* E.log "Can collect? %s " name; *)
      let rec called_can_collect children =
         (* E.log "-> %s " (String.concat "," children); *)
         List.fold_left
         (fun can func ->
            (* E.log "Looking up %s\n" func;*) 
            (* E.log "So far %b next %s\n" can func; *)
            can ||
            let node = Hashtbl.find graph func in
            if func = "<indirect>" then
               called_can_collect node.called 
            else
                can_collect graph func (name :: seen))
         false
         children
       in
       (* E.log "Looking up %s\n" name; *)
       let node = Hashtbl.find graph name in
       (* E.log "%s can collect? %b\n" name node.can_collect; *)
       let v = node.can_collect || called_can_collect node.called in
       (* E.log "collect? = %b\n" v; *)
       v
   end
;;

(* prints the total number of functions and number of functions that can
 * collect *)
let print_statistics graph : unit =
   let hash_table_keys =
      let all = ref [] in
      Hashtbl.iter (fun key value ->
         all := key :: ! all)
         graph;
      ! all
   in
   let total = (List.length (List.filter
                               (fun name ->
                                  let node = Hashtbl.find graph name in
                                  node.defined)
                               hash_table_keys))
   and collect = (List.length (List.filter (fun name ->
      can_collect graph name []) hash_table_keys))
   in
   E.log "Call graph statistics\n";
   E.log " Total functions: %d\n" total;
   E.log " Collecting functions: %d\n" collect;
   E.log " Non-Collecting functions: %d\n" (total - collect);
   E.log " Ratio of non-collecting to total: %f\n" ((float_of_int (total -
   collect)) /. (float_of_int total));
   ()
;;

let traverse_graph graph =
   Hashtbl.iter
   (fun a b ->
      E.log "%s calls %s. Can collect = %b\n" a (String.concat "," b.called_by)
      b.can_collect)
   graph
;;

let make_call_graph file flagger =
   let graph = Hashtbl.create 10 in
   let cg = new cgCompute graph flagger in
   visitCilFileSameGlobals (cg :> cilVisitor) file;
   graph
;;
