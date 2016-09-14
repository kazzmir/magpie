type callNode = {
   (* functions called by this node *)
   mutable called : string list;
   (* functions that call this node *)
   mutable called_by : string list;

   mutable can_collect : bool;
   mutable defined : bool;
}

val make_call_graph : Cil.file -> (string -> bool) -> (string,callNode) Hashtbl.t
val can_collect : (string,callNode) Hashtbl.t -> string -> string list -> bool
val print_statistics : (string,callNode) Hashtbl.t -> unit
