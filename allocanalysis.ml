(* vi
 * :set textwidth=500
 *)
(* Things to fix
 * 1. handle structure fields in mark/repair functions - Done
 * 2. better support for guessing the type of an allocation site - more or less done
 * 3. find static roots declared in functions - Not needed! Cil moves static
 * variables to the global namespace.
 * 4. store heap allocations created in functions in a gc_variable_stack - Done
 * 5. Make the 'free' function a parameter - Done
 * 6. Deal with whacky expressions in sizeof, like sizeof( *p ) and
 * sizeof( some_struct ) where some_struct is 'typedef struct some_struct
 * some_struct' - Done
 * 7. Initialize counting variable in tarray mark/repair funcs - Done
 * 8. Set pointers on the stack to 0. - Done
 * 9. Autotag sub-unions, f.x.a.b.c = 1; auto( &f ); auto( &f.x ); ... - Done
 * 10. Handle arrays with sizes in struct mark/repair. f.x[0..9] - Done
 * 11. Handle arrays of arrays in walkers - Done
 * 12. Handle arrays of arrays as roots - Done
 * 13. Only create stacks that are needed, so make them lazily. - Done
 * 14. Use a call graph analysis to remove some unneeded gc frames. - Done
 * 15. Copy autotag information when doing a struct copy of a union.
 *
 * Other things:
    * If multiple variables of the same struct type are roots then the same
    * code will be generated to add the fields of the struct as a root. Instead
    * of copying such code, a function for each struct could call GC_add_root for
    * each field of the struct. Something like
    * gc_add_roots_foobar_struct( struct foobar * f ){
    *   GC_add_root( & f->x );
    *   GC_add_root( & f->y.z.p );
    * }
    * - Done via adding struct roots as tagged.
 *)
open Cil
module E = Errormsg

type allocation_function = Malloc | Calloc | Realloc | KMalloc | VMalloc | KCalloc | GetFreePage;;

module Naming =
   struct

      let s_u c =
         match c.cstruct with
         | true -> "struct"
         | false -> "union"
      ;;

      let gc_mark_name comp =
         Printf.sprintf "__gc_mark_%s_%s" (s_u comp) comp.cname
      ;;

      let gc_repair_name comp =
         Printf.sprintf "__gc_repair_%s_%s" (s_u comp) comp.cname
      ;;
      
      let gc_mark_tarray_name comp =
         Printf.sprintf "__gc_mark_tarray_%s_%s" (s_u comp) comp.cname
      ;;

      let gc_repair_tarray_name comp =
         Printf.sprintf "__gc_repair_tarray_%s_%s" (s_u comp) comp.cname
      ;;

      let gc_struct_tag_name comp =
         Printf.sprintf "__gc_%s_%s_tag" (s_u comp) comp.cname
      ;;

      let gc_struct_array_tag_name comp =
         Printf.sprintf "__gc_tarray_%s_%s_tag" (s_u comp) comp.cname
      ;;

      let gc_info (v : varinfo) =
         Printf.sprintf "__gc_autotag_info_%s" v.vname
      ;;

      let gc_prefix = "GC";;

      let get_autotagged_case =
         Printf.sprintf "%s_get_autotagged_case" gc_prefix
      ;;

      let autotag =
         Printf.sprintf "%s_autotag_union" gc_prefix
      ;;

      let gc_mark =
         Printf.sprintf "%s_mark" gc_prefix
      ;;

      let gc_repair =
         Printf.sprintf "%s_repair" gc_prefix
      ;;

      let gc_standard_atomic_tag =
         "__gcstandard_atomic_tag"
      ;;

      let gc_standard_array_tag =
         "__gcstandard_array_tag"
      ;;

      let gc_initialize =
         Printf.sprintf "%s_initialize" gc_prefix
      ;;

      (*
      let gc_variable_stack =
         Printf.sprintf "%s_variable_stack" gc_prefix
      ;;
      *)

      let gc_get_variable_stack =
         Printf.sprintf "%s_get_variable_stack" gc_prefix
      ;;

      let gc_set_variable_stack =
         Printf.sprintf "%s_set_variable_stack" gc_prefix
      ;;

      let add_root_tagged =
         Printf.sprintf "%s_add_root_tagged" gc_prefix
      ;;

      let add_root =
         Printf.sprintf "%s_add_root" gc_prefix
      ;;

      let init_tag =
         Printf.sprintf "%s_init_tag" gc_prefix
      ;;

      let find_end_of_object =
         Printf.sprintf "%s_find_end_of_object" gc_prefix
      ;;

      let copy_autotag comp =
         Printf.sprintf "%s_copy_autotag_%s" gc_prefix comp.cname

      let gc_allocation_name a =
         Printf.sprintf "%s_%s"
         gc_prefix
         (match a with
         | Malloc -> "malloc"
         | Calloc -> "calloc"
         | Realloc -> "realloc"
         | KMalloc -> "kmalloc"
         | VMalloc -> "vmalloc"
         | KCalloc -> "kcalloc"
         | GetFreePage -> "get_free_page")
      ;;

   end;;

module Util = 
   struct
      let memset file =
         Cil.makeVarinfo false "memset" (Formatcil.cType "void * ()(void * a, int s, int b )" [])
         (*
         (findOrCreateFunc file "memset" (Formatcil.cType "void * ()(void * a, int s, int b )" []))
         *)
   end;;

type allocation = Atomic of Cil.typ | Array of allocation * Cil.exp | Struct of compinfo |
StructArray of compinfo * Cil.exp ;;

(* default name of the tuning file *)
let gc_tuning_filename = ref "tuning.h";;
(* default name of the free function *)
let free_func = ref "free";;
(* whether to add GC_initialize to main *)
let add_call_to_initialize = ref true;;
(* whether to add #include <string.h> to the top of the file *)
let do_include_string_h = ref true;;

let debug_mode = ref false;;

(* whether to use the call graph information. should only be used if the entire
 * program is analyzed at once( cil --merge )
 *)
let use_call_graph = ref false;;

(* some utility functions *)
let concat_lists (lst: 'a list) =
   List.fold_left
   (fun a b -> a @ b)
   []
   lst
;;

let rec makeNumList n =
   match n with
   | 0 -> []
   | _ -> n :: (makeNumList (n - 1))
;;

let rec removeDuplicates (lst : 'a list) =
   match lst with
   | x :: xs ->
         if List.mem x xs then
            removeDuplicates xs
         else
            x :: removeDuplicates xs
   | [] -> []
;;

let rec removeDuplicatesEq (lst : 'a list) pred =
   match lst with
   | x :: xs ->
         if List.exists (fun v -> pred v x) xs then
            removeDuplicatesEq xs pred
         else
            x :: removeDuplicatesEq xs pred
   | [] -> []
;;

exception ZeroArray

let rec lastElement (lst : 'a list) =
   match lst with
   | [] -> raise ZeroArray
   | x :: [] -> x
   | x :: xs -> lastElement(xs)
;;

let rec removeLast (lst : 'a list) =
   match lst with
   | [] -> raise ZeroArray
   | x :: [] -> []
   | x :: xs ->
         x :: (removeLast xs)
;;

let rec cilTypeToString () t =
   match t with
   | TPtr(t,_) -> Printf.sprintf "pointer of %a" cilTypeToString t
   | TInt(_,_) -> "int"
   | TComp(_,_) -> "struct/union"
   | TVoid(_) -> "void"
   | _ -> "??"
;;

let rec typeName t =
   match t with
   | Atomic t -> Printf.sprintf "Atomic %a" cilTypeToString t
   | Array(t, size) -> Printf.sprintf "Array of %s" (typeName t)
   | Struct c -> "Struct"
   | StructArray(c, size) -> "Complex array"
;;
(* end utility functions *)

(* let the_allocators = ref ["malloc";"calloc";"realloc";"kmalloc"];; *)
(* let the_allocators = ref ["alloc_c";"alloc_r"] *)

(* these are the allocators we can deal with and their default names *)
let the_allocators =
   let h = Hashtbl.create 0 in
   Hashtbl.add h Malloc ["malloc"];
   Hashtbl.add h Calloc ["calloc"];
   Hashtbl.add h Realloc ["realloc"];
   Hashtbl.add h KMalloc ["kmalloc"];
   Hashtbl.add h VMalloc ["vmalloc"];
   Hashtbl.add h KCalloc ["kcalloc"];
   Hashtbl.add h GetFreePage ["__get_free_page"];
   h
;;
         
(* functions with a name in the set 'sets' have the allocator type 'm' *)
let setAllocators m strs =
   Hashtbl.replace the_allocators m strs
;;

(* true if name is an allocator *)
let isAllocator name =
   Hashtbl.fold (fun keys values found ->
      if found then
         found
      else
         List.mem name values)
   the_allocators
   false
;;

(* get the keys from a hash *)
let hash_table_keys table : allocation_function list =
   let all = ref [] in
   Hashtbl.iter (fun key value ->
      all := key :: ! all)
   table;
   ! all
;;

(* get the internally defined allocator type from a name *)
let allocatorType (name: string) : allocation_function =
   let keys = hash_table_keys the_allocators in
   let rec find (rest: allocation_function list) : allocation_function =
      match rest with
      | [] -> raise (Not_found)
      | x :: xs ->
            let values = Hashtbl.find the_allocators x in
            if List.mem name values then
               x
            else
               find xs
   in
   find keys
;;


let isSetjmp name =
   name = "setjmp" ||
   name = "_setjmp"
;;

(* cil converts 'int * x = malloc(...)' into
 * void * tmp = malloc(...);
 * int * x = tmp;
 * So this structure keeps track of that.
 * get = tmp
 * call = malloc
 * set = x
 *)
(*
type site = { 
   mutable get : varinfo;
   mutable call : varinfo;
   mutable set : lval option;
   mutable args : exp list;
}
*)

let usesBinop a b c =
   false
;;

(* true if t is a pointer *)
let isBasic t =
   match t with
   | TPtr(_,_) -> false
   | _ -> true

(* true if exp has a sizeof expression inside it *)
let rec hasSizeOf exp =
   match exp with
   | CastE(_, e) -> hasSizeOf e
   | SizeOf t -> true
   | SizeOfE t -> true
   | BinOp(_, left, right, t) ->
         (hasSizeOf left) ||
         (hasSizeOf right)
   | _ -> false
;;

(* convert C type to an allocation type *)
let rec typeOfType t =
   match t with
   | TComp(comp,_) -> Struct comp
   | TPtr(x,_) -> Array(typeOfType x, Cil.integer 0)
   | TNamed(info,_) -> typeOfType info.ttype
   | _ -> Atomic t
;;

(* convert expression to an allocation type. this is applied to the stuff inside
 * a malloc, such as malloc( sizeof(int) ).
 *)
let rec typeOf2 exp =
   match exp with
   | CastE(_, e) -> typeOf2 e
   | SizeOf t -> typeOfType t
   | SizeOfE exp -> typeOf2 exp
   | Lval(Var v,_) -> typeOfType v.vtype
   | Lval(Mem exp2,offset) -> begin
      (* E.log "Memory of '%a'\n" Cil.d_exp exp2; *)
      match offset with
      | NoOffset -> begin
            match typeOf2 exp2 with
            | Array(t,_) -> t
            | _ -> typeOf2 exp2
      end
      | Field(field, field_offset) ->
            let rec loop field offset =
               match offset with
               | NoOffset -> typeOfType field.ftype
               | Field(f2, o2) -> loop f2 o2
               | Index(exp, offset) -> begin
                     match typeOf2 exp with
                     | Array(t,_) -> t
                     | _ -> typeOf2 exp
               end
            in
            loop field field_offset
      | Index(exp, offset) -> typeOf2 exp
      (*
      let rec loop off =
      match offset with
      | NoOffset
      raise (Failure "oijadsf")
      *)
      (*
      let rec loop off =
         match off with
         match typeOf2 exp2 with
         | Array(t,_) -> t
         | _ -> let rec loop off =
                  (match off with
                  | NoOffset -> typeOf2 exp2
                  | Field(field,offset) -> loop 
                  *)
   end
   | Const c -> Atomic Cil.intType
   | BinOp(op, left, right, t) ->
         let find = 
            let analyze l r =
               let t_left = typeOf2 l in
               let t_right = typeOf2 r in
               (*
               (E.log "left is %s right is %s" (typeName t_left) (typeName
               t_right));
               *)
               (match (t_left,t_right) with
               | Struct(c), Atomic(_) ->
                     StructArray(c, r)
               | Struct(c), Struct(_) ->
                     StructArray(c, r)
               | Atomic(TPtr(_,_)), Atomic(_) ->
                     Array(t_left, r)
               | Struct(_), StructArray(c,r) ->
                     StructArray(c,r)
               | Atomic(_), StructArray(c,r) ->
                     StructArray(c,r)
               | Atomic(_), Atomic(_) ->
                     Atomic t 
               | _ -> t_left)
            in
               if hasSizeOf left then
                  analyze left right
               else
                  analyze right left
         in
         (match op with
         | Mult -> find
         | Div -> find
         | Shiftrt -> find
         | Shiftlt -> find
         | _ ->
               (match typeOf2 left, typeOf2 right with
               | Struct(c), Atomic(_) ->
                     Struct(c)
               | Atomic(_), Struct(c) ->
                     Struct(c)
               | _ -> find))
   | _ -> Atomic Cil.intType
;;

(* add a function to the global list *)
let add_function f g =
   f.globals <- f.globals @ [g];
   g
;;

(*
let rec insert_before (lst: 'a list) before after =
   match lst with
   | x :: xs ->
         if x == after then begin
            E.log "Inserted before something\n";
            before :: (x :: xs)
         end else
            after :: (insert_before xs before after)
   | [] -> []
;;
*)

(*
let rec find_global globals var =
   match globals with
   | x :: xs ->
         (match x with
         | GFun(v,_) ->
               if v == var then begin
                  x
               end else
                  find_global xs var
         | _ -> find_global xs var)
   | [] -> raise (Failure "Could not find global")
;;
*)

(*
struct * atomic int = tagged struct array
struct* * atomic int = array
atomic* * atomic int = array
atomic int * atomic int = atomic
*)

exception NotStructArray

(* true if t is an array with the base type a struct
 * int x[2] - no!
 * struct foo x[2] - yes!
 * int x[2][2] - no!
 * struct foo x[2][2] - yes!
 * 
 * actually array_of_comp returns the comp if available and is_array_of_comp
 * returns true/false.
 *)
let rec array_of_comp t =
   match (Cil.unrollType t) with
   | TArray(TComp(comp,_),_,_) -> comp
   | TArray(TArray(a,b,c),_,_) -> array_of_comp (TArray(a,b,c))
   | TArray(TNamed(info,a),b,c) -> array_of_comp (TArray(Cil.unrollType
   (TNamed(info,a)),b,c))
   | _ -> raise (NotStructArray)
;;
                     
(* true if t is an array of structs *)
let is_array_of_comp t =
   try
      ignore(array_of_comp t);
      true
   with NotStructArray ->
      false
;;

(* true if t is a pointer or a struct *)
let rec base_type_ptr_or_comp t =
   match (Cil.unrollType t) with
   | TPtr _ -> true
   | TComp _ -> true
   | TArray(t,_,_) -> base_type_ptr_or_comp t
   | _ -> false
;;

(* return the index of a field in a struct *)
let count_fields comp field =
   let rec next fields num =
      match fields with
      | x :: xs ->
            if x == field then
               num
            else
               next xs (num + 1)
               (*
               (match (Cil.unrollType x.ftype) with
               | TComp _ -> (num + 1)
               | TPtr _ -> (num + 1)
               | TInt _ -> num
               | TVoid _ -> num
               | TFloat _ -> num
               | TNamed _ -> raise (Failure "tnamed after unrollType?")
               | TFun _ -> num)
               *)

      | _ -> raise (Failure "field not found!")
   in
   next comp.cfields 0
;;
                        
let address_of_exp_lval exp =
   match exp with
   | Lval(l) -> Cil.mkAddrOf l
   | _ -> raise (Failure "cannot take address of non-lval expression")
;;

let rec base_comp lval =
   match lval with
   | Var(v),_ ->
         let rec get_base vtype =
            match vtype with
            | TComp(c,_) -> c
            | TPtr(t,_) -> get_base (Cil.unrollType t)
            | _ -> raise (Failure "unknown type")
         in
         get_base (Cil.unrollType v.vtype)
   | Mem(exp),_ -> begin
      match exp with
      | Lval(l) -> base_comp l
      | _ -> raise (Failure "unknown expression")
   end
;;

let rec is_union_lval lval mem_count = begin
   match lval with
   | Var(v),_ ->
         let rec is_base_type vtype count =
            if count < 0 then
               false
            else
               match vtype with
               | TComp(c,_) ->
                     begin
                        count = 0 && c.cstruct = false
                     end
               | TPtr(ptype,_) -> is_base_type (Cil.unrollType ptype) (count - 1)
               | _ -> begin
                  false
               end
         in
         is_base_type (Cil.unrollType v.vtype) mem_count
   | Mem(exp),_ -> is_union_exp exp (mem_count + 1)
end and is_union_exp exp mem_count =
   match exp with
   | Lval(lval) -> begin
      (*
      E.log "Checking lval for union %a\n" Cil.d_lval lval;
      *)
      is_union_lval lval mem_count
   end
   | _ -> false
;;

(* returns true if comp has any pointer fields *)
let has_pointer_fields comp =
   let rec search fields =
      match fields with
      | f :: fs -> begin
            let rec find t =
               match (Cil.unrollType t) with
               | TVoid _ -> false
               | TInt _ -> false
               | TFun _ -> false
               | TBuiltin_va_list _ -> false
               | TEnum _ -> false
               | TNamed _ -> raise (Failure "Could not determine pointer fields. tnamed after unrollType?")
               | TFloat _ -> false
               | TPtr _ -> true
               | TArray(t,_,_) -> find t 
               | TComp(c,_) -> search c.cfields
            in
            find f.ftype || search fs
      end
      | [] -> false
   in
   search comp.cfields
;;

(* return true if comp is a union or any fields are unions *)
let rec has_union_fields comp =
   if comp.cstruct = false then
      true
   else
      let rec loop fields =
         match fields with
         | h::t -> begin
            match h.ftype with
            | TComp(c,_) -> has_union_fields c
            | _ -> loop t
         end
         | _ -> false
      in
      loop comp.cfields
;;

(* return true if comp has any unions with pointer fields in it *)
let has_union_pointers comp =
   let rec find fs =
      match fs with
      | x :: xs -> begin
         let rec loop t =
            match t with
            | TComp(sub_comp,_) when sub_comp.cstruct = true ->
                  find sub_comp.cfields
            | TComp(sub_comp,_) when sub_comp.cstruct = false ->
                  true
            | TComp _ -> false
            | TVoid _ -> false
            | TInt _ -> false
            | TFun _ -> false
            | TBuiltin_va_list _ -> false
            | TEnum _ -> false
            | TNamed _ -> raise (Failure "Could not determine union fields. tnamed after unrollType?")
            | TArray(t,_,_) -> loop (Cil.unrollType t)
            | TPtr _ -> false
            | TFloat _ -> false
         in
         loop (Cil.unrollType x.ftype)
      end
      | [] -> false
   in
   find comp.cfields

(* guess the allocation type at an allocation site.
 * convert malloc( sizeof(int) ) -> Atomic and
 * malloc( sizeof( int* ) * 5 ) -> Array
 *)
let guessType call args =
   (*
   List.iter (fun exp -> 
      E.log "Type of %a is %a\n" Cil.d_exp exp Cil.d_type (typeOf exp))
   args;
   *)

   let probably_type = 
      try
         let exp = (List.find hasSizeOf args) in
         let e = typeOf2 exp in
         (* E.log "Type of '%a' is %s\n" Cil.d_exp exp (typeName e); *)
         e
      with Not_found ->
         Atomic Cil.intType
   in
   match allocatorType( call.vname ) with
   | Malloc -> probably_type
   | Calloc ->
         let not_sizeof =
            try
               List.find (fun n -> not (hasSizeOf n)) args
            with Not_found ->
               List.hd args
         in
         (match probably_type with
         | Atomic(TPtr _) -> Array(probably_type, not_sizeof)
         | Atomic _ -> probably_type
         | Struct c -> StructArray(c,not_sizeof)
         | _ -> probably_type)
   | Realloc -> probably_type
   | KMalloc -> probably_type
   | VMalloc -> probably_type
   | KCalloc ->
         let not_sizeof =
            try
               List.find (fun n -> not (hasSizeOf n)) args
            with Not_found ->
               List.hd args
         in
         (match probably_type with
         | Atomic(TPtr _) -> Array(probably_type, not_sizeof)
         | Atomic _ -> probably_type
         | Struct c -> StructArray(c,not_sizeof)
         | _ -> probably_type)
   | GetFreePage -> probably_type
;;

(* holds lazily created GC_?alloc prototypes
 * why lazy? because when a prototype is looked up the C code for the function
 * prototype is added to the top of the file so we only want to add prototypes
 * that are actually used.
 *)
let gc_allocated_prototypes = ref [];;

(* returns a function that returns true if the 'name' argument is an allocator
 *)
let gc_allocator extra_args =
   let generate_list what num =
      let rec all accum i =
         match i with
         | 0 -> List.rev accum
         | n -> all (what :: accum) (n - 1)
      in
      all [] num
   in
   let make_func args =
      Formatcil.cType (Printf.sprintf "void * () (struct %%c:gc *, %s)"
      (String.concat "," args))
      ["gc", Fc(Cil.mkCompInfo true "gc_tag_struct" (fun c -> []) [])]
   in
   let malloc_type = make_func ["int"] in
   let calloc_type = make_func ["int";"int"] in
   let realloc_type = make_func ["void *"; "int"] in
   let kmalloc_type = make_func (generate_list "int" (List.length extra_args)) in
   let vmalloc_type = make_func ["int"] in
   let kcalloc_type = make_func ((generate_list "int" (List.length
   extra_args))) in
   let getfreepage_type = make_func ["int"] in
   fun file name ->
      let create n t =
         (* E.log "Creating gc allocator %s\n" name; *)
         gc_allocated_prototypes := 
            (fun f2 -> findOrCreateFunc f2 (Naming.gc_allocation_name n) t)
            :: ! gc_allocated_prototypes;
         findOrCreateFunc file (Naming.gc_allocation_name n) t
      in
      match allocatorType name with
      | Malloc -> create Malloc malloc_type
      | Calloc -> create Calloc calloc_type
      | Realloc -> create Realloc realloc_type
      | KMalloc -> create KMalloc kmalloc_type
      | VMalloc -> create VMalloc vmalloc_type
      | KCalloc -> create KCalloc kcalloc_type
      | GetFreePage -> create GetFreePage getfreepage_type
;;

(* generate unique numbers ala gensym *)
let unique_number = ref 1;;
let generate_number () =
   let n = !unique_number in
   unique_number := !unique_number + 1;
   n
;;

(* create a function that will walk an array of structs *)
let create_walker file vi current_function complex add_struct =
   let f =
      let name = ("__gc_complex_walker_" ^ vi.svar.vname ^ "_"
      ^ (string_of_int (generate_number ()))) in
      emptyFunction name
      in
      let muck = makeFormalVar f "muck" (Formatcil.cType "void (*)(void *)" []) in
      let var = makeFormalVar f "obj" (TPtr(complex.vtype,[])) in
      let info = makeFormalVar f "info" (Formatcil.cType "unsigned long *" []) in
      let makeIndexVar () = makeTempVar f (Formatcil.cType "unsigned long" []) in
      f.svar.vstorage <- Static;
      (* make a walker for an array of structs *)
      let create_tarray_walker comp size offset =
         let index = makeIndexVar () in
         let stuff =
            let mark = (findOrCreateFunc file Naming.gc_mark (Formatcil.cType
            "void ()(void * )" [])) in
            let gc_comp_info = (Cil.mkCompInfo true "gc_tag_struct" (fun c -> []) []) in
            let tag =
               let v = Cil.makeLocalVar f (Naming.gc_struct_tag_name
               comp) (Formatcil.cType "struct %c:name *" ["name", Fc gc_comp_info]) in
               v.vstorage <- Extern;
               v
               in
               (* call a function for side effects *)
               add_struct comp;
               let mark_for_type = (findOrCreateFunc file
               "gc_mark_for_type" (Formatcil.cType "void ()(void *, struct %c:name * )" ["name", Fc gc_comp_info])) in
               let repair_for_type = (findOrCreateFunc file
               "gc_repair_for_type" (Formatcil.cType "void ()(void * )" [])) in
               Formatcil.cStmts
               "if ( %v:muck == %v:mark ){
                  %l:mark_for_type( & %l:spot, %v:tag );
                } else {
                  %v:repair_for_type( & %l:spot, %v:tag );
                }"
                (fun n t -> makeTempVar vi ~name:n t)
                locUnknown
                ["muck", Fv muck;
                "mark", Fv mark;
                "spot", Fl (offset (Index(Lval(Var
                index,NoOffset),NoOffset)));
                "mark_for_type", Fv mark_for_type;
                "repair_for_type", Fv repair_for_type;
                "tag", Fv tag;
                "obj", Fv var;
                "index", Fv index;
                "info", Fv info]
               in
               mkForIncr index Cil.zero size Cil.one stuff
         in
      (* make a walker for an array of pointers *)
      let create_array_walker size offset =
         let index = makeIndexVar () in
         let body =
            Formatcil.cStmts
            "if ( %v:proc == %v:mark ){
               %v:proc( %l:spot );
             } else {
               %v:proc( & %l:spot );
             }"
             (fun n t -> makeTempVar vi ~name:n t)
             locUnknown
             ["proc", Fv muck;
             "mark", Fv (findOrCreateFunc file Naming.gc_mark (Formatcil.cType "void ()(void * )" []));
             "spot", Fl (offset (Index(Lval(Var index,NoOffset),NoOffset)))]
         in
         mkForIncr index Cil.zero size Cil.one body
      in
      let body =
         let rec loop some_type offset =
            match (Cil.unrollType some_type) with
            | TArray(TComp(comp,_),Some(size),_) ->
                  create_tarray_walker comp size offset
            | TArray(TPtr _,Some(size),_) ->
                  create_array_walker size offset
            | TArray(TArray(a,b,c),Some(size),_) ->
                  let index = makeIndexVar () in
                  let body =
                     loop (TArray(a,b,c))
                     (fun o -> (offset (Index(Lval(Var index,NoOffset),o))))
                  in
                  mkForIncr index Cil.zero size Cil.one body
            | TArray(TNamed(info,a),b,c) ->
                  loop (TArray(Cil.unrollType (TNamed(info,a)),b,c))
                  offset
            | _ -> []
         in
         loop complex.vtype (fun o -> Mem(Lval(Var var,NoOffset)), o)
      in
      f.sbody.bstmts <- body;
      f
;;

class analyzer file call_graph = object(self)
   inherit nopCilVisitor

   val mutable allocated_structs : allocation list = []
   val mutable roots : Cil.global list = []

   method getAllocatedStructs =
      allocated_structs

   method getRoots = roots

   method vglob glob =
      match glob with
      | GVar( var, init, location ) ->
            (* E.log "Visiting global variable %s\n" var.vname; *)
            (* roots <- var :: roots; *)
            roots <- glob :: roots;
            DoChildren

      | GFun(vi,_) ->
            (* E.log "Visit function %s\n" vi.svar.vname; *)
            let can_collect =
               match call_graph with
               | None -> true
               | Some(graph) -> not !use_call_graph || (Cg.can_collect graph vi.svar.vname [])
            in
            let walkers = ref [] in
            let makeWalker current_function complex =
               let walker = create_walker file vi current_function complex
               (fun c -> allocated_structs <- Struct c :: allocated_structs) in
               walkers := (GFun (walker,locUnknown)) :: !walkers;
               walker.svar
            in
            let simple_gc_frame,
                array_gc_frame,
                struct_gc_frame,
                complex_gc_frame = 
                   let makeFrame name size = 
            (* lazily create the frame *)
            let n = ref None in
            fun () ->
               match ! n with
               | None ->
                     let v =
                        (*
                        E.log "Create frame %s in function %s\n" name vi.svar.vname;
                        *)
                        makeVarinfo false (Printf.sprintf "%s_gc_frame" name)
                        (Formatcil.cType "void * [%e:size]" ["size", Fe (Cil.integer size)])
                        (*
                        makeLocalVar vi (Printf.sprintf "%s_gc_frame" name)
                        (Formatcil.cType "void * [%e:size]" ["size", Fe (Cil.integer size)])
                        *)
                     in
                     n := (Some v);
                     v
               | Some v -> v
         in
         (makeFrame "simple" 2),
         (makeFrame "array" 2),
         (makeFrame "struct" 2),
         (makeFrame "complex" 2)
      in
      let simple_frame_index = ref 2 in
      let tagged_frame_index = ref 2 in
      let complex_frame_index = ref 2 in
      let array_frame_index = ref 2 in
      (* a list of instructions that add a variable to a gc frame *)
      let frame_statement = Cil.mkStmt (Instr []) in
      let add_frame_inst i =
         let ok =
            match frame_statement.skind with
            | Instr is -> Instr(is @ [i])
            | _ -> frame_statement.skind
         in
         frame_statement.skind <- ok
      in
      (* this thing adds variables to gc frames *)
      let stacker current_function = object(self)
         inherit nopCilVisitor

         (* list of gc_struct_tags *)
         val mutable tags = []
         (* same as above but store the 'allocation' type instead of the struct
            *)
         val mutable structs = []
         (* vars put into some frame so far *)
         val mutable seen_vars = []

         val mutable local_vars = []

         method getLocalVars = local_vars

         method hasSeen v =
            if List.mem v seen_vars then
               true
            else begin
               seen_vars <- v :: seen_vars;
               false
            end

         method getStructTags =
            structs

         (* lazily create tags *)
         method getTag t =
            let makeTag name =
               let var = Cil.makeVarinfo false name (Formatcil.cType "struct %c:name *"
               ["name", Fc(Cil.mkCompInfo true "gc_tag_struct" (fun c -> []) [])]) in
               var.vstorage <- Extern;
               local_vars <- var :: local_vars;
               var
            in
            let name = 
               match t with
               | Atomic _ -> Naming.gc_standard_atomic_tag
               | Array _ -> Naming.gc_standard_array_tag
               | StructArray(c,r) -> Naming.gc_struct_array_tag_name c
               | Struct comp -> Naming.gc_struct_tag_name comp
            in
            try
               List.find (fun v -> v.vname = name) tags
            with Not_found ->
               let newtag = makeTag name in
               tags <- newtag :: tags;
               (match t with
               | StructArray(c,r) -> structs <- t :: structs
               | Struct comp -> structs <- t :: structs
               | _ -> ());
               newtag

         method makeInfo v =
            let v = Cil.makeVarinfo false (Naming.gc_info v) (Formatcil.cType "int
            [sizeof(%v:v)]" ["v", Fv v])
            in
            local_vars <- v :: local_vars;
            v

         method autotag lval =
            (* E.log "Autotag %a\n" Cil.d_lval lval; *)
            let autotag_field lval_so_far case =
               [Formatcil.cInstr
               "%v:autotag ( & %l:lval, %e:tag );"
               locUnknown
               ["autotag", Fv (findOrCreateFunc file "GC_autotag_union"
               (Formatcil.cType "void ()(void ** p, int tag)" []));
               "lval", Fl lval_so_far;
               "tag", Fe (Cil.integer case)]]
            in
            let rec traverse get_lval current_offset last_offset =
               match current_offset with
               | NoOffset -> []
               | Field(field, more_offsets) -> begin
                  let next_offset =
                     (Cil.addOffset (Field(field, NoOffset)) last_offset)
                  in
                  if field.fcomp.cstruct = true || not (has_pointer_fields
                  field.fcomp) then
                     traverse get_lval more_offsets next_offset
                  else
                     autotag_field (get_lval last_offset)
                     (count_fields field.fcomp field)
                     @
                     traverse get_lval more_offsets next_offset
               end
               | Index(exp,more_offsets) ->
                     traverse get_lval more_offsets (Cil.addOffset (Index
                     (exp,NoOffset)) last_offset)
            in
            match lval with
            | Var v, offset  ->
                  traverse (fun o -> (Var v, o)) offset NoOffset
            | Mem e, offset -> begin
                  match e with
                  | Lval l ->
                        (traverse (fun o -> (Mem (Lval l), o)) offset NoOffset)
                        @
                        (self#autotag l)
                  (* TODO: there might be problems with this *)
                  | _ -> traverse (fun o -> (Mem e, o)) offset NoOffset
            end

            (* lval is the variable to add to some gc frame
             * zero_out is true if the variable should be zero'd out. it should
             * only be true when the variable is local, arguments should not be
             * zero'd out.
             *)
            method add_frame_var lval zero_out =
               let zero_out_pointer v =
                  Formatcil.cInstr
                  "%v:v = 0;"
                  locUnknown
                  ["v", Fv v]
               in
               let zero_out_struct v =
                  Formatcil.cInstr
                  "memset( & %v:v, 0, sizeof( %v:v ) );"
                  locUnknown
                  ["v", Fv v;
                   "memset", Fv (Util.memset file)]
               in
               let zero_out_array v =
                  zero_out_struct v
               in
               (* simple pointer *)
               let add_pointer pointer =
                  let i = 
                        Formatcil.cInstr
                        "%v:gc[ %e:index ] = (void * ) & %v:var;"
                        locUnknown
                        ["gc", Fv (simple_gc_frame ());
                        "index", Fe (Cil.integer ! simple_frame_index);
                        "var", Fv pointer]
                     in
                     simple_frame_index := ! simple_frame_index + 1;
                     add_frame_inst i;
                     if zero_out then begin
                        add_frame_inst (zero_out_pointer pointer);
                        []
                     end else
                        []
               in
               (* struct *)
               let add_struct obj comp =
                  if has_pointer_fields comp then begin
                        let make_index_instr code extra =
                           let i = 
                              Formatcil.cInstr
                              (Printf.sprintf "%%v:gc[ %%e:index ] = %s;" code)
                              locUnknown
                              (["gc", Fv (struct_gc_frame ());
                              "index", Fe (Cil.integer ! tagged_frame_index);]
                              @ extra)
                           in
                           tagged_frame_index := ! tagged_frame_index + 1;
                           i
                        in
                        let i = make_index_instr "(void * ) & %v:var" ["var", Fv
                              obj]
                        in
                        let tag = make_index_instr "(void * ) %v:tag" ["tag", Fv
                        (self#getTag (Struct comp))] in
                        add_frame_inst i;
                        add_frame_inst tag;
                        if comp.cstruct = false || has_union_pointers comp then
                           let info = self#makeInfo obj in
                           add_frame_inst (Formatcil.cInstr "%v:memset( & %v:info, -1,
                           sizeof( %v:info ) );"
                           locUnknown
                           ["info", Fv info;
                           "memset", Fv (Util.memset file)]);
                           add_frame_inst (make_index_instr "(void * ) %v:info"
                           ["info", Fv info]);
                           add_frame_inst (make_index_instr "(void * ) sizeof(
                              %v:var )" ["var", Fv obj]);
                        else begin
                           add_frame_inst (make_index_instr "0" []);
                           add_frame_inst (make_index_instr "0" [])
                        end
                     end else begin
                        ()
                     end;
                     if zero_out then begin
                        add_frame_inst (zero_out_struct obj);
                        []
                     end else
                        []
               in
               (* array of pointers *)
               let add_pointer_array obj size =
                  let make_index_instr code extra =
                     let i =
                        Formatcil.cInstr
                        (Printf.sprintf "%%v:gc[ %%e:index ] = %s;" code)
                        locUnknown
                        (["gc", Fv (array_gc_frame ());
                        "index", Fe (Cil.integer ! array_frame_index);]
                        @ extra)
                     in
                     array_frame_index := ! array_frame_index + 1;
                     i
                   in
                   let i = make_index_instr "(void * ) & %v:var" ["var", Fv obj]
                   in
                   let size = make_index_instr "(void * ) sizeof( %v:var )"
                   ["var", Fv obj] in
                   add_frame_inst i;
                   add_frame_inst size;
                   if zero_out then begin
                      add_frame_inst (zero_out_array obj);
                      []
                   end else
                      []
               in
               (* array of arrays or structs *)
               let add_complex_array obj size =
                  let do_array v =
                     let make_index_instr code extra =
                        let i =
                           Formatcil.cInstr
                           (Printf.sprintf "%%v:gc[ %%e:index ] = %s;" code)
                           locUnknown
                           (["gc", Fv (complex_gc_frame ());
                           "index", Fe (Cil.integer ! complex_frame_index);]
                           @ extra)
                        in
                        complex_frame_index := ! complex_frame_index + 1;
                        i
                     in
                     let i = make_index_instr "(void * ) & %v:var" ["var", Fv v] in
                     let walker = make_index_instr "(void * ) %v:walker"
                     ["walker", Fv (makeWalker vi v)] in
                     add_frame_inst i;
                     add_frame_inst walker;
                     if is_array_of_comp v.vtype then begin
                        let comp = (array_of_comp v.vtype) in
                        if comp.cstruct = false || has_union_pointers comp then
                           begin
                              let info = self#makeInfo v in
                              add_frame_inst (Formatcil.cInstr "%v:memset( & %v:info, -1,
                              sizeof( %v:info ) );"
                              locUnknown
                              ["info", Fv info;
                              "memset", Fv (Util.memset file)]);
                              add_frame_inst (make_index_instr "(void * ) %v:info"
                              ["info", Fv info]);
                              add_frame_inst (make_index_instr "(void * ) sizeof(
                                 %v:var )" ["var", Fv v]);
                           end
                        else begin
                           add_frame_inst (make_index_instr "0" []);
                           add_frame_inst (make_index_instr "0" [])
                        end
                     end else begin
                        add_frame_inst (make_index_instr "0" []);
                        add_frame_inst (make_index_instr "0" [])
                     end;
                     if zero_out then begin
                        add_frame_inst (zero_out_array v);
                        []
                     end else
                        []
                  in
                  if base_type_ptr_or_comp obj.vtype then
                     (* use_comp (array_of_comp v.vtype) *)
                     do_array obj
                  else
                     []
               in
               let rec m2 v t =
                  (* E.log "Check type for %s %a\n" v.vname Cil.d_type t; *)
               match (Cil.unrollType t) with
               | TPtr _ -> add_pointer v
               | TComp(comp,_) -> add_struct v comp
               | TArray(TPtr _,Some(array_size),_) ->
                     add_pointer_array v array_size
               (* | TArray(TComp(comp,_),Some(array_size),_) -> *)
               | TArray(_,Some(array_size),_) ->
                     add_complex_array v array_size
               | TArray _ -> []
               | TInt _ -> []
               | TFloat _ -> []
               | TBuiltin_va_list _ -> []
               | TEnum _ -> []
               | TNamed _ -> raise (Failure "Could not add frame variable. tnamed after unrollType?")
               | TFun _ -> []
               | TVoid _ -> []
               in
               let rec loop (l : Cil.lval option) =
                  match l with
                  | None -> []
                  | Some(Var v, offset) ->
                        if (self#hasSeen v) || v.vglob then
                           []
                        else
                           m2 v v.vtype
                  | Some(Mem exp, offset) ->
                        let rec exploop main =
                           match main with
                           | Lval(host) -> loop (Some host)
                           | BinOp(_, e1, e2, _) -> (exploop e1) @ (exploop e2)
                           | UnOp(_, e, _) -> exploop e
                           | CastE(_, e) -> exploop e
                           | AddrOf lval -> loop (Some lval)
                           | StartOf lval -> loop (Some lval)
                           | _ -> []
                        in
                        exploop exp
               in
               loop lval

               (*
         method vvdec vardec =
            (*
            E.log "Visited %s\n" vardec.vname;
            makeLocalVar vi (Printf.sprintf "foo_%s" vardec.vname) (Formatcil.cType "int" []);
            *)
            ignore(self#add_frame_var (Some (Cil.var vardec)));
            SkipChildren
            *)

         method get_return_type f =
            match f with
            | TFun(ret,_,_,_) -> ret
            | TPtr(t,_) -> self#get_return_type (Cil.unrollType t)
            | _ -> raise (Failure (Pretty.sprint 1000 (Pretty.dprintf "magpie: not a function %a"
            Cil.d_type f)))

         method vinst inst =
            match inst with
            (* | Call(Some (Var vi,vi1), Lval(Var func,b), args, loc) -> *)
            | Call(lval, Lval(Var func,b), args, loc) ->
                  (* E.log "Calling %s. Set %s\n" func.vname vi.svar.vname; *)
                  let auto =
                     match lval with
                     | Some(x) -> self#autotag x
                     | None -> []
                  in
                  let temporary, temp_set =
                     match lval with
                     | Some(x) ->
                           let v = makeTempVar vi (self#get_return_type
                           (Cil.unrollType func.vtype)) in
                           (Some(Cil.var v), [(Formatcil.cInstr "%l:li = %l:v;" loc
                           ["li", Fl x; "v", Fl (Cil.var v)])])
                     | None -> lval, []
                  in
                  let force_gc =
                     Formatcil.cInstr "gc(1);" loc [
                        "gc", Fv (findOrCreateFunc file
                        "garbage_collect" (Formatcil.cType "void ()(int x)" []))]
                  in
                  let do_gc = ref false in
                  let call =
                     if isAllocator func.vname then begin
                        let alloc_type = guessType func args in
                        let newinst =
                           Call(temporary, Lval(Var ((gc_allocator args)
                           file func.vname), b),
                           (Lval (Var (self#getTag alloc_type), NoOffset)) :: args, loc)
                        in
                        begin
                           do_gc := true;
                           newinst
                        end
                        (*
                        if ! debug_mode then
                           newinst :: [force_gc]
                        else
                           newinst
                           *)
                     end else if func.vname = ! free_func then begin
                        Formatcil.cInstr "%v:free (0);" loc ["free", Fv func]
                     end
                     else
                        Call(temporary, Lval(Var func,b), args, loc )
                  in
                  if ! debug_mode && ! do_gc then
                     ChangeTo (call :: (temp_set @ auto) @ [force_gc])
                  else
                     ChangeTo (call :: (temp_set @ auto))
                  (*
                  if can_collect then
                     ChangeTo (call :: temp_set @ auto)
                  else
                     ChangeTo (call :: auto)
                     *)
                  (*
                  let new_call =
                     if isAllocator func.vname then begin
                        let alloc_type = guessType func args in
                        let newinst =
                           Call(temporary, Lval(Var ((gc_allocator args)
                           file func.vname), b),
                           (Lval (Var (self#getTag alloc_type), NoOffset)) :: args, loc)
                        in
                     let sets = [new_call] @ temp_set @ auto
                     in
                     ChangeTo sets
                  end else if func.vname = ! free_func then begin
                     ChangeTo ([(Formatcil.cInstr "%v:free (0);" loc ["free", Fv
                     func])] @ temp_set @ auto)
                  end else
                     ChangeTo (new_call :: temp_set @ auto)
                     *)
            | Set(lval, exp, loc) ->
                  let auto = self#autotag lval in
                  if (is_union_lval lval 0) && (is_union_exp exp 0) then
                     begin
                        (*
                     E.log "Union assignment for value %a\n" Cil.d_lval lval;
                     *)
                     let copy =
                        Formatcil.cInstr "copy(%e:to, %e:from);"
                        loc
                        ["copy", Fv (findOrCreateFunc file
                        (Naming.copy_autotag (base_comp lval))
                        (Formatcil.cType "void ()(void *, void *)" []));
                        "to", Fe (Cil.mkAddrOf lval);
                        "from", Fe (address_of_exp_lval exp)]
                     in
                     ChangeTo (inst :: auto @ [copy])
                     end
                  else
                     begin
                        (*
                        E.log "Not a union assignment %b %b\n"
                        (is_union_lval lval 0)
                        (is_union_exp exp 0);
                        *)
                     ChangeTo (inst :: auto)
                     end
            | _ -> SkipChildren
      end in
      let visit_stack = stacker vi in
      if can_collect then begin
      ignore(List.map (fun v -> visit_stack#add_frame_var (Some (Cil.var v))
      true) vi.slocals);
      ignore(List.map (fun v -> visit_stack#add_frame_var (Some (Cil.var v))
      false) vi.sformals);
      ignore (Cil.visitCilFunction (visit_stack :> nopCilVisitor) vi);
      allocated_structs <- visit_stack#getStructTags @ allocated_structs;
      vi.slocals <- vi.slocals @ visit_stack#getLocalVars;
      let update_frame frame size =
         (*
         E.log "Update frame %s with size %d\n" frame.vname size;
         *)
         frame.vtype <- Formatcil.cType "void * [%e:size]"
         ["size", Fe (Cil.integer size)];
      in
      (*
      update_frame struct_gc_frame ! tagged_frame_index;
      update_frame simple_gc_frame ! simple_frame_index;
      update_frame array_gc_frame ! array_frame_index;
      update_frame complex_gc_frame ! complex_frame_index;
      *)
      (*
      let stack = 
         let n = (makeLocalVar vi Naming.gc_variable_stack (Formatcil.cType "void **"
         []))
         in
         n.vstorage <- Extern;
         n
      in
      *)
      (* frames = list of frame * total size * size * kind *)
      let frames =
         List.map (fun v ->
            match v with
            | frame, a, b, c -> (frame ()),a,b,c)
         (List.filter (fun v -> 
            match v with
            | frame, total_size, size, kind -> size > 0)
         [simple_gc_frame, ! simple_frame_index, (! simple_frame_index) - 2, 0;
         array_gc_frame, ! array_frame_index,  ((! array_frame_index) - 2) / 2, 1;
         complex_gc_frame, ! complex_frame_index, ((! complex_frame_index) - 2 ) / 4, 2;
         struct_gc_frame, ! tagged_frame_index, ((! tagged_frame_index) - 2) /
         4, 3;])
      in
      if (List.length frames) > 0 then begin
         let last_frame = (makeLocalVar vi "GC_last_variable_stack"
         (Formatcil.cType "void **" [])) in
         let save_last =
            Formatcil.cStmt
            "%v:last = %v:get();"
            (fun n t -> makeTempVar vi ~name:n t)
            locUnknown
            ["last", Fv last_frame;
            "get", Fv (findOrCreateFunc file Naming.gc_get_variable_stack
            (Formatcil.cType "void ** ()()" []));]
         in
         let setups =
            try
               concat_lists
               (List.map2
               (fun v last ->
                  match v with
                  | frame, total_size, size, kind ->
                        let memset = Util.memset file
                        in
                        vi.slocals <- vi.slocals @ [frame];
                        update_frame frame total_size;
                        Formatcil.cStmts 
                        "
                        %v:gc [ 0 ] = (void *) %v:stack;
                        %v:gc [ 1 ] = (void *)((%e:size << 2 ) + %e:kind );
                        %v:set( %v:gc );
                        "
                        (fun n t -> makeTempVar vi ~name:n t)
                        locUnknown
                        ["memset", Fv memset;
                        "gc", Fv frame;
                        "size", Fe (Cil.integer size);
                        "kind", Fe (Cil.integer kind);
                        "stack", Fv last;
                        "set", Fv (findOrCreateFunc file Naming.gc_set_variable_stack
                        (Formatcil.cType "void ()( void ** x )" []));])
               frames
               (last_frame :: (removeLast (List.map (fun v -> match v with a, q, b, k ->
                  a) frames))))
            with ZeroArray -> []
         in
         vi.sbody.bstmts <- save_last :: setups @ (frame_statement :: vi.sbody.bstmts);
         let add_gc_frames = object(self)
            inherit nopCilVisitor
            (* start at index 2 in the gc_stack *)
            val mutable simple_index = 2

            method vstmt statement =
               match statement.skind with
               | Return(exp,loc) ->
                     let new_ret = Cil.mkStmt (Return(exp,loc)) in
                     let save =
                        Formatcil.cStmt
                        "%v:set( %v:last );"
                        (fun n t -> makeTempVar vi ~name:n t)
                        locUnknown
                        ["last", Fv last_frame;
                        "set", Fv (findOrCreateFunc file Naming.gc_set_variable_stack
                        (Formatcil.cType "void ()( void ** x )" []));]
                     in
                     statement.skind <- (Block({bstmts = save :: [new_ret]; battrs = []}));
                     SkipChildren
                  | _ -> DoChildren
         end in
         let setjmp_stack = object(self)
            inherit nopCilVisitor

            method vinst inst =
               match inst with
               | Call(_, Lval(Var func,_), _, loc) -> begin
                     try
                        if isSetjmp(func.vname) then
                           let set =
                                let last_frame = (lastElement (List.map (fun v -> match v
                                        with a, q, b, k -> a) frames))
                                in
                                Formatcil.cInstr "%v:set( %v:frame );"
                                loc
                                ["frame", Fv last_frame;
                                 "set", Fv (findOrCreateFunc file Naming.gc_set_variable_stack
                                 (Formatcil.cType "void ()( void ** x )" []));]
                           in
                           ChangeTo (inst :: [set])
                        else
                           SkipChildren
                     with ZeroArray -> SkipChildren
               end
               | _ -> SkipChildren
         end in
         ignore (Cil.visitCilFunction add_gc_frames vi);
         ignore (Cil.visitCilFunction setjmp_stack vi);
         ChangeTo (!walkers @ [glob]);
         end
      else
         ChangeTo (!walkers @ [glob]);
      end
      else begin
         ignore (Cil.visitCilFunction (visit_stack :> nopCilVisitor) vi);
         SkipChildren
      end

      | _ -> DoChildren;

      end;;

class add_init_call file = object(self)
   inherit nopCilVisitor

   method vfunc func =
      if func.svar.vname = "main" then
         let call_gc_init =
            let call = findOrCreateFunc file Naming.gc_initialize
            (Formatcil.cType "void ()()" []) in
            Formatcil.cStmt "%v:func();" 
            (fun n t -> makeTempVar func ~name:n t)
            locUnknown
            ["func", Fv call];
         in
         func.sbody.bstmts <- call_gc_init :: func.sbody.bstmts;
         SkipChildren
      else
         SkipChildren

end;;

let gc_malloc_type =
   Formatcil.cType "void * () (struct %c:gc * tag, int size)"
   ["gc", Fc(Cil.mkCompInfo true "gc_tag_struct" (fun c -> []) [])]
;;
(* (TFun ((TPtr ((TVoid []), [])), Some([("GC_malloc", (TVoid []), [])]), false, [])) *)

let cast_to_void_ptr exp =
   let void_ptr = (TPtr ((TVoid []), [])) in
   (CastE (void_ptr, exp))
;;

(* wrap some statements with switch( autotag(x) ){ case 0 : ... } *)
let wrap_statements_with_switch file func statements lval =
   let body =
      List.map
      (fun s ->
         let break = Cil.mkStmt (Break locUnknown) in
         Cil.mkStmt (Block {bstmts = s :: break :: []; battrs =
            []}))
      statements
      in
   let v = makeTempVar func Cil.intType in
   let base = Formatcil.cInstr "%v:v = %v:auto( & %l:field );"
   locUnknown
   ["v", Fv v; "auto", Fv (findOrCreateFunc file
   Naming.get_autotagged_case (Formatcil.cType "int ()(void * x)" []));
   "field", Fl lval]
   in
   let switch =
      let exp = Lval(Var v, NoOffset) in
      let labels =
         let rec loop stmts num =
            match stmts with
            | s :: ss -> begin
               s.labels <- [Case(Cil.integer num, locUnknown)];
               s :: (loop ss (num + 1))
            end
            | [] -> []
         in
         loop body 0
      in
      Cil.mkStmt
      (Switch(exp, {bstmts = body; battrs = []}, labels, locUnknown))
   in
   Cil.mkStmt (Block {bstmts = Cil.mkStmt (Instr [base]) :: switch :: [];
   battrs = []})

(* mark each field of a struct according to the rules in the matcher function.
 * recursively look at fields of sub-structures.
 * unions are wrapped in a GC_get_autotagged_case to see which field to mark.
 *)
let rec traverse_struct file func get_offset fields (matcher : ('a -> fieldinfo -> stmt
list)) : Cil.stmt list =
   let rec add_field head fs =
      (match fs with
      | x :: xs -> begin
            (let rec match_type tt =
               match tt with
            | TNamed(info,_) -> match_type info.ttype
            | TComp(sub_comp,_) when sub_comp.cstruct = true ->
                  let bodies = add_field (fun offset -> (head (Field
                  (x,offset)))) sub_comp.cfields in
                  [Cil.mkStmt (Block{bstmts = bodies; battrs = []})]
            | TComp(sub_comp,_) when sub_comp.cstruct = false ->
                  let bodies =
                     (traverse_struct
                     file
                     func
                     (fun offset -> (head (Field (x,offset))))
                     sub_comp.cfields
                     matcher)
                  in
                  [wrap_statements_with_switch file func bodies (head (Field
                  (x,NoOffset)))]
            | _ -> matcher head x
            in
            match_type x.ftype)
            @
            (add_field head xs)
      end
      | [] -> [])
   in
   add_field get_offset fields

module Markfuncs =
   struct
      (* mark/repair for structs/unions *)
      let makeFunction func_namer name take_addr file comp =
         let f = emptyFunction (func_namer comp) in
         f.svar.vstorage <- Static;
         let arg = makeFormalVar f "x" (Formatcil.cType "void *" []) in
         let casted = makeTempVar f ~name:"mark" (Formatcil.cType "struct %c:gc *" ["gc",Fc(comp)]) in
         let proc = findOrCreateFunc file name (Formatcil.cType "void ()(void * x)" []) in
         let var_stmt = 
            (Formatcil.cStmt
            ("%v:c = (struct %c:gc *) x_;")
            (fun n t -> makeTempVar f ~name:n t)
            locUnknown
            ["gc",Fc(comp);
            "c", Fv casted;
            "x_",Fv arg])
         in
         let marks =
            let bodies = 
               traverse_struct file f (fun offset ->
                  (Mem(Lval(Var(casted),NoOffset)),offset))
               comp.cfields
               (let rec match_field =
                  (fun (head : (offset -> 'a))
                       (x : fieldinfo) ->
                  let rec tloop t head =
                     let mark_pointer =
                        let void_ptr =
                           (cast_to_void_ptr (Formatcil.cExp (Printf.sprintf
                           "%s %%l:var" (if take_addr then "&" else ""))
                           ["var", Fl(head NoOffset);]))
                        in
                        Formatcil.cStmts
                        (* This should work, but cil complains about it *)
                        (* "%v:mark( ( void * ) ( * %v:arg ) %o:offset ) ;" *)
                        "%v:proc( %e:void_ptr );"
                        (fun n t -> makeTempVar f ~name:n t)
                        locUnknown
                        ["void_ptr", Fe void_ptr;
                        "proc", Fv proc;]
                     in
                     let mark_array t size =
                        let index = Cil.makeTempVar f Cil.intType in
                        let rest =
                           let next_offset =
                              (fun offset ->
                                 (head (Index(Lval(Var index,NoOffset),
                                 offset))))
                        in
                        (* recursively handle arrays *)
                        match (Cil.unrollType t) with
                        | TArray _ -> tloop t next_offset
                        | TPtr _ -> tloop t next_offset
                        | TComp(comp,_) ->
                              let new_head = next_offset in
                              let bodies =
                                 traverse_struct file f new_head
                                 comp.cfields match_field
                              in
                              (match comp.cstruct with
                              | true -> bodies
                              | false -> 
                                    [wrap_statements_with_switch file f bodies
                                    (head NoOffset)])
                              | _ -> []
                        in
                        let loop = mkForIncr index Cil.zero size Cil.one rest
                        in
                        [Cil.mkStmt (Block {bstmts = loop; battrs = []})]
                     in
                     match (Cil.unrollType t) with
                     | TPtr _ -> mark_pointer
                     | TArray(t,Some(size),_) -> mark_array t size
                     | _ -> [Cil.mkStmt (Block {bstmts = []; battrs = []})]
                  in
                  tloop x.ftype (fun offset -> (head (Field(x,offset)))))
               in
               match_field)
            in
            match comp.cstruct with
            | true -> bodies
            | false -> 
               [wrap_statements_with_switch file f bodies
               (Mem(Lval(Var(casted),NoOffset)),NoOffset)]
         in
         let return =
            (Formatcil.cStmt
            ("return;")
            (fun n t -> makeTempVar f ~name:n t)
            locUnknown
            [])
         in
         let body = var_stmt :: marks @ [return] in
         f.sbody <- {battrs = []; bstmts = body};
         f;
   end;;

let makeCopyAutotag file comp =
   let func = emptyFunction (Naming.copy_autotag comp) in
   (* func.svar.vstorage <- Static; *)
   let compPointerType = (Formatcil.cType "struct %c:gc *" ["gc",Fc(comp)]) in
   let dest = makeFormalVar func "dest" compPointerType in
   let src = makeFormalVar func "src" compPointerType in
   let body =
      Formatcil.cStmts
      (*
      "tag( dest, %v:getTag( src ) );"
      *)
      "newtag = getTag( src );
       tag( dest, newtag );"
      (fun n t -> makeTempVar func ~name:n t)
      locUnknown
      ["tag", Fv (findOrCreateFunc file Naming.autotag
      (Formatcil.cType "void ()(void **, int)" []));
       "getTag", Fv (findOrCreateFunc file Naming.get_autotagged_case
       (Formatcil.cType "int ()(void *)" []));
       "dest", Fv dest;
       "src", Fv src;
       "newtag", Fv (Cil.makeLocalVar func "newtag"
       (Formatcil.cType "int" []));
      ];
   in
   func.sbody <- {battrs = []; bstmts = body};
   func

let makeMarkFunction = Markfuncs.makeFunction Naming.gc_mark_name Naming.gc_mark
false;;
let makeRepairFunction = Markfuncs.makeFunction Naming.gc_repair_name
Naming.gc_repair true;;

(* mark/repair for arrays *)
let makeArrayFunction file comp namer take_addr proc_name =
   let gc_comp_info = (Cil.mkCompInfo true "gc_tag_struct" (fun c -> []) []) in
   let make_index arr index : Cil.exp =
      let exp = (Formatcil.cExp "(void **)(%v:casted + %v:index)" ["casted", Fv
      arr; "index", Fv index;])
      in
      exp
      (*
      if not take_addr then
         Lval(Mem exp,NoOffset)
      else
         exp
         *)
      (*
      if not take_addr then
         Lval(Mem (Lval(Cil.var arr)),Index(Lval(Cil.var index),NoOffset))
      else
         Cil.mkAddrOf (Mem (Lval(Cil.var arr)),Index(Lval(Cil.var index),NoOffset))
         *)
   in
   (*
   let make_index_addr arr index =
      let exp = make_index arr index in
      if not take_addr then
         Lval(Cil.mkMem exp NoOffset)
      else
         exp
   in
   *)
   let f = emptyFunction (namer comp) in
   f.svar.vstorage <- Static;
   let arg = makeFormalVar f "x" (Formatcil.cType "void *" []) in
   let tag =
         let var = Cil.makeLocalVar f (Naming.gc_struct_tag_name comp)
         (Formatcil.cType "struct %c:name *"
         ["name", Fc gc_comp_info]) in
         var.vstorage <- Extern;
         var
   in
   let casted = makeTempVar f ~name:"mark" (Formatcil.cType "struct %c:gc *" ["gc",Fc(comp)]) in
   (*
   let proc = findOrCreateFunc file proc_name (Formatcil.cType "void ()(void *
   x, struct %c:tag * tag )" ["tag", Fc gc_comp_info]) in
*)
   let proc = Cil.makeVarinfo false (proc_name comp) (Formatcil.cType "void
   ()(void *)" [])  in
   let end_ = makeTempVar f ~name:"end" (Formatcil.cType "void **" []) in
   let index = makeTempVar f Cil.intType in
   let body = 
      Formatcil.cStmts
      ("%v:index = 0;
        %v:c = (struct %c:gc *) x_;
        %v:end = find_end( %v:c );
        while ( (void **) %e:v_index < %v:end ){
           %v:mark( (void *) %e:v_index );
           %v:index += 1;
        }
      ")
      (fun n t -> makeTempVar f ~name:n t)
      locUnknown
      ["gc",Fc(comp);
      "c", Fv casted;
      "x_",Fv arg;
      "v_index", Fe (make_index casted index);
      (* "v_index_m", Fe (make_index_addr casted index); *)
      "tag", Fv tag;
      "index", Fv index;
      "mark", Fv proc;
      "find_end", Fv (findOrCreateFunc file Naming.find_end_of_object
      (Formatcil.cType "void * ()(void * x)" []));
      "end", Fv end_;]
   in

   (*
   let var_stmt = 
      (Formatcil.cStmt
      ("%v:c = (struct %c:gc * * ) x_;")
      (fun n t -> makeTempVar f ~name:n t)
      locUnknown
      ["gc",Fc(comp);
      "c", Fv casted;
      "x_",Fv arg])
   in
   let return =
      (Formatcil.cStmt
      ("return;")
      (fun n t -> makeTempVar f ~name:n t)
      locUnknown
      [])
   in
   let body = var_stmt :: [return] in
   *)
   f.sbody <- {battrs = []; bstmts = body};
   f
;;

let makeMarkArrayFunction file comp =
   makeArrayFunction file comp Naming.gc_mark_tarray_name false Naming.gc_mark_name;;

let makeRepairArrayFunction file comp =
   makeArrayFunction file comp Naming.gc_repair_tarray_name true Naming.gc_repair_name;;

class tuningVisitor file (init_func : fundec) gc_init_func = object(self)
   inherit nopCilVisitor

   method hasCall stmt func =
      let instrHasCall i =
         match i with
         | Call(_, Lval(Var v,_), _, _) -> v.vname = func.vname
         | _ -> false
      in
      match stmt with
      | Block b ->
            List.exists (fun s -> self#hasCall s func) (List.map (fun s -> s.skind)
            b.bstmts)
      | Instr is ->
            List.exists (fun i -> instrHasCall i) is
      | _ -> false

   method vglob glob =
      match glob with
      | GFun(func,loc) ->
            if func == init_func then begin
               let call =
                  Formatcil.cStmt
                  "%v:call();"
                  (fun n t -> makeTempVar func ~name:n t)
                  locUnknown
                  ["call", Fv gc_init_func]
               in
               if not (self#hasCall (Block func.sbody) gc_init_func) then begin
                  func.sbody.bstmts <- call :: func.sbody.bstmts;
                  ChangeTo ((GVar(gc_init_func,{init = None},locUnknown)) :: glob ::
                     [])
               end else
                  SkipChildren
            end else
               SkipChildren
      | _ -> SkipChildren
end

let createTuningFile filename =
   let file =
      {fileName = filename; globals = []; globinit = None;
      globinitcalled = false}
   in
   file
;;

let make_init_func file structs (roots : Cil.global list) marks =
   let gc_func name =
      try
      (List.find (fun s ->
         s.svar.vname = name) marks).svar
      with Not_found ->
         E.log "Could not find mark for %s\n" name;
         raise (Failure "??")
      (* findOrCreateFunc file name (Formatcil.cType "void ()(void * x)" []) *)
   in
   let gc_comp_info = (Cil.mkCompInfo true "gc_tag_struct" (fun c -> []) []) in
   let gc_add_root =
      findOrCreateFunc file Naming.add_root (Formatcil.cType "void ()( void * x )"
      [])
   in
   let gc_init =
      findOrCreateFunc file Naming.init_tag (Formatcil.cType "struct %c:name *
      ()( %t:tag a, %t:tag b )" ["name", Fc(gc_comp_info); "tag",
      Ft (Formatcil.cType "void ()( void * x )" [])])
   in
   let func_name = ("GC_init_" ^ (Digest.to_hex (Digest.string
   file.fileName)))
   in
   E.log "Created GC initializer %s\n" func_name;
   let new_fun = emptyFunction func_name in
   let body =
      let tags = Hashtbl.create 10 in
      let makeTag name =
         let var = Cil.makeLocalVar new_fun name (Formatcil.cType "struct %c:name *"
         ["name", Fc(gc_comp_info)]) in
         var.vstorage <- Extern;
         var
      in
      let makeStructTag comp =
         try
            Hashtbl.find tags comp
         with Not_found ->
            let tag = makeTag (Naming.gc_struct_tag_name comp) in
            Hashtbl.add tags comp tag;
            tag
      in
      let makeArrayTag comp =
         let tag = makeTag (Naming.gc_struct_array_tag_name comp) in
         tag
      in
      (* initialize the tags *)
      (List.map (fun s ->
         match s with
         | Struct comp ->
               let v = makeStructTag comp in
               let mark = gc_func (Naming.gc_mark_name comp) in
               let repair = gc_func (Naming.gc_repair_name comp) in
               Formatcil.cStmt
               "%v:var = %v:init ( %v:mark, %v:repair ) ;"
               (fun n t -> makeTempVar new_fun ~name:n t)
               locUnknown
               ["var", Fv v;
               "mark", Fv mark;
               "repair", Fv repair;
               "init", Fv gc_init;]
         | StructArray(comp,size) ->
               (*
               let makeTag name =
                  let var = Cil.makeLocalVar new_fun name (Formatcil.cType "struct %c:name *"
                  ["name", Fc(gc_comp_info)]) in
                  var.vstorage <- Extern;
                  var
               in
               *)
               let v = makeArrayTag comp in
               let mark = gc_func (Naming.gc_mark_tarray_name comp) in
               let repair = gc_func (Naming.gc_repair_tarray_name comp) in
               Formatcil.cStmt
               "%v:var = %v:init ( %v:mark, %v:repair ) ;"
               (fun n t -> makeTempVar new_fun ~name:n t)
               locUnknown
               ["var", Fv v;
               "mark", Fv mark;
               "repair", Fv repair;
               "init", Fv gc_init;]
         | _ -> raise (Failure "Not a struct or struct array"))
      structs)
      @
      (* add global variables as roots *)
      (List.fold_left
      (fun a b -> a @ b)
      []
      (List.map
      (fun (root : Cil.global) ->
         let add_pointer offset =
            Formatcil.cStmts
            "%v:add ( (void *) & %l:var );"
            (fun n t -> makeTempVar new_fun ~name:n t)
            locUnknown
            ["add", Fv gc_add_root;
            "var", Fl (offset NoOffset)]
         in
         let add_array root_v offset has_init loop sub_t size =
            if base_type_ptr_or_comp sub_t then begin
               let temp_var = makeTempVar new_fun Cil.intType in
               let bodies = 
                  loop root_v sub_t (fun o -> (offset (Index(Lval(Var
                  temp_var,NoOffset),o))))
                  has_init
               in
               mkForIncr temp_var Cil.zero size Cil.one bodies
            end else
               []
         in
         let add_struct comp offset =
            Formatcil.cStmts
            "%v:add_tagged ( (void *) & %l:var, %v:tag, sizeof( %l:var ) );"
            (fun n t -> makeTempVar new_fun ~name:n t)
            locUnknown
            ["add_tagged", Fv (findOrCreateFunc file Naming.add_root_tagged
            (Formatcil.cType "void ()( void * v, struct %c:gc *, int size )" ["gc", Fc gc_comp_info;]));
            "var", Fl (offset NoOffset);
            "tag", Fv (makeStructTag comp);
            "memset", Fv (Util.memset file);]
         in
         let rec loop root_v some_type offset has_init =
            match (Cil.unrollType some_type) with
            | TPtr(_,_) -> add_pointer offset
            | TArray(sub_t,Some(size),_) -> add_array root_v offset has_init loop sub_t size
            | TComp(comp,_) -> add_struct comp offset
         | _ -> []
         in
         match root with
         | GVar(var,init,loc) ->
               let has_init =
                  match init.init with
                  | None -> false
                  | Some _ -> true
               in
               let body =
                  loop var var.vtype (fun o -> (Var var,o)) has_init
               in
               if false && base_type_ptr_or_comp var.vtype && not has_init then
                  Formatcil.cStmts
                  "memset( & %v:var, 0, sizeof( %v:var ) );"
                  (fun n t -> makeTempVar new_fun ~name:n t)
                  locUnknown
                  ["memset", Fv (Util.memset file);
                  "var", Fv var]
                 @
                 body
               else
                  body
         | _ -> raise (Failure "not a var")
         (* loop root.vtype (fun o -> (Var root,o)) *)
         )
      roots))
   in
   (* create tuning file *)
   begin
      let filename = ! gc_tuning_filename in
      let tuning_file =
         if Sys.file_exists filename then
            Frontc.parse filename ()
         else
            createTuningFile filename
            (*
            {fileName = filename; globals = []; globinit = None;
            globinitcalled = false}
            *)
      in
      let init_func =
         let rec loop globs =
            match globs with
            | x :: xs -> begin
                  match x with
                  | GFun(func,loc) ->
                        if func.svar.vname = "initialize_tags" then
                           func
                        else
                           loop xs
                  | _ -> loop xs
            end
            | [] ->
                  let e = emptyFunction "initialize_tags" in
                  tuning_file.globals <- tuning_file.globals @
                  [(GFun(e,locUnknown))];
                  e
         in
         loop tuning_file.globals
      in
      Cil.visitCilFile ((new tuningVisitor tuning_file init_func new_fun.svar) :> cilVisitor)
      tuning_file;
      (List.iter (fun s ->
         let hasVar v =
            List.exists (fun g ->
               match g with
               | GVar(gvar,_,_) -> gvar.vname = v.vname
               | _ -> false)
            tuning_file.globals
         in
         let add v =
            if not (hasVar v) then
                  tuning_file.globals <- (GVar(v,{init = None},locUnknown)) ::
                     tuning_file.globals
         in
         match s with
         | Struct comp ->
               add (makeGlobalVar (Naming.gc_struct_tag_name comp)
               (TPtr(TComp(gc_comp_info,[]),[])))
         | StructArray(comp,_) -> 
               add (makeGlobalVar (Naming.gc_struct_array_tag_name comp)
               (TPtr(TComp(gc_comp_info,[]),[])))
         | _ -> ())
      structs);
      let out = open_out filename in
      begin
         Cil.dumpFile defaultCilPrinter out filename tuning_file;
         close_out out
      end
   end;
   new_fun.sbody <- {battrs = []; bstmts = body};
   new_fun
;;

(* take a big mess of structs and roots and return a list of Struct and
 * StructArray types
 *)
let flatten_structs roots structs =
   (List.sort
      (fun first second ->
         match first, second with
         | Struct _, Struct _ -> 0
         | Struct _, StructArray _ -> -1
         | StructArray _, Struct _ -> 1
         | _, _ -> 0)
      (removeDuplicatesEq
      ((List.filter
      (fun v ->
         match v with
         | Struct _ | StructArray _ -> true
         (* | StructArray _ -> true *)
         | _ -> false)
      (List.map
      (fun root ->
         let rec loop some_type =
            match (Cil.unrollType some_type) with
            | TComp(comp,_) -> Struct comp
            | TArray(t,_,_) -> loop t
            | _ -> Atomic some_type
         in
         match root with
         | GVar(var,_,_) -> loop var.vtype
         | _ -> raise (Failure "not a gvar"))
      roots))
      @
      (concat_lists (List.map
      (fun v ->
         match v with
         | StructArray(c, r) -> Struct c :: v :: []
         | _ -> v :: [])
      structs)))
      (fun a b ->
         match a,b with
         | Struct c1, Struct c2 -> c1 == c2
         | StructArray(c1,e1), StructArray(c2, e2) ->
               (*
               E.log "Is %s == %s? %b. %a == %a? %b\n" c1.cname c2.cname (c1 ==
                  c2) Cil.d_exp e1 Cil.d_exp e2 (e1 == e2);
                  *)
               c1 == c2
         | _ -> false)))

let allocation_analysis (f:Cil.file) =
   (* E.log "Allocation analysis\n"; *)
   (* let gc_malloc = findOrCreateFunc f (Naming.gc_allocation_name Malloc)
    * gc_malloc_type in *)
   (* E.log "Visiting file %s\n" f.fileName; *)
   let call_graph =
      if ! use_call_graph then begin
         let graph = Cg.make_call_graph f isAllocator in
         Cg.print_statistics graph;
         Some(graph)
      end
      else
         None
   in
   let a = (new analyzer f call_graph) in
   visitCilFile (a :> cilVisitor) f;
   let structs = flatten_structs a#getRoots a#getAllocatedStructs in
   (* mark/repair functions *)
   let marks =
      List.flatten
      (List.map (fun v ->
         let add maker c =
            let func = maker f c in
            ignore(add_function f (GFun(func,locUnknown)));
            func
         in
         match v with
         | Struct c -> begin
            (add makeMarkFunction c) ::
            (add makeRepairFunction c) ::
            if has_union_fields c then
               [(add makeCopyAutotag c)]
            else
               []
         end
         | StructArray(c,size) -> begin
            (add makeMarkArrayFunction c) ::
            (add makeRepairArrayFunction c) ::
            []
         end
         | _ -> [])
      structs)
   in
   (* add_function f (GFun((make_init_func f a#getAllocatedStructs),locUnknown))
    *)
   (* List.iter (fun v -> E.log "handle root %s\n" v.vname) a#getRoots; *)
   (* hack to add prototypes to the file *)
   if ! add_call_to_initialize then
      visitCilFile (new add_init_call f) f;
   List.iter (fun proc -> ignore(proc f)) (! gc_allocated_prototypes);
   f.globinit <- Some(make_init_func f structs a#getRoots marks);
   (* hacks to add define functions/types that are referenced in the .c file *)
   ignore(Cil.findOrCreateFunc f Naming.gc_get_variable_stack (Formatcil.cType
   "void ** ()()" []));
   let tag_struct =
      let gc_comp_info = (Cil.mkCompInfo true "gc_tag_struct" (fun c -> []) []) in
      let v =
         Cil.makeVarinfo false (Printf.sprintf "%s_tag_struct" "gc")
         (Formatcil.cType "struct %c:name *" ["name", Fc gc_comp_info]) in
      v.vstorage <- Extern;
      v
   in
   f.globals <- GVarDecl(tag_struct,locUnknown) :: f.globals;
   if ! do_include_string_h then
      let include_string_h =
         GText("#include <string.h>")
      in
      f.globals <- include_string_h :: f.globals;
;;

(* poor man's string split *)
let split sep str =
   let rec doit accum str =
      match str with
      | "" -> accum
      | _ ->
            try
               let pos = String.index str sep in
               doit ((String.sub str 0 pos) :: accum) (String.sub str (pos + 1)
               ((String.length str) - pos - 1))
            with Not_found ->
               str :: accum
   in
   List.rev (doit [] str)
;;

(*
let x = split ',' "1,2,3" in
List.iter (fun v -> E.log "%s\n" v) x
;;
*)

let feature : Cil.featureDescr =
   let setter who =
      fun s ->
         (setAllocators who (split ',' s))
   in
   { fd_name = "allocanalysis";
   fd_enabled = ref false;
   fd_description = "magpie analysis";
   fd_extraopt = [
      "--tuning", Arg.String (fun s -> gc_tuning_filename := s),
      " Set the filename to write the gc header to. Default is 'tuning.h'";
      "--malloc", Arg.String (setter Malloc),
      " Set allocators that should be treated like malloc. Give a comma seperated string.";
      "--calloc", Arg.String (setter Calloc),
      " Set allocators that should be treated like calloc. Give a comma seperated string.";
      "--realloc", Arg.String (setter Realloc),
      " Set allocators that should be treated like realloc. Give a comma seperated string.";
      "--kmalloc", Arg.String (setter KMalloc),
      " Set allocators that should be treated like kmalloc. Give a comma seperated string.";
      "--vmalloc", Arg.String (setter VMalloc),
      " Set allocators that should be treated like vmalloc. Give a comma seperated string.";
      "--kcalloc", Arg.String (setter KCalloc),
      " Set allocators that should be treated like kcalloc. Give a comma seperated string.";
      "--getfreepage", Arg.String (setter GetFreePage),
      " Set allocators that should be treated like getfreepage. Give a comma seperated string.";
      "--free", Arg.String (fun s -> free_func := s),
      " Set the free function.";
      "--call-graph", Arg.Unit (fun () -> use_call_graph := true),
      " Enable call graph optimizations. This requires all the program source to be available, so be sure to enable merging in Cil.";
      "--dont-init", Arg.Unit (fun () -> add_call_to_initialize := false),
      " Do not add a call to GC_initialize() to main.";
      "--dont-include-string", Arg.Unit (fun () -> do_include_string_h :=
         false),
         " Do not add '#include <string.h>' to the resulting .c file.";
        ];
        fd_doit = allocation_analysis;
        fd_post_check = true
   }
