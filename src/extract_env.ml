(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Declarations
open Names
open Libnames
open Pp
open Util
open Miniml
open Table
open Extraction
open Modutil
open Common
open Mod_subst

(***************************************)
(*S Part I: computing Coq environment. *)
(***************************************)

let toplevel_env () =
  let seg = Lib.contents_after None in
  let get_reference = function
    | (_,kn), Lib.Leaf o ->
	let mp,_,l = repr_kn kn in
	let seb = match Libobject.object_tag o with
	  | "CONSTANT" -> SFBconst (Global.lookup_constant (constant_of_kn kn))
	  | "INDUCTIVE" -> SFBmind (Global.lookup_mind (mind_of_kn kn))
	  | "MODULE" -> SFBmodule (Global.lookup_module (MPdot (mp,l)))
	  | "MODULE TYPE" ->
	      SFBmodtype (Global.lookup_modtype (MPdot (mp,l)))
	  | _ -> failwith "caught"
	in l,seb
    | _ -> failwith "caught"
  in
  SEBstruct (List.rev (map_succeed get_reference seg))


let environment_until dir_opt =
  let rec parse = function
    | [] when dir_opt = None -> [current_toplevel (), toplevel_env ()]
    | [] -> []
    | d :: l ->
	match (Global.lookup_module (MPfile d)).mod_expr with
	  | Some meb ->
	      if dir_opt = Some d then [MPfile d, meb]
	      else (MPfile d, meb) :: (parse l)
	  | _ -> assert false
  in parse (Library.loaded_libraries ())


(*s Visit:
  a structure recording the needed dependencies for the current extraction *)

module type VISIT = sig
  (* Reset the dependencies by emptying the visit lists *)
  val reset : unit -> unit

  (* Add the module_path and all its prefixes to the mp visit list *)
  val add_mp : module_path -> unit

  (* Same, but we'll keep all fields of these modules *)
  val add_mp_all : module_path -> unit

  (* Add kernel_name / constant / reference / ... in the visit lists.
     These functions silently add the mp of their arg in the mp list *)
  val add_ind : mutual_inductive -> unit
  val add_con : constant -> unit
  val add_ref : global_reference -> unit
  val add_decl_deps : ml_decl -> unit
  val add_spec_deps : ml_spec -> unit

  (* Test functions:
     is a particular object a needed dependency for the current extraction ? *)
  val needed_ind : mutual_inductive -> bool
  val needed_con : constant -> bool
  val needed_mp : module_path -> bool
  val needed_mp_all : module_path -> bool
end

module Visit : VISIT = struct
  (* What used to be in a single KNset should now be split into a KNset
     (for inductives and modules names) and a Cset_env for constants
     (and still the remaining MPset) *)
  type must_visit =
      { mutable ind : KNset.t; mutable con : KNset.t;
	mutable mp : MPset.t; mutable mp_all : MPset.t }
  (* the imperative internal visit lists *)
  let v = { ind = KNset.empty ; con = KNset.empty ;
	    mp = MPset.empty; mp_all = MPset.empty }
  (* the accessor functions *)
  let reset () =
    v.ind <- KNset.empty;
    v.con <- KNset.empty;
    v.mp <- MPset.empty;
    v.mp_all <- MPset.empty
  let needed_ind i = KNset.mem (user_mind i) v.ind
  let needed_con c = KNset.mem (user_con c) v.con
  let needed_mp mp = MPset.mem mp v.mp || MPset.mem mp v.mp_all
  let needed_mp_all mp = MPset.mem mp v.mp_all
  let add_mp mp =
    check_loaded_modfile mp; v.mp <- MPset.union (prefixes_mp mp) v.mp
  let add_mp_all mp =
    check_loaded_modfile mp; v.mp <- MPset.union (prefixes_mp mp) v.mp;
    v.mp_all <- MPset.add mp v.mp_all
  let add_ind i =
    let kn = user_mind i in
    v.ind <- KNset.add kn v.ind; add_mp (modpath kn)
  let add_con c =
    let kn = user_con c in
    v.con <- KNset.add kn v.con; add_mp (modpath kn)
  let add_ref = function
    | ConstRef c -> add_con c
    | IndRef (ind,_) | ConstructRef ((ind,_),_) -> add_ind ind
    | VarRef _ -> assert false
  let add_decl_deps = decl_iter_references add_ref add_ref add_ref
  let add_spec_deps = spec_iter_references add_ref add_ref add_ref
end

exception Impossible

let check_arity env cb =
  let t = Typeops.type_of_constant_type env cb.const_type in
  if Reduction.is_arity env t then raise Impossible

let check_fix env cb i =
  match cb.const_body with
    | Def lbody ->
	(match kind_of_term (Declarations.force lbody) with
	  | Fix ((_,j),recd) when i=j -> check_arity env cb; (true,recd)
	  | CoFix (j,recd) when i=j -> check_arity env cb; (false,recd)
	  | _ -> raise Impossible)
    | Undef _ | OpaqueDef _ -> raise Impossible

let prec_declaration_equal (na1, ca1, ta1) (na2, ca2, ta2) =
  na1 = na2 &&
  array_equal eq_constr ca1 ca2 &&
  array_equal eq_constr ta1 ta2

let factor_fix env l cb msb =
  let _,recd as check = check_fix env cb 0 in
  let n = Array.length (let fi,_,_ = recd in fi) in
  if n = 1 then [|l|], recd, msb
  else begin
    if List.length msb < n-1 then raise Impossible;
    let msb', msb'' = list_chop (n-1) msb in
    let labels = Array.make n l in
    list_iter_i
      (fun j ->
	 function
	   | (l,SFBconst cb') ->
	       let check' = check_fix env cb' (j+1) in
	       if not (fst check = fst check' &&
		   prec_declaration_equal (snd check) (snd check'))
	       then raise Impossible;
	       labels.(j+1) <- l;
	   | _ -> raise Impossible) msb';
    labels, recd, msb''
  end

(** Expanding a [struct_expr_body] into a version without abbreviations
    or functor applications. This is done via a detour to entries
    (hack proposed by Elie)
*)

let rec seb2mse = function
  | SEBapply (s,s',_) -> Entries.MSEapply(seb2mse s, seb2mse s')
  | SEBident mp -> Entries.MSEident mp
  | _ -> failwith "seb2mse: received a non-atomic seb"

let expand_seb env mp seb =
  let seb,_,_,_ =
    let inl = Some (Flags.get_inline_level()) in
    Mod_typing.translate_struct_module_entry env mp inl (seb2mse seb)
  in seb

(** When possible, we use the nicer, shorter, algebraic type structures
    instead of the expanded ones. *)

let my_type_of_mb mb =
  let m0 = mb.mod_type in
  match mb.mod_type_alg with Some m -> m0,m | None -> m0,m0

let my_type_of_mtb mtb =
  let m0 = mtb.typ_expr in
  match mtb.typ_expr_alg with Some m -> m0,m | None -> m0,m0

(** Ad-hoc update of environment, inspired by [Mod_type.check_with_aux_def].
    To check with Elie. *)

let rec msid_of_seb = function
  | SEBident mp -> mp
  | SEBwith (seb,_) -> msid_of_seb seb
  | _ -> assert false

let env_for_mtb_with_def env mp seb idl =
  let sig_b = match seb with
    | SEBstruct(sig_b) -> sig_b
    | _ -> assert false
  in
  let l = label_of_id (List.hd idl) in
  let spot = function (l',SFBconst _) -> l = l' | _ -> false in
  let before = fst (list_split_when spot sig_b) in
  Modops.add_signature mp before empty_delta_resolver env

(* From a [structure_body] (i.e. a list of [structure_field_body])
   to specifications. *)

let rec extract_sfb_spec env mp = function
  | [] -> []
  | (l,SFBconst cb) :: msig ->
      let kn = make_con mp empty_dirpath l in
      let s = extract_constant_spec env kn cb in
      let specs = extract_sfb_spec env mp msig in
      if logical_spec s then specs
      else begin Visit.add_spec_deps s; (l,Spec s) :: specs end
  | (l,SFBmind _) :: msig ->
      let mind = make_mind mp empty_dirpath l in
      let s = Sind (mind, extract_inductive env mind) in
      let specs = extract_sfb_spec env mp msig in
      if logical_spec s then specs
      else begin Visit.add_spec_deps s; (l,Spec s) :: specs end
  | (l,SFBmodule mb) :: msig ->
      let specs = extract_sfb_spec env mp msig in
      let spec = extract_seb_spec env mb.mod_mp (my_type_of_mb mb) in
      (l,Smodule spec) :: specs
  | (l,SFBmodtype mtb) :: msig ->
      let specs = extract_sfb_spec env mp msig in
      let spec = extract_seb_spec env mtb.typ_mp (my_type_of_mtb mtb) in
      (l,Smodtype spec) :: specs

(* From [struct_expr_body] to specifications *)

(* Invariant: the [seb] given to [extract_seb_spec] should either come
   from a [mod_type] or [type_expr] field, or their [_alg] counterparts.
   This way, any encountered [SEBident] should be a true module type.
*)

and extract_seb_spec env mp1 (seb,seb_alg) = match seb_alg with
  | SEBident mp -> Visit.add_mp_all mp; MTident mp
  | SEBwith(seb',With_definition_body(idl,cb))->
      let env' = env_for_mtb_with_def env (msid_of_seb seb') seb idl in
      let mt = extract_seb_spec env mp1 (seb,seb') in
      (match extract_with_type env' cb with (* cb peut contenir des kn  *)
	 | None -> mt
	 | Some (vl,typ) -> MTwith(mt,ML_With_type(idl,vl,typ)))
  | SEBwith(seb',With_module_body(idl,mp))->
      Visit.add_mp_all mp;
      MTwith(extract_seb_spec env mp1 (seb,seb'),
	     ML_With_module(idl,mp))
  | SEBfunctor (mbid, mtb, seb_alg') ->
      let seb' = match seb with
	| SEBfunctor (mbid',_,seb') when mbid' = mbid -> seb'
	| _ -> assert false
      in
      let mp = MPbound mbid in
      let env' = Modops.add_module (Modops.module_body_of_type mp mtb) env in
      MTfunsig (mbid, extract_seb_spec env mp (my_type_of_mtb mtb),
		extract_seb_spec env' mp1 (seb',seb_alg'))
  | SEBstruct (msig) ->
      let env' = Modops.add_signature mp1 msig empty_delta_resolver env in
      MTsig (mp1, extract_sfb_spec env' mp1 msig)
  | SEBapply _ ->
      if seb <> seb_alg then extract_seb_spec env mp1 (seb,seb)
      else assert false



(* From a [structure_body] (i.e. a list of [structure_field_body])
   to implementations.

   NB: when [all=false], the evaluation order of the list is
   important: last to first ensures correct dependencies.
*)

let rec extract_sfb env mp all = function
  | [] -> []
  | (l,SFBconst cb) :: msb ->
      (try
	 let vl,recd,msb = factor_fix env l cb msb in
	 let vc = Array.map (make_con mp empty_dirpath) vl in
	 let ms = extract_sfb env mp all msb in
	 let b = array_exists Visit.needed_con vc in
	 if all || b then
	   let d = extract_fixpoint env vc recd in
	   if (not b) && (logical_decl d) then ms
	   else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
	 else ms
       with Impossible ->
	 let ms = extract_sfb env mp all msb in
	 let c = make_con mp empty_dirpath l in
	 let b = Visit.needed_con c in
	 if all || b then
	   let d = extract_constant env c cb in
	   if (not b) && (logical_decl d) then ms
	   else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
	 else ms)
  | (l,SFBmind mib) :: msb ->
      let ms = extract_sfb env mp all msb in
      let mind = make_mind mp empty_dirpath l in
      let b = Visit.needed_ind mind in
      if all || b then
	let d = Dind (mind, extract_inductive env mind) in
	if (not b) && (logical_decl d) then ms
	else begin Visit.add_decl_deps d; (l,SEdecl d) :: ms end
      else ms
  | (l,SFBmodule mb) :: msb ->
      let ms = extract_sfb env mp all msb in
      let mp = MPdot (mp,l) in
      if all || Visit.needed_mp mp then
	(l,SEmodule (extract_module env mp true mb)) :: ms
      else ms
  | (l,SFBmodtype mtb) :: msb ->
      let ms = extract_sfb env mp all msb in
      let mp = MPdot (mp,l) in
       if all || Visit.needed_mp mp then
	(l,SEmodtype (extract_seb_spec env mp (my_type_of_mtb mtb))) :: ms
      else ms

(* From [struct_expr_body] to implementations *)

and extract_seb env mp all = function
  | (SEBident _ | SEBapply _) as seb when lang () <> Ocaml ->
      (* in Haskell/Scheme, we expand everything *)
      extract_seb env mp all (expand_seb env mp seb)
  | SEBident mp ->
      if is_modfile mp && not (modular ()) then error_MPfile_as_mod mp false;
      Visit.add_mp_all mp; MEident mp
  | SEBapply (meb, meb',_) ->
      MEapply (extract_seb env mp true meb,
	       extract_seb env mp true meb')
  | SEBfunctor (mbid, mtb, meb) ->
      let mp1 = MPbound mbid in
      let env' = Modops.add_module (Modops.module_body_of_type  mp1 mtb)
	env  in
      MEfunctor (mbid, extract_seb_spec env mp1 (my_type_of_mtb mtb),
		 extract_seb env' mp true meb)
  | SEBstruct (msb) ->
      let env' = Modops.add_signature mp msb empty_delta_resolver env in
      MEstruct (mp,extract_sfb env' mp all msb)
  | SEBwith (_,_) -> anomaly "Not available yet"

and extract_module env mp all mb =
  (* A module has an empty [mod_expr] when :
     - it is a module variable (for instance X inside a Module F [X:SIG])
     - it is a module assumption (Declare Module).
     Since we look at modules from outside, we shouldn't have variables.
     But a Declare Module at toplevel seems legal (cf #2525). For the
     moment we don't support this situation. *)
  match mb.mod_expr with
    | None -> error_no_module_expr mp
    | Some me ->
      { ml_mod_expr = extract_seb env mp all me;
	ml_mod_type = extract_seb_spec env mp (my_type_of_mb mb) }


let unpack = function MEstruct (_,sel) -> sel | _ -> assert false

let mono_environment refs mpl =
  Visit.reset ();
  List.iter Visit.add_ref refs;
  List.iter Visit.add_mp_all mpl;
  let env = Global.env () in
  let l = List.rev (environment_until None) in
  List.rev_map
    (fun (mp,m) -> mp, unpack (extract_seb env mp (Visit.needed_mp_all mp) m))
    l

(**************************************)
(*S Part II : Input/Output primitives *)
(**************************************)

let descr () = match lang () with
  | Ocaml -> Ocaml.ocaml_descr
  | Haskell -> Haskell.haskell_descr
  | Scheme -> Scheme.scheme_descr

(* From a filename string "foo.ml" or "foo", builds "foo.ml" and "foo.mli"
   Works similarly for the other languages. *)

let default_id = id_of_string "Main"

let mono_filename f =
  let d = descr () in
  match f with
    | None -> None, None, default_id
    | Some f ->
	let f =
	  if Filename.check_suffix f d.file_suffix then
	    Filename.chop_suffix f d.file_suffix
	  else f
	in
	let id =
	  if lang () <> Haskell then default_id
	  else
            try id_of_string (Filename.basename f)
	    with e when Errors.noncritical e ->
              error "Extraction: provided filename is not a valid identifier"
	in
	Some (f^d.file_suffix), Option.map ((^) f) d.sig_suffix, id

(* Builds a suitable filename from a module id *)

let module_filename mp =
  let f = file_of_modfile mp in
  let d = descr () in
  Some (f^d.file_suffix), Option.map ((^) f) d.sig_suffix, id_of_string f

(*s Extraction of one decl to stdout. *)

let print_one_decl struc mp decl =
  let d = descr () in
  reset_renaming_tables AllButExternal;
  set_phase Pre;
  ignore (d.pp_struct struc);
  set_phase Impl;
  push_visible mp [];
  msgnl (d.pp_decl decl);
  pop_visible ()

(*s Extraction of a ml struct to a file. *)

(** For Recursive Extraction, writing directly on stdout
    won't work with coqide, we use a buffer instead *)

let buf = Buffer.create 1000

let formatter dry file =
  let ft =
    if dry then Format.make_formatter (fun _ _ _ -> ()) (fun _ -> ())
    else
      match file with
	| Some f -> Pp_control.with_output_to f
	| None -> Format.formatter_of_buffer buf
  in
  (* We never want to see ellipsis ... in extracted code *)
  Format.pp_set_max_boxes ft max_int;
  (* We reuse the width information given via "Set Printing Width" *)
  (match Pp_control.get_margin () with
    | None -> ()
    | Some i ->
      Format.pp_set_margin ft i;
      Format.pp_set_max_indent ft (i-10));
      (* note: max_indent should be < margin above, otherwise it's ignored *)
  ft

let print_structure_to_file (fn,si,mo) dry struc =
  Buffer.clear buf;
  let d = descr () in
  reset_renaming_tables AllButExternal;
  let unsafe_needs = {
    mldummy = struct_ast_search ((=) MLdummy) struc;
    tdummy = struct_type_search Mlutil.isDummy struc;
    tunknown = struct_type_search ((=) Tunknown) struc;
    magic =
      if lang () <> Haskell then false
      else struct_ast_search (function MLmagic _ -> true | _ -> false) struc }
  in
  (* First, a dry run, for computing objects to rename or duplicate *)
  set_phase Pre;
  let devnull = formatter true None in
  msg_with devnull (d.pp_struct struc);
  let opened = opened_libraries () in
  (* Print the implementation *)
  let cout = if dry then None else Option.map open_out fn in
  let ft = formatter dry cout in
  begin try
    (* The real printing of the implementation *)
    set_phase Impl;
    msg_with ft (d.preamble mo opened unsafe_needs);
    msg_with ft (d.pp_struct struc);
    Option.iter close_out cout;
  with reraise ->
    Option.iter close_out cout; raise reraise
  end;
  if not dry then Option.iter info_file fn;
  (* Now, let's print the signature *)
  Option.iter
    (fun si ->
       let cout = open_out si in
       let ft = formatter false (Some cout) in
       begin try
	 set_phase Intf;
	 msg_with ft (d.sig_preamble mo opened unsafe_needs);
	 msg_with ft (d.pp_sig (signature_of_structure struc));
	 close_out cout;
       with reraise ->
	 close_out cout; raise reraise
       end;
       info_file si)
    (if dry then None else si);
  (* Print the buffer content via Coq standard formatter (ok with coqide). *)
  if Buffer.length buf <> 0 then begin
    Pp.message (Buffer.contents buf);
    Buffer.reset buf
  end


(*********************************************)
(*s Part III: the actual extraction commands *)
(*********************************************)


let reset () =
  Visit.reset (); reset_tables (); reset_renaming_tables Everything

let init modular library =
  check_inside_section (); check_inside_module ();
  set_keywords (descr ()).keywords;
  set_modular modular;
  set_library library;
  reset ();
  if modular && lang () = Scheme then error_scheme ()

let warns () =
  warning_opaques (access_opaque ());
  warning_axioms ()

(* From a list of [reference], let's retrieve whether they correspond
   to modules or [global_reference]. Warn the user if both is possible. *)

let rec locate_ref = function
  | [] -> [],[]
  | r::l ->
      let q = snd (qualid_of_reference r) in
      let mpo = try Some (Nametab.locate_module q) with Not_found -> None
      and ro =
        try Some (Smartlocate.global_with_alias r)
        with e when Errors.noncritical e -> None
      in
      match mpo, ro with
	| None, None -> Nametab.error_global_not_found q
	| None, Some r -> let refs,mps = locate_ref l in r::refs,mps
	| Some mp, None -> let refs,mps = locate_ref l in refs,mp::mps
	| Some mp, Some r ->
	    warning_both_mod_and_cst q mp r;
	    let refs,mps = locate_ref l in refs,mp::mps

(*s Recursive extraction in the Coq toplevel. The vernacular command is
    \verb!Recursive Extraction! [qualid1] ... [qualidn]. Also used when
    extracting to a file with the command:
    \verb!Extraction "file"! [qualid1] ... [qualidn]. *)

let full_extr f (refs,mps) =
  init false false;
  List.iter (fun mp -> if is_modfile mp then error_MPfile_as_mod mp true) mps;
  let struc = optimize_struct (refs,mps) (mono_environment refs mps) in
  warns ();
  print_structure_to_file (mono_filename f) false struc;
  reset ()

let full_extraction f lr = full_extr f (locate_ref lr)

(*s Separate extraction is similar to recursive extraction, with the output
   decomposed in many files, one per Coq .v file *)

let separate_extraction lr =
  init true false;
  let refs,mps = locate_ref lr in
  let struc = optimize_struct (refs,mps) (mono_environment refs mps) in
  warns ();
  let print = function
    | (MPfile dir as mp, sel) as e ->
	print_structure_to_file (module_filename mp) false [e]
    | _ -> assert false
  in
  List.iter print struc;
  reset ()

(*s Simple extraction in the Coq toplevel. The vernacular command
    is \verb!Extraction! [qualid]. *)

let simple_extraction r =
  Vernacentries.dump_global (Genarg.AN r);
  match locate_ref [r] with
  | ([], [mp]) as p -> full_extr None p
  | [r],[] ->
      init false false;
      let struc = optimize_struct ([r],[]) (mono_environment [r] []) in
      let d = get_decl_in_structure r struc in
      warns ();
      if is_custom r then msgnl (str "(** User defined extraction *)");
      print_one_decl struc (modpath_of_r r) d;
      reset ()
  | _ -> assert false


(*s (Recursive) Extraction of a library. The vernacular command is
  \verb!(Recursive) Extraction Library! [M]. *)

let extraction_library is_rec m =
  init true true;
  let dir_m =
    let q = qualid_of_ident m in
    try Nametab.full_name_module q with Not_found -> error_unknown_module q
  in
  Visit.add_mp_all (MPfile dir_m);
  let env = Global.env () in
  let l = List.rev (environment_until (Some dir_m)) in
  let select l (mp,meb) =
    if Visit.needed_mp mp
    then (mp, unpack (extract_seb env mp true meb)) :: l
    else l
  in
  let struc = List.fold_left select [] l in
  let struc = optimize_struct ([],[]) struc in
  warns ();
  let print = function
    | (MPfile dir as mp, sel) as e ->
	let dry = not is_rec && dir <> dir_m in
	print_structure_to_file (module_filename mp) dry [e]
    | _ -> assert false
  in
  List.iter print struc;
  reset ()
