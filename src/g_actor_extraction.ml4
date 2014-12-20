(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2014     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* ML names *)

open Vernacexpr
open Pcoq
open Genarg
open Pp
open Names
open Nameops
open Actor_table
open Actor_extract_env

let pr_mlname _ _ _ s = spc () ++ qs s

ARGUMENT EXTEND actor_mlname
  TYPED AS string
  PRINTED BY pr_mlname
| [ preident(id) ] -> [ id ]
| [ string(s) ] -> [ s ]
END

let pr_int_or_id _ _ _ = function
  | ArgInt i -> int i
  | ArgId id -> pr_id id

ARGUMENT EXTEND actor_int_or_id
  TYPED AS actor_int_or_id
  PRINTED BY pr_int_or_id
| [ preident(id) ] -> [ ArgId (id_of_string id) ]
| [ integer(i) ] -> [ ArgInt i ]
END

let pr_language = function
  | Ocaml -> str "Ocaml"
  | Haskell -> str "Haskell"
  | Scheme -> str "Scheme"
  | Erlang -> str "Erlang"

VERNAC ARGUMENT EXTEND actor_language
PRINTED BY pr_language
| [ "Ocaml" ] -> [ Ocaml ]
| [ "Haskell" ] -> [ Haskell ]
| [ "Scheme" ] -> [ Scheme ]
| [ "Erlang" ] -> [ Erlang ]
END

(* Extraction commands *)

VERNAC COMMAND EXTEND ActorExtraction
(* ActorExtraction in the Coq toplevel *)
| [ "ActorExtraction" global(x) ] -> [ simple_extraction x ]
| [ "Recursive" "ActorExtraction" ne_global_list(l) ] -> [ full_extraction None l ]

(* Monolithic extraction to a file *)
| [ "ActorExtraction" string(f) ne_global_list(l) ]
  -> [ full_extraction (Some f) l ]
END

VERNAC COMMAND EXTEND SeparateActorExtraction
(* Same, with content splitted in several files *)
| [ "Separate" "ActorExtraction" ne_global_list(l) ]
  -> [ separate_extraction l ]
END

(* Modular extraction (one Coq library = one ML module) *)
VERNAC COMMAND EXTEND ActorExtractionLibrary
| [ "ActorExtraction" "Library" ident(m) ]
  -> [ extraction_library false m ]
END

VERNAC COMMAND EXTEND RecursiveActorExtractionLibrary
| [ "Recursive" "ActorExtraction" "Library" ident(m) ]
  -> [ extraction_library true m ]
END

(* Target Language *)
VERNAC COMMAND EXTEND ActorExtractionLanguage
| [ "ActorExtraction" "Language" actor_language(l) ]
  -> [ extraction_language l ]
END

VERNAC COMMAND EXTEND ActorExtractionInline
(* Custom inlining directives *)
| [ "ActorExtraction" "Inline" ne_global_list(l) ]
  -> [ extraction_inline true l ]
END

VERNAC COMMAND EXTEND ActorExtractionNoInline
| [ "ActorExtraction" "NoInline" ne_global_list(l) ]
  -> [ extraction_inline false l ]
END

VERNAC COMMAND EXTEND PrintActorExtractionInline
| [ "Print" "ActorExtraction" "Inline" ]
  -> [ print_extraction_inline () ]
END

VERNAC COMMAND EXTEND ResetActorExtractionInline
| [ "Reset" "ActorExtraction" "Inline" ]
  -> [ reset_extraction_inline () ]
END

VERNAC COMMAND EXTEND ActorExtractionImplicit
(* Custom implicit arguments of some csts/inds/constructors *)
| [ "ActorExtraction" "Implicit" global(r) "[" actor_int_or_id_list(l) "]" ]
  -> [ extraction_implicit r l ]
END

VERNAC COMMAND EXTEND ActorExtractionBlacklist
(* Force ActorExtraction to not use some filenames *)
| [ "ActorExtraction" "Blacklist" ne_ident_list(l) ]
  -> [ extraction_blacklist l ]
END

VERNAC COMMAND EXTEND PrintActorExtractionBlacklist
| [ "Print" "ActorExtraction" "Blacklist" ]
  -> [ print_extraction_blacklist () ]
END

VERNAC COMMAND EXTEND ResetActorExtractionBlacklist
| [ "Reset" "ActorExtraction" "Blacklist" ]
  -> [ reset_extraction_blacklist () ]
END


(* Overriding of a Coq object by an ML one *)
VERNAC COMMAND EXTEND ActorExtractionConstant
| [ "ActorExtract" "Constant" global(x) string_list(idl) "=>" actor_mlname(y) ]
  -> [ extract_constant_inline false x idl y ]
END

VERNAC COMMAND EXTEND ActorExtractionInlinedConstant
| [ "ActorExtract" "Inlined" "Constant" global(x) "=>" actor_mlname(y) ]
  -> [ extract_constant_inline true x [] y ]
END

VERNAC COMMAND EXTEND ActorExtractionInductive
| [ "ActorExtract" "Inductive" global(x) "=>"
    actor_mlname(id) "[" actor_mlname_list(idl) "]" string_opt(o) ]
  -> [ extract_inductive x id idl o ]
END
