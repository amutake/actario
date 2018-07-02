(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pcoq.Prim

DECLARE PLUGIN "extraction_plugin"

(* ML names *)

open Ltac_plugin
open Genarg
open Stdarg
open Pp
open Names
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
  | ArgId id -> Id.print id

ARGUMENT EXTEND actor_int_or_id
  PRINTED BY pr_int_or_id
| [ preident(id) ] -> [ ArgId (Id.of_string id) ]
| [ integer(i) ] -> [ ArgInt i ]
END

let pr_language = function
  | Ocaml -> str "OCaml"
  | Haskell -> str "Haskell"
  | Scheme -> str "Scheme"
  | Erlang -> str "Erlang"
  | JSON -> str "JSON"

let warn_deprecated_ocaml_spelling =
  CWarnings.create ~name:"deprecated-ocaml-spelling" ~category:"deprecated"
    (fun () ->
      strbrk ("The spelling \"OCaml\" should be used instead of \"Ocaml\"."))

VERNAC ARGUMENT EXTEND actor_language
PRINTED BY pr_language
| [ "Erlang" ] -> [ Erlang ]
| [ "JSON" ] -> [ JSON ]
END

(* Extraction commands *)

VERNAC COMMAND EXTEND ActorExtraction CLASSIFIED AS QUERY
(* ActorExtraction in the Coq toplevel *)
| [ "ActorExtraction" global(x) ] -> [ simple_extraction x ]
| [ "Recursive" "ActorExtraction" ne_global_list(l) ] -> [ full_extraction None l ]

(* Monolithic extraction to a file *)
| [ "ActorExtraction" string(f) ne_global_list(l) ]
  -> [ full_extraction (Some f) l ]

(* Extraction to a temporary file and OCaml compilation *)
| [ "ActorExtraction" "TestCompile" ne_global_list(l) ]
  -> [ extract_and_compile l ]
END

VERNAC COMMAND EXTEND SeparateActorExtraction CLASSIFIED AS QUERY
(* Same, with content splitted in several files *)
| [ "Separate" "ActorExtraction" ne_global_list(l) ]
  -> [ separate_extraction l ]
END

(* Modular extraction (one Coq library = one ML module) *)
VERNAC COMMAND EXTEND ActorExtractionLibrary CLASSIFIED AS QUERY
| [ "ActorExtraction" "Library" ident(m) ]
  -> [ extraction_library false m ]
END

VERNAC COMMAND EXTEND RecursiveActorExtractionLibrary CLASSIFIED AS QUERY
| [ "Recursive" "ActorExtraction" "Library" ident(m) ]
  -> [ extraction_library true m ]
END

(* Target Language *)
VERNAC COMMAND EXTEND ExtractionActorLanguage CLASSIFIED AS SIDEFF
| [ "ActorExtraction" "Language" actor_language(l) ]
  -> [ extraction_language l ]
END

VERNAC COMMAND EXTEND ActorExtractionInline CLASSIFIED AS SIDEFF
(* Custom inlining directives *)
| [ "ActorExtraction" "Inline" ne_global_list(l) ]
  -> [ extraction_inline true l ]
END

VERNAC COMMAND EXTEND ActorExtractionNoInline CLASSIFIED AS SIDEFF
| [ "ActorExtraction" "NoInline" ne_global_list(l) ]
  -> [ extraction_inline false l ]
END

VERNAC COMMAND EXTEND PrintActorExtractionInline CLASSIFIED AS QUERY
| [ "Print" "ActorExtraction" "Inline" ]
  -> [Feedback. msg_info (print_extraction_inline ()) ]
END

VERNAC COMMAND EXTEND ResetActorExtractionInline CLASSIFIED AS SIDEFF
| [ "Reset" "ActorExtraction" "Inline" ]
  -> [ reset_extraction_inline () ]
END

VERNAC COMMAND EXTEND ActorExtractionImplicit CLASSIFIED AS SIDEFF
(* Custom implicit arguments of some csts/inds/constructors *)
| [ "ActorExtraction" "Implicit" global(r) "[" actor_int_or_id_list(l) "]" ]
  -> [ extraction_implicit r l ]
END

VERNAC COMMAND EXTEND ActorExtractionBlacklist CLASSIFIED AS SIDEFF
(* Force ActorExtraction to not use some filenames *)
| [ "ActorExtraction" "Blacklist" ne_ident_list(l) ]
  -> [ extraction_blacklist l ]
END

VERNAC COMMAND EXTEND PrintActorExtractionBlacklist CLASSIFIED AS QUERY
| [ "Print" "ActorExtraction" "Blacklist" ]
  -> [ Feedback.msg_info (print_extraction_blacklist ()) ]
END

VERNAC COMMAND EXTEND ResetActorExtractionBlacklist CLASSIFIED AS SIDEFF
| [ "Reset" "ActorExtraction" "Blacklist" ]
  -> [ reset_extraction_blacklist () ]
END


(* Overriding of a Coq object by an ML one *)
VERNAC COMMAND EXTEND ActorExtractionConstant CLASSIFIED AS SIDEFF
| [ "ActorExtract" "Constant" global(x) string_list(idl) "=>" actor_mlname(y) ]
  -> [ extract_constant_inline false x idl y ]
END

VERNAC COMMAND EXTEND ActorExtractionInlinedConstant CLASSIFIED AS SIDEFF
| [ "ActorExtract" "Inlined" "Constant" global(x) "=>" actor_mlname(y) ]
  -> [ extract_constant_inline true x [] y ]
END

VERNAC COMMAND EXTEND ActorExtractionInductive CLASSIFIED AS SIDEFF
| [ "ActorExtract" "Inductive" global(x) "=>"
    actor_mlname(id) "[" actor_mlname_list(idl) "]" string_opt(o) ]
  -> [ extract_inductive x id idl o ]
END
(* Show the extraction of the current proof *)

VERNAC COMMAND EXTEND ShowExtraction CLASSIFIED AS QUERY
| [ "Show" "Extraction" ]
  -> [ show_extraction () ]
END
