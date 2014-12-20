open Pp
open Names
open Nameops
open Util
open Miniml
open Actor_mlutil
open Actor_common

(* Erlang AST *)

type erl_var = MkVar of identifier           (* 大文字始まり *)
type erl_atom = MkAtom of string         (* アトム (identifier じゃなくて string のほうがいいかも) *)

type erl_expr =
  | ErlSeq of erl_expr * erl_expr (* ..., ... *)
  | ErlBind of erl_var * erl_expr (* Var = ... *)
  | ErlLam of erl_var list * erl_expr (* fun(A, B, ...) -> ... end *)
  | ErlApp of erl_expr * erl_expr list (* 'f'(A), F(A, B, C), (fun X -> X)(A) など *)
  | ErlOp of erl_atom * erl_expr * erl_expr       (* A + B など *)
  | ErlCase of erl_expr * erl_branch list (* case ... of ... -> ...; ... -> ... end *)
  | ErlReceive of erl_branch list        (* receive ... -> ...; ... -> ... end *)
  | ErlThrow of erl_expr                 (* throw(e) *)
  | ErlTuple of erl_expr list             (* {a, b, c} *)
  | ErlList of erl_expr list              (* [a, b, c] *)
  | ErlListCons of erl_expr * erl_expr    (* [a | b] *)
  | ErlVar of erl_var     (*  *)
  | ErlAtom of erl_atom   (* 'atom', 関数名も''でつつんでいいっぽい *)
  | ErlFunName of erl_atom      (* ゼロ引数関数とアトムを区別するために定義 *)
  | ErlString of string   (* "str" *)

and erl_branch = erl_expr * erl_expr

(* トップレベルパターンマッチはしない *)
type erl_decl = ErlFun of erl_atom * erl_var list * erl_expr

(* for debugging *)

let debug s = str ("[debug:" ^ s ^ "]") ++ fnl ()

(* Pretty Printers for Erlang AST *)

let pp_erl_var = function
  | MkVar id -> str (String.capitalize (string_of_id id))
let pp_erl_atom = function
  | MkAtom s -> str (String.uncapitalize s) (* 最初の文字が小文字で、かつスペースや記号が入ってなかったら''でつつまないようにしたい *)

let pp_erl_args f args =
  pp_par true (prlist_with_sep (fun () -> str ", ") f args)

let rec pp_erl_expr = function
  | ErlSeq (e1, e2) -> pp_erl_expr e1 ++ str "," ++ fnl () ++ pp_erl_expr e2
  | ErlBind (var, e) -> pp_erl_var var ++ str " = " ++ pp_erl_expr e
  | ErlLam (args, body) ->
     str "fun" ++ pp_erl_args pp_erl_var args ++ str " ->" ++ fnl () ++
       str "    " ++ hov 0 (pp_erl_expr body) ++ fnl () ++
       str "end"
  | ErlApp (f, args) ->
     let non_fun = match f with
       | ErlFunName _ -> false
       | _ -> true
     in
     pp_par non_fun (pp_erl_expr f) ++ pp_erl_args pp_erl_expr args
  | ErlOp (op, arg1, arg2) ->
     pp_erl_expr arg1 ++ str " " ++ pp_erl_atom op ++ str " " ++ pp_erl_expr arg2
  | ErlCase (e, bs) ->
     str "case " ++ pp_erl_expr e ++ str " of" ++ fnl () ++
       str "    " ++ hov 0 (prlist_with_sep (fun () -> str ";" ++ fnl ()) pp_erl_branch bs) ++ fnl () ++
       str "end"
  | ErlReceive bs ->
     str "receive" ++ fnl () ++
       str "    " ++ hov 0 (prlist_with_sep (fun () -> str ";" ++ fnl ()) pp_erl_branch bs) ++ fnl () ++
       str "end"
  | ErlThrow e -> str "throw(" ++ pp_erl_expr e ++ str ")"
  | ErlTuple es -> str "{" ++ prlist_with_sep (fun () -> str ", ") pp_erl_expr es ++ str "}"
  | ErlList es -> str "[" ++ prlist_with_sep (fun () -> str ", ") pp_erl_expr es ++ str "]"
  | ErlListCons (h, t) -> str "[ " ++ pp_erl_expr h ++ str " | " ++ pp_erl_expr t ++ str " ]"
  | ErlVar v -> pp_erl_var v
  | ErlAtom a -> pp_erl_atom a
  | ErlFunName n -> pp_erl_atom n
  | ErlString s -> str "\"" ++ str s ++ str "\""

and pp_erl_branch (pat, body) =
  pp_erl_expr pat ++ str " ->" ++ fnl () ++
    str "    " ++ hov 0 (pp_erl_expr body)

let pp_erl_decl = function
  | ErlFun (fname, args, body) ->
     pp_erl_atom fname ++ pp_erl_args pp_erl_var args ++ str " -> " ++ fnl () ++
       str "    " ++ hov 0 (pp_erl_expr body) ++ str "." ++ fnl2 ()

(* AST Converters *)

let array_zip xs ys = array_map2 (fun x y -> x, y) xs ys
let map_id args = List.map id_of_mlid args

let keywords =
  List.fold_right
    (fun s -> Idset.add (id_of_string s))
    [ "module"; "export";
      "fun"; "end"; "if"; "case"; "of"; "when";
      "receive"; "after"; "try"; "catch" ]
    Idset.empty

(* pp_pattern : env -> int -> erl_expr *)
(* num は変数の数 *)
let rec conv_pattern env num = function
  | Pcons (r, pats) ->
     let c = ErlAtom (MkAtom (pp_global Cons r)) in
     let es = List.map (conv_pattern env num) pats in
     ErlTuple (c :: es)
  | Ptuple pats -> ErlTuple (List.map (conv_pattern env num) pats)
  | Prel n -> ErlVar (MkVar (get_db_name n env))
  | Pwild -> ErlAtom (MkAtom "_")
  | Pusual r -> (** Shortcut for Pcons (r,[Prel n;...;Prel 1]) **)
     let rec n_to_1 n = if n < 1 then [] else n :: n_to_1 (n - 1) in
     let pats = List.map (fun n -> Prel n) (n_to_1 num) in
     conv_pattern env num (Pcons (r, pats))

(* Special treatment for Actor primitives *)
let conv_cons es = function
  | "Receive" ->
     let lam_branch = function
       | ErlLam (args, body) -> (ErlVar (List.hd args), body)
       | _ -> assert false
     in
     ErlReceive (List.map lam_branch es)
  (* new behv (fun x => body) => X = spawn(fun () -> behv() end), body *)
  | "New" ->
     begin
       match List.nth es 1 with
       | ErlLam (args, body) ->
          ErlSeq (ErlBind (List.hd args,
                           ErlApp (ErlFunName (MkAtom "spawn"),
                                   [ErlLam ([], List.hd es)])),
                  body)
       | _ -> assert false
     end
  | "Send" -> ErlSeq (ErlOp (MkAtom "!", List.hd es, List.nth es 1), List.nth es 2)
  (* become (behavior arg1 arg2) => behavior(arg1, arg2) *)
  | "Become" -> List.hd es
  (* self (fun me => body) => Me = self(), body *)
  | "Self" ->
     begin
       match List.hd es with
       | ErlLam (args, body) ->
          ErlSeq (ErlBind (List.hd args,
                           ErlApp (ErlFunName (MkAtom "self"), [])),
                  body)
       | _ -> assert false
     end
  | cstr -> ErlTuple (ErlAtom (MkAtom cstr) :: es)

(* pp_branch : env -> ml_branch -> erl_branch *)
let rec conv_branch env = function
  | (ids, pat, a) ->
     let ids', env = push_vars (List.rev (map_id ids)) env in
     (conv_pattern env (List.length ids) pat, conv_expr true env a)

(* pp_fix : env -> identifier array -> ml_ast array -> std_ppcmds *)
(* https://twitter.com/ajiyoshi/status/544349185525297152 *)
(* Erlang は関数本体の中で再帰関数を書けないので、Yコンビネータっぽいことをする。 *)
(* example:
 *
 * let rec f a = f (g a) and g a = f a in ... (この例は停止しないけど)
 *
 * =>
 *
 * F_fix = fun(F_fresh, G_fresh, A) -> F_fresh(F_fresh, G_fresh, G_fresh(F_fresh, G_fresh, A)) end,
 * G_fix = fun(F_fresh, G_fresh, A) -> F_fresh(F_fresh, G_fresh, A) end,
 * F = fun(A) -> F_fix(F_fix, G_fix, A) end,
 * G = fun(A) -> G_fix(F_fix, G_fix, A) end,
 * ...
 *)
and conv_list_seq = function
  | [] -> failwith "conv_list_seq: unexpected arguments"
  | [e] -> e
  | e :: es -> ErlSeq (e, conv_list_seq es)

and conv_fix_one env ex_args fix_id def =
  let args, body = collect_lams def in
  let args', env' = push_vars (List.rev (map_id args)) env in
  let ex_args', env'' = push_vars (List.rev ex_args) env' in
  let erl_body = conv_expr true env'' body in
  ErlBind (MkVar fix_id, ErlLam (List.map (fun v -> MkVar v) (ex_args' @ args'), erl_body))

and conv_fix_two fix_ids id fix_id def =
  let args, _ = collect_lams def in
  let args = map_id args in
  ErlBind (MkVar id,
           ErlLam (List.map (fun v -> MkVar v) args,
                   ErlApp (ErlVar (MkVar fix_id),
                           List.map (fun v -> ErlVar (MkVar v)) (fix_ids @ args))))

and conv_fix env ids defs =
  let to_fix id = id_of_string ((string_of_id id) ^ "_fix") in
  let fix_ids = List.map to_fix ids in
  let zipped = List.combine fix_ids defs in
  let binds = List.map (fun (id, def) -> conv_fix_one env ids id def) zipped in
  let binds' = List.map (fun (id, def) -> conv_fix_two fix_ids id (to_fix id) def) zipped in
  conv_list_seq (binds @ binds')

(* pp_expr : bool -> env -> ml_ast -> erl_expr *)
(* 最初の引数は、関数名が出てきたらゼロ引数関数として扱うかどうか *)
(* これをするとアドホックな実装になってしまうので、ちゃんとやるとしたら MiniML を改造して、関数名に対して引数の数の情報を足したりとかしないといけないと思う *)
and conv_expr zero env = function
  | MLrel n ->                  (* 環境から de Bruijn index で入れた変数名を取り出す *)
     let id = get_db_name n env in
     (* let id = id_of_string ("REL" ^ (string_of_int n)) in *)
     ErlVar (MkVar id)           (* ここで出てくるのは変数名しかないよね？ *)
  | MLapp (f, args) ->         (* 関数適用 *)
     let f = conv_expr false env f in (* ここだけ zero = false *)
     let args = List.map (conv_expr true env) args in
     begin
       match f with
       | ErlFunName (MkAtom "init") -> List.nth args 1
       | _ -> ErlApp (f, args)
     end
  | MLlam _ as a ->             (* 無名関数 *)
     let args, a' = collect_lams a in (* fun x -> fun y -> ... -> t を fun x y ... -> t にする *)
     let args, env' = push_vars (List.rev (map_id args)) env in (* 環境に入れる *)
     let args = List.map (fun v -> MkVar v) args in
     ErlLam (args, conv_expr true env' a')
  | MLletin (id, a1, a2) ->     (* 局所束縛 *)
     let i, env' = push_vars [id_of_mlid id] env in
     let var = MkVar (List.hd i) in
     let erl_a1 = conv_expr true env a1 in
     let erl_a2 = conv_expr true env' a2 in
     ErlSeq (ErlBind (var, erl_a1), erl_a2)
  | MLglob r -> (* ??? トップレベルに定義してる名前とか？ *)
     let f = ErlFunName (MkAtom (pp_global Term r)) in
     if zero then
       ErlApp (f, [])
     else
       f
  | MLcons (_, r, asts) ->      (* MLcons (型, コンストラクタ名, 引数) だと思う、たぶん *)
     let cstr = pp_global Cons r in
     let es = List.map (conv_expr true env) asts in
     (* ここを actions と behavior のコンストラクタのときだけ別なように処理すればいい *)
     conv_cons es cstr
  | MLtuple asts ->             (* タプル *)
     let es = List.map (conv_expr true env) asts in
     ErlTuple es
  | MLcase (_, a, pats) ->      (* パターンマッチ *)
     let a = conv_expr true env a in
     let bls = List.map (conv_branch env) (Array.to_list pats) in
     ErlCase (a, bls)
  | MLfix (i, ids, defs) ->     (* 相互再帰 let rec f a = ... g ... and g a = ... g ... in ... *)
     conv_fix env (Array.to_list ids) (Array.to_list defs)
     (* pr_id ids.(i)              (\* <- ??? *\) *)
  | MLexn s ->                  (* 例外 *)
     ErlThrow (ErlString s)
  | MLdummy -> ErlAtom (MkAtom "__")         (* ??? *)
  | MLaxiom -> ErlThrow (ErlString "axiom")
  | MLmagic a -> conv_expr true env a  (* erlang に magic に対応するものってあんの *)

(* preamble : identifier -> module_path list -> unsafe_needs -> std_ppcmds *)
(* preamble で -export([Function1/Arity1,..,FunctionN/ArityN]) を出力したいが、関数名の情報は入力に含まれないので、モジュール名だけ出力する *)
(* preamble の入力に関数名と引数の数が含まれるようなものを渡すように改造したほうがいいかもしれない *)
let preamble mod_name used_modules usf =
  str "-module(" ++ str (String.uncapitalize (string_of_id mod_name)) ++ str ")." ++ fnl ()

(* haskell.ml の pp_function とほぼおなじ *)
(* pp_function : global_reference -> ml_ast -> std_ppcmds *)
let conv_function r lam =
  let fnamestr = pp_global Term r in
  (* init だけ特別扱い (抽出しない) *)
  if fnamestr = "init" then None else
    let fname = MkAtom fnamestr in
    (* collect_lams は mlutil.ml に定義されてて、
     * fun x -> fun y -> fun z -> ... -> t みたいなのを、
     * ([ x; y; z; ... ], t) にする
     *)
    let args, body = collect_lams lam in
    let args, env = push_vars (map_id args) (empty_env ()) in
    let args = List.map (fun v -> MkVar v) (List.rev args) in
    let body = conv_expr true env body in
    Some (ErlFun (fname, args, body))

let pp_decl = function
  | Dind (_, _) -> mt ()        (* Inductive は何も出力しない *)
  | Dtype (_, _, _) -> mt ()    (* Type alias は何も出力しない *)
  | Dterm (r, ast, _) ->        (* 普通の関数定義 *)
     begin
       match conv_function r ast with
       | Some d -> pp_erl_decl d
       | None -> mt ()
     end
  | Dfix (rv, defv, _) ->    (* 相互再帰 (Erlang はトップレベルは相互再帰可能なので Dterm のときと同じ) *)
     let _ = assert (Array.length rv == Array.length defv) in
     let pp = function
       | Some d -> pp_erl_decl d
       | None -> mt ()
     in
     prvect (fun (r, def) -> pp (conv_function r def)) (array_zip rv defv)

let pp_structure_elem = function
  | SEdecl d -> pp_decl d
  | SEmodule _ | SEmodtype _ -> mt ()

let pp_module_structure =
  prlist_strict (fun (_, e) -> pp_structure_elem e)

let name_arity_module el =
  let name_arity_function r lam =
    let fname = pp_global Term r in
    let args, _ = collect_lams lam in
    (fname, List.length args)
  in
  let name_arity_decl = function
    | Dterm (r, ast, _) -> [name_arity_function r ast]
    | Dfix (rv, defv, _) ->
       List.map (fun (r, def) -> name_arity_function r def)
                (Array.to_list (array_zip rv defv))
    | _ -> []
  in
  let name_arity_structure_elem = function
    | SEdecl d -> name_arity_decl d
    | _ -> []
  in
  List.flatten (List.map (fun (_, e) -> name_arity_structure_elem e) el)

(* Recursive Extraction のときに使われるっぽい *)
let pp_struct st =
  let name_arity_pairs_par_module (mp, sel) =
    push_visible mp [];
    let pairs = List.filter (fun (n, _) -> n <> "init") (name_arity_module sel) in
    pop_visible ();
    pairs
  in
  let exports = List.flatten (List.map name_arity_pairs_par_module st) in
  let pp_export =
    str "-export([" ++
      prlist_with_sep (fun () -> str ", ")
                      (fun (n, a) -> str n ++ str "/" ++ int a)
                      exports ++
      str "])."
  in
  let pp_inline =
    let arity0 = List.filter (fun (_, a) -> a == 0) exports in
    str "-compile({inline, [" ++
      prlist_with_sep (fun () -> str ", ")
                      (fun (n, a) -> str n ++ str "/" ++ int a)
                      arity0 ++
      str "]})."
  in
  let pp_sel (mp, sel) =
    push_visible mp [];
    let p = pp_module_structure sel in
    pop_visible ();
    p
  in
  pp_export ++ fnl () ++ pp_inline ++ fnl2 () ++ prlist_strict pp_sel st

let erlang_descr = {
  keywords = keywords;
  file_suffix = ".erl";
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = (fun _ _ _ -> mt ());
  pp_sig = (fun _ -> mt ());
  pp_decl = pp_decl;
}
