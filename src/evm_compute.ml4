
let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)
let pp_list pp fmt l = List.iter (fun x -> Format.fprintf fmt "%a; " pp x) l
let pp_list_nl pp fmt l = List.iter (fun x -> Format.fprintf fmt "%a;\n" pp x) l
let pp_constrs fmt l = (pp_list pp_constr) fmt l

type constr = Term.constr

module Replace (X : sig val eq: Term.constr -> Term.constr -> bool 
			val subst : (Term.constr * Term.constr) list end) =
  struct

    (* assumes that [c] and [t] have no outer casts, and all
       applications have been flattened *)    
    let rec find l (t: constr) =
      match l with 
      | [] -> None
      | (c,c') :: q -> 
	begin 
	  match Term.kind_of_term c, Term.kind_of_term t with 
	  | Term.App (f1,args1), Term.App (f2, args2) -> 
	    let l1 = Array.length args1 in 
	    let l2 = Array.length args2 in 
	    if l1 <= l2 && X.eq c (Term.mkApp (f2, Array.sub args2 0 l1)) 
	    then
	      (* we must return the array of arguments, to make the
		 substitution in them too *)
	      Some (c',Array.sub args2 l1 (l2 - l1))
	    else 
	      find q t
	  | _, _ -> 
	    if X.eq c t 
	    then Some (c', [| |]) 
	    else find q t	      
	end
	  
	  
    let replace_terms t = 
      let rec aux (k:int) t =
	match find X.subst t with 
	| Some (t',v) -> 
	  let v' = Array.map (Term.map_constr_with_binders (succ) aux k) v in
	  Term.mkApp (Term.lift k t', v')
	| None -> 
	  Term.map_constr_with_binders succ aux k t
      in aux 0 t
	  
  end

let nowhere =
  { Tacexpr.onhyps = Some [];
    Tacexpr.concl_occs = Glob_term.no_occurrences_expr
  }

let mk_letin
    (name:string)
    (c: constr)
    (k : Names .identifier -> Proof_type.tactic)
: Proof_type.tactic =
  fun goal ->
    let name = (Names.id_of_string name) in
    let name =  Tactics.fresh_id [] name goal in
    let letin = (Tactics.letin_tac None  (Names.Name name) c None nowhere) in
      Tacticals.tclTHEN letin (k name) goal

let assert_tac
    (name:string)
    (c: constr)
    (k : Names.identifier -> Proof_type.tactic)
: Proof_type.tactic =
  fun goal ->
    let name = (Names.id_of_string name) in
    let name =  Tactics.fresh_id [] name goal in
    let t = (Tactics.assert_tac  (Names.Name name) c) in
      Tacticals.tclTHENS t [Tacticals.tclIDTAC; (k name)] goal


(* The contrib name is used to locate errors when loading constrs *)
let contrib_name = "evm_compute"

(* Getting constrs (primitive Coq terms) from existing Coq
   libraries. *)
let find_constant contrib dir s =
  Libnames.constr_of_global (Coqlib.find_reference contrib dir s)

let init_constant dir s = find_constant contrib_name dir s

module Leibniz = struct
  let path = ["Coq"; "Init"; "Logic"]
    
  let eq_refl t x= 
    Term.mkApp (init_constant path "eq_refl", [| t; x|])

  let eq t x y = 
    Term.mkApp (init_constant path "eq", [| t; x ; y|])
      
  let eq_ind_r ty x p px y yx =
    Term.mkApp (init_constant path "eq_ind_r", [|ty;x;p;px;y;yx|])
end

let mk_vm_cast t c = Term.mkCast (c,Term.VMcast,t)

let mk_let  
    (name:Names.identifier)
    (c: constr)
    (t: constr)
    (k : Names.identifier -> constr) =
  Term.mkNamedLetIn name c t (Term.subst_vars [name] (k name))

let mk_fun
    (name:Names.identifier)
    (t: constr)
    (k : Names.identifier -> constr) =
  Term.mkNamedLambda name t (Term.subst_vars [name] (k name))

let rec has_evar x =
  match Term.kind_of_term x with
    | Term.Evar _ -> true
    | Term.Rel _ | Term.Var _ | Term.Meta _ | Term.Sort _ | Term.Const _ | Term.Ind _ | Term.Construct _ ->
      false
    | Term.Cast (t1, _, t2) | Term.Prod (_, t1, t2) | Term.Lambda (_, t1, t2) ->
      has_evar t1 || has_evar t2
    | Term.LetIn (_, t1, t2, t3) ->
      has_evar t1 || has_evar t2 || has_evar t3
    | Term.App (t1, ts) ->
      has_evar t1 || has_evar_array ts
    | Term.Case (_, t1, t2, ts) ->
      has_evar t1 || has_evar t2 || has_evar_array ts
    | Term.Fix ((_, tr)) | Term.CoFix ((_, tr)) ->
      has_evar_prec tr
and has_evar_array x =
  Util.array_exists has_evar x
and has_evar_prec (_, ts1, ts2) =
  Util.array_exists has_evar ts1 || Util.array_exists has_evar ts2


let evm_compute eq blacklist = fun gl -> 
  (* the type of the conclusion of the goal is [concl] *)
  let concl = Tacmach.pf_concl gl in 

  let extra = 
    List.fold_left (fun acc (id,body,ty) -> 
      match body with 
	| None -> acc
	| Some body -> if has_evar body then (Term.mkVar id :: acc) else acc)
      [] (Tacmach.pf_hyps gl) in 

  (* the set of evars that appear in the goal *)
  let evars = Evd.evar_list (Tacmach.project gl) concl in 
  
  (* the arguments of the function are: the constr that are blacklisted, then the evars  *)
  let args = extra @ blacklist @ (List.map (fun x -> Term.mkEvar x) evars) in 
  
  let argsv = Array.of_list args in 

  let context = (Termops.rel_list 0 (List.length args)) in 

  (* we associate to each argument the proper de bruijn index *)
  let (subst: (Term.constr * Term.constr) list) = List.combine args context in 
  
  let module R = Replace(struct let eq = eq let subst = subst end) in 
  
  let t = R.replace_terms concl in 
  
  (* we have to retype both the blacklist and the evars to know how to build the final product *)
  let rel_context = List.map (fun x -> Names.Anonymous, None, Tacmach.pf_type_of gl x) args in 
  
  (* the abstraction *)
  let t = Term.it_mkLambda_or_LetIn t (List.rev rel_context) in 
  
  let typeof_t = (Tacmach.pf_type_of gl t) in 

  (* the normal form of the head function *)
  let nft = Vnorm.cbv_vm (Tacmach.pf_env gl) t typeof_t in 
  

  let (!!) x = Tactics.fresh_id [] ((Names.id_of_string x)) gl in

  (* p = [fun x => x a_i] which corresponds to the type of the goal when applied to [t] *)
  let p = mk_fun (!! "x") typeof_t (fun x -> Term.mkApp (Term.mkVar x,argsv)) in 
  
  let proof_term pnft = begin  
    mk_let (!! "nft") nft typeof_t (fun nft -> let nft' = Term.mkVar nft in
    mk_let (!! "t") t typeof_t (fun t -> let t' = Term.mkVar t in 	
    mk_let (!! "H") (mk_vm_cast (Leibniz.eq typeof_t t' nft') (Leibniz.eq_refl typeof_t nft')) (Leibniz.eq typeof_t t' nft')
   (fun h -> 
    (* typeof_t -> Prop *)
    let body = Leibniz.eq_ind_r typeof_t 
      nft' p pnft t' (Term.mkVar h) 
    in 
    Term.mkCast (body, Term.DEFAULTcast, Term.mkApp (t', argsv))
  )))
  end in 
  
  try 
    assert_tac "subgoal" (Term.mkApp (p,[| nft |]))
      (fun subgoal -> 
	(* We use the tactic [exact_no_check]. It has two consequences:
	- first, it means that in theory we could produce ill typed proof terms, that fail to type check at Qed; 
	- second, it means that we are able to use vm_compute and vm_compute casts, that will be checkable at Qed time when all evars have been instantiated. 
	*)
	Tactics.exact_no_check (proof_term (Term.mkVar subgoal))  
      ) gl
  with 
    | e ->
      Tacticals.tclFAIL 0 (Pp.str (Printf.sprintf "evm_compute failed with an exception %s" (Printexc.to_string e))) gl
      
;;


open Tacmach
open Tacticals
open Tacexpr
open Tacinterp
open Genarg

let pr_constr_list _ _ _ l = Pp.str "<constr list>"
  
type constr_list = Term.constr list

ARGUMENT EXTEND constrlist  
TYPED AS (constr_list) 
PRINTED BY pr_constr_list
| [ constr(t) ] -> [[t]]
| [ constr(t) ";" constrlist(q) ] -> [t::q]
| [ ] -> [ [] ]
END



TACTIC EXTEND evm1
  | ["evm"] ->     [evm_compute Term.eq_constr []]      
END;;


TACTIC EXTEND exploit
  | ["evm" "blacklist"  "[" constrlist(l) "]"] ->     [evm_compute Term.eq_constr l] 
END;;

