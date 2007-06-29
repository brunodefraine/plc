open Ast ;;
open Mlgen ;;
open Camlp4.PreCast ;;

(** General aux functions **)

let string_init n f =
	let s = String.create n in
	begin
		for i = 0 to n-1 do
			s.[i] <- f i
		done;
		s
	end
;;

let rec fold_range f accu l u =
	if l < u then let u = u - 1 in fold_range f (f accu u) l u else accu
;;

(** Open/closed versions **)

type version = int * int ;;

let versions_fold f acc k =
	let n = 1 lsl k in
	let rec aux acc i =
		if i = n then acc else aux (f acc (i,k)) (i+1)
	in
	aux acc 0
;;

let version_opened (i,k) j =
	(i lsr j) land 1 = 1
;;

let version_reconstruct bs =
	List.fold_left (fun (o,k) b ->
		(let o = o lsl 1 in if b then o + 1 else o), k+1
	) (0,0) bs
;;

let version_fold f acc (i,k) =
	let rec aux acc j =
		if j = k then acc else aux (f acc (version_opened (i,k) j)) (j+1)
	in
	aux acc 0
;;

let version_string (i,k) =
	string_init k (fun j -> if version_opened (i,k) j then 'o' else 'c')
;;

let version_neg (i,k) =
	(1 lsl k) - 1 - i, k
;;

(** Open/closed versions and argument masks **)

let arg_decl_allows a o = match a with
	| ArgOpen _ -> o
	| ArgClosed _ -> not o
	| ArgAny _ -> true
;;

let version_matches_mask v (m,_) =
	let (m,s) = version_fold (fun (m,s) o ->
		match m with
		| a::m -> m, s && arg_decl_allows a o
		| [] -> assert false
	) (m,true) v in
	assert (m = []); s
;;

(** Name functions **)

let comp_name n = String.capitalize n ;;

let pred_name n v = n ^ "_" ^ (version_string v) ;;

let pred_var_name n = "_arg" ^ (string_of_int n) ;;

let f_name = "_f" ;;

let found_name = "Found" ;;
let notalist_name = "Not_a_list" ;;
let notanint_name = "Not_an_int" ;;
let type_name = "plval" ;;
let int_name = "Int" ;;
let cons_name = "cons" ;;
let nil_name = "nil" ;;

let list_of_name = "list_of_" ^ type_name ;;
let int_of_name = "int_of_" ^ type_name ;;
let string_of_name = "string_of_" ^ type_name ;;

(** Aux **)

let int_expr _loc i =
	<:expr< $uid:int_name$ $int:(string_of_int i)$ >>
;;

let int_patt _loc i =
	<:patt< $uid:int_name$ $int:(string_of_int i)$ >>
;;

(** Atom/statics translation **)

let excep_decl _loc n =
	<:str_item< exception $uid:n$ >>
;;

let value_type _loc comps =
	let ts = StringMap.fold (fun comp n l ->
		let args = fold_range (fun acc _ -> <:ctyp< $lid:type_name$ >>::acc) [] 1 (n+1) in
		(ctyp_of_cons _loc (comp_name comp) args)::l
	) comps [ <:ctyp< $uid:int_name$ of int >> ] in
	<:str_item< type $lid:type_name$ = [ $list:ts$ ] >>
;;

let list_repr _loc = <:str_item<
value rec $lid:list_of_name$ = fun
	[ $uid:comp_name nil_name$ -> []
	| $uid:comp_name cons_name$ a b -> [ a :: $lid:list_of_name$ b ]
	| _ -> raise $uid:notalist_name$ ]
>> ;;

let int_repr _loc = <:str_item<
value $lid:int_of_name$ = fun
	[ $uid:int_name$ i -> i
	| _ -> raise $uid:notanint_name$ ]
>> ;;

let value_repr _loc comps =
	let cases = StringMap.fold (fun comp n l ->
		let args = fold_range (fun acc i -> (pred_var_name i)::acc) [] 1 (n+1) in
		let patt = patt_of_cons _loc (comp_name comp) (List.map (lid_patt _loc) args)
		and expr = match concat_expr ~sep:"," _loc (List.map (fun a ->
			<:expr< $lid:string_of_name$ $lid:a$ >>
		) args) with
		| None -> <:expr< $str:comp$ >>
		| Some e -> <:expr< $str:comp ^ "("$ ^ $e$ ^ ")" >>
		in
		<:match_case< $patt$ -> $expr$ >> ::l
	) comps [ <:match_case< $uid:int_name$ i -> string_of_int i >> ] in
	<:str_item< value rec $lid:string_of_name$ v =
	try
		"[" ^ String.concat "," (List.map $lid:string_of_name$ ($lid:list_of_name$ v)) ^ "]"
	with [ $uid:notalist_name$ -> match v with [ $list:cases$ ] ] >>
;;

(** Env management **)

let empty = StringMap.empty ;;

let rec bound map = function
	| Integer (_,_) -> true
	| Var (v,_loc) -> StringMap.mem v map
	| Comp (_,ts,_) -> List.for_all (bound map) ts
	| Anon _loc -> false
;;

let lookup map v =
	StringMap.find v map
;;

let binding map v =
	try
		Some (lookup map v)
	with Not_found -> None
;;

let bind_or_test map tsts v id =
	try
		let id' = lookup map v in
		map, (id,id')::tsts
	with Not_found -> StringMap.add v id map, tsts
;;

(**
	Rules translation:
	pred -> pred_version -> rule (-> terms) -> goal -> terms
**)

(** Decorate a version with identifiers for the closed arguments **)
let extend_version c v =
	let c,ev = version_fold (fun (c,ev) o ->
		if not o then c+1, (Some (pred_var_name c))::ev else c, None::ev
	) (c,[]) v
	in c,List.rev ev
;;

(** Split terms according to closed (by id) and open **)
let recombine_terms ts ev =
	let t1,t2 = List.fold_left (fun (t1,t2) -> function
		| (t,Some id) -> (t,id)::t1,t2
		| (t,None) -> t1,t::t2
	) ([],[]) (List.combine ts ev) in
	List.rev t1, List.rev t2
;;

(** Prepare patterns from extended version (identifiers) **)
let goal_ins _loc ev = List.rev (List.fold_left (fun acc -> function
	| Some id -> (lid_patt _loc id)::acc
	| None -> acc
) [] ev) ;;

exception UnboundVar of string * Loc.t;;

(** Prepare exprs from open terms **)
let rec goal_out_comp env c ts _loc =
	expr_of_cons _loc (comp_name c) (goal_outs env ts)
and goal_out env = function
	| Integer (i, _loc) -> int_expr _loc i
	| Comp (c, ts, _loc) -> goal_out_comp env c ts _loc
	| Var (v, _loc) ->
		(try lid_expr _loc (lookup env v)
		with Not_found -> raise (UnboundVar (v,_loc)))
	| Anon _loc -> raise (UnboundVar ("_",_loc))
and	goal_outs env t2 = List.map (goal_out env) t2 ;;

(** Create patterns from a list of terms, meanwhile update env,c,t **)
let rec patt_of_comp env c t cn ts _loc =
	let env,c,t,in_p = patts_of_ts env c t ts in
	env, c, t, (patt_of_cons _loc (comp_name cn) in_p)	 
and patt_of_t env c t = function
	| Integer (i,_loc) -> env, c, t, int_patt _loc i
	| Comp (cn,ts,_loc) -> patt_of_comp env c t cn ts _loc
	| Var (v,_loc) ->
		let id = pred_var_name c and c = c + 1 in
		let env,t = bind_or_test env t v id in
		env, c, t, (lid_patt _loc id)
	| Anon _loc -> env, c, t, <:patt< _ >>
and patts_of_ts env c t ts =
	let env,c,t,p = List.fold_left (fun (env,c,t,p) term ->
		let env,c,t,patt = patt_of_t env c t term in
		env,c,t,(patt::p)
	) (env,c,t,[]) ts in
	env, c, t, List.rev p
;;

(** Visit terms of a goal, update env and tests **)
let terms _loc env c t1 =
	let env,c,ep,t = List.fold_left (fun (env,c,ep,t) -> function
		| Integer (i, _loc), id ->
			env, c, (lid_expr _loc id, int_patt _loc i)::ep, t
		| Comp (cn, ts, _loc), id ->
			let env,c,t,in_p = patts_of_ts env c t ts in
			env, c, (lid_expr _loc id, patt_of_cons _loc (comp_name cn) in_p)::ep, t
		| Var (v, _loc), id ->
			let env,t = bind_or_test env t v id in
			env, c, ep, t
		| Anon _loc, _ -> env, c, ep, t
	) (env,c,[],[]) t1 in
	env, c, expand_tests _loc ep t false
;;

exception OpenUnify of Loc.t;;

let rec unify _loc (env,c,tep,tst,a) = function
	| Integer (i,_), Integer (i',_) ->
		if i = i' then env, c, tep, tst, a
		else env, c, tep, tst, true
	| Comp (cn,ts,_), Comp (cn',ts',_) ->
		if cn = cn' && List.length ts = List.length ts' then
			List.fold_left (fun (env,c,tep,tst,a) ->
				Loc.raise _loc (Failure "Deep compound-to-compound unification unsupported")
				(* unify _loc (env,c,tep,tst,a) *)
			) (env,c,tep,tst,a) (List.combine ts ts')
		else env, c, tep, tst, true
	| Integer (_,_), Comp (_,_,_) | Comp (_,_,_), Integer (_,_) ->
		env, c, tep, tst, true
	| Var (v,_locv), Var (v',_) ->
		(match (binding env v, binding env v') with
		| Some id, Some id' -> env, c, tep, (id,id')::tst, a
		| Some id, None -> StringMap.add v' id env, c, tep, tst, a
		| None, Some id -> StringMap.add v id env, c, tep, tst, a
		| None, None -> raise (OpenUnify _loc))
	| Anon _, _ | _, Anon _ -> env, c, tep, tst, a
	| Var (v,_locv), Integer (i,_loci) | Integer (i,_loci), Var (v,_locv) ->
		(match binding env v with
		| Some id -> env, c, (lid_expr _locv id, int_patt _loci i)::tep, tst, a
		| None ->
			let te = int_expr _loci i in
			let id = pred_var_name c and c = c + 1 in
			(StringMap.add v id env), c, (te,lid_patt _locv id)::tep, tst, a)
	| Var (v,_locv), Comp (cn,ts,_locc) | Comp (cn,ts,_locc), Var (v,_locv) ->
		(match binding env v with
		| Some id ->
			let env,c,tst,tp = patt_of_comp env c tst cn ts _locc in
			env, c, (lid_expr _locv id,tp)::tep, tst, a
		| None ->
		(try
			let te = goal_out_comp env cn ts _locc in
			let id = pred_var_name c and c = c + 1 in
			(StringMap.add v id env), c, (te,lid_patt _locv id)::tep, tst, a
		with UnboundVar _ -> raise (OpenUnify _loc)))
;;

(** Visit goals of a rule **)
let pred_goal _loc (env,c,f) n ts =
	let v = version_reconstruct (List.rev_map (fun t -> not (bound env t)) ts) in
	let call = lid_expr _loc (pred_name n v) in
	let c,ev = extend_version c (version_neg v) in
	let ins = goal_ins _loc ev and t1,t2 = recombine_terms ts ev in
	let env, c, tst = terms _loc env c t1 in
	let outs =
		try goal_outs env t2
		(* we select a version with only bound vars *)
		with UnboundVar _ -> assert false
	in begin
		(match tst with
		| Maybe (_,_,_) ->
			warning _loc "will unify after satisfying goal, might not match Prolog semantics"
		| _ -> ());
		env, c, (fun body -> f (wrap _loc call ins outs tst body))
	end
;;	

let same_goal _loc (env,c,f) pos t t' =
	let env, 	c, tst =
		let env', c', tep', tst', a' = unify _loc (env,c,[],[],false) (t,t') in
		let tst' = expand_tests _loc tep' tst' a' in
		if pos then env', c', tst' else env, c, tst'
	in
	env, c,
		if pos then (fun body -> f (apply_test _loc tst body <:expr< () >>))
		else (fun body -> f (apply_test _loc tst <:expr< () >> body))
;;

let rec int_expr_of_term env = function
	| Integer (i,_loc) -> <:expr< $int:string_of_int i$ >>
	| Comp ("add",[e1;e2],_loc) ->
		let e1 = int_expr_of_term env e1 and e2 = int_expr_of_term env e2 in
		<:expr< $e1$ + $e2$ >>
	| Comp ("sub",[e1;e2],_loc) ->
		let e1 = int_expr_of_term env e1 and e2 = int_expr_of_term env e2 in
		<:expr< $e1$ - $e2$ >>
	| Comp (n,_,_loc) -> Loc.raise _loc (Failure ("Function " ^ n ^ " not supported"))
	| Anon _loc -> raise (UnboundVar ("_",_loc))
	| Var (v,_loc) ->
		try
			let id = lookup env v in
			<:expr< $lid:int_of_name$ $lid_expr _loc id$ >>
		with Not_found -> raise (UnboundVar (v,_loc))
;;

let relation_goal _loc (env,c,f) r t1 t2 =
	let e1 = int_expr_of_term env t1 and e2 = int_expr_of_term env t2 in
	let tst = <:expr< $lid:r$ $e1$ $e2$ >> in
	env, c, (fun body -> f <:expr< if $tst$ then $body$ else () >>)
;;

let is_goal _loc (env,c,f) t t' =
	let e = <:expr< $uid:int_name$ $int_expr_of_term env t'$ >> in
	let (env, c, tst, p) = patt_of_t env c [] t in
	let tst = expand_tests _loc [(e,p)] tst false in
	env, c, (fun body -> f (apply_test _loc tst body <:expr< () >>))
;;

let rec goal acc = function
	| Integer (_,_loc) -> Loc.raise _loc (Failure ("Integer not callable"))
	| Var (_,_loc) | Anon _loc ->
		Loc.raise _loc (Failure ("Meta-call not supported"))
	| Comp ("same",[t;t'],_loc) -> same_goal _loc acc true t t'
	| Comp ("diff",[t;t'],_loc) -> same_goal _loc acc false t t'
	| Comp ("is",[t;t'],_loc) -> is_goal _loc acc t t'
	| Comp ("eq",[t;t'],_loc) -> relation_goal _loc acc "=" t t'
	| Comp ("ne",[t;t'],_loc) -> relation_goal _loc acc "<>" t t'
	| Comp ("lt",[t;t'],_loc) -> relation_goal _loc acc "<" t t'
	| Comp ("lte",[t;t'],_loc) -> relation_goal _loc acc "<=" t t'
	| Comp ("gt",[t;t'],_loc) -> relation_goal _loc acc ">" t t'
	| Comp ("gte",[t;t'],_loc) -> relation_goal _loc acc ">=" t t'
	| Comp ("not",[t],_loc) -> not_goal _loc acc t
	| Comp (n,ts,_loc) -> pred_goal _loc acc n ts
and not_goal _loc (env,c,f) g =
	let (_,_,notf) = goal (env,c,(fun body -> body)) g in
	let nbody = notf <:expr< raise $uid:found_name$ >> in
	env, c, (fun body -> safe_catch _loc nbody body found_name)
;;

(** Visit rules of a predicate version **)
let rule ev c ((ts,goals,_loc):'a rule) =
	let t1,t2 = recombine_terms ts ev in
	let env,c,tst = terms _loc empty c t1 in
	let env,c,f = List.fold_left goal (env,c,(fun body -> body)) goals in
	let outs = goal_outs env t2 in
	let body = fun_apply _loc (lid_expr _loc f_name) outs in
	let body = f body in
	apply_test _loc tst body <:expr< () >>
;;

(** Visit a predicate to produce a certain version **)
let pred_version _loc n rs v =
	let name = lid_patt _loc (pred_name n v) in
	let c,ev = extend_version 0 v in
	let args = goal_ins _loc ev in
	let rs = List.map (rule ev c) rs in
	let body = sequence _loc rs in
	let f = fun_args _loc ((lid_patt _loc f_name)::args) body in
	<:binding< $name$ = $f$ >>
;;

(** Visit a predicate to produce all possible versions **)
let pred _loc (name,n) rs ms = versions_fold (fun a v ->
	if ms = [] || List.exists (version_matches_mask v) ms then
		let fname = pred_name name v in
		try (pred_version _loc name rs v)::a with
		| UnboundVar(var,_loc) ->
			warning _loc (Printf.sprintf "skipping %s, unbound %s" fname var);
			a
		| OpenUnify(_loc) ->
			warning _loc (Printf.sprintf "skipping %s, open unification" fname);
			a
	else a
) [] n ;;

(** Starters **)

let prog_statics _loc (prog : 'a prog) =
	let statics = statics prog in
	let statics = StringMap.add nil_name 0 statics in
	let statics = StringMap.add cons_name 2 statics in
	[value_type _loc statics;
	excep_decl _loc notalist_name;
	list_repr _loc;
	value_repr _loc statics;
	excep_decl _loc notanint_name;
	int_repr _loc;
	excep_decl _loc found_name]
;;

let prog_rules _loc (prog : 'a prog) =
	let defs = PredMap.fold (fun p (rs,ms) acc ->
		List.append (pred _loc p (List.rev rs) (List.rev ms)) acc
	) prog [] in
	[ <:str_item< value rec $list:defs$ >> ]
;;
