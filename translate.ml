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

(** Atom translation **)

let value_type _loc comps =
	let ts = StringMap.fold (fun comp n l ->
		let args = fold_range (fun acc _ -> <:ctyp< rvalue >>::acc) [] 1 (n+1) in
		(ctyp_of_cons _loc (comp_name comp) args)::l
	) comps [] in
	<:str_item< type rvalue = [ $list:ts$ ] >>
;;

let value_repr _loc comps =
	let cases = StringMap.fold (fun comp n l ->
		let args = fold_range (fun acc i -> (pred_var_name i)::acc) [] 1 (n+1) in
		let patt = patt_of_cons _loc (comp_name comp) (List.map (lid_patt _loc) args)
		and expr = match concat_expr ~sep:"," _loc (List.map (fun a ->
			<:expr< string_of_rvalue $lid:a$ >>
		) args) with
		| None -> <:expr< $str:comp$ >>
		| Some e -> <:expr< $str:comp ^ "("$ ^ $e$ ^ ")" >>
		in
		<:match_case< $patt$ -> $expr$ >> ::l
	) comps [] in
	<:str_item< value rec string_of_rvalue = fun [ $list:cases$ ] >>
;;

let found_exception _loc =
	<:str_item< exception $uid:found_name$ >>
;;

(** Env management **)

let empty = StringMap.empty ;;

let rec bound map = function
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
	| Comp (cn,ts,_), Comp (cn',ts',_) ->
		if cn = cn' && List.length ts = List.length ts' then
			List.fold_left (unify _loc) (env,c,tep,tst,a) (List.combine ts ts')
		else env, c, tep, tst, true
	| Var (v,_locv), Var (v',_) ->
		(match (binding env v, binding env v') with
		| Some id, Some id' -> env, c, tep, (id,id')::tst, a
		| Some id, None -> StringMap.add v' id env, c, tep, tst, a
		| None, Some id -> StringMap.add v id env, c, tep, tst, a
		| None, None -> raise (OpenUnify _loc))
	| Anon _, _ | _, Anon _ -> env, c, tep, tst, a
	| Var (v,_locv), Comp (cn,ts,_locc) | Comp (cn,ts,_locc), Var (v,_locv) ->
		match binding env v with
		| Some id ->
			let env,c,tst,tp = patt_of_comp env c tst cn ts _locc in
			env, c, (lid_expr _locv id,tp)::tep, tst, a
		| None ->
		(try
			let te = goal_out_comp env cn ts _locc in
			let id = pred_var_name c and c = c + 1 in
			(StringMap.add v id env), c, (te,lid_patt _loc id)::tep, tst, a
		with UnboundVar _ -> raise (OpenUnify _loc))
;;

(** Visit goals of a rule **)
let goal (env,c,f) pos ((n,_),ts,_loc) =
	let v = version_reconstruct (List.rev_map (fun t -> not (bound env t)) ts) in
	let call = lid_expr _loc (pred_name n v) in
	let c,ev = extend_version c (version_neg v) in
	let ins = goal_ins _loc ev and t1,t2 = recombine_terms ts ev in
	let env, c, tst =
		let env', c', tst' = terms _loc env c t1 in
		if pos then env', c', tst' else env, c, tst'
	in
	let outs =
		try goal_outs env t2
		(* we select a version with only bound vars *)
		with UnboundVar _ -> assert false
	in begin
		(match tst with
		| Maybe (_,_,_) ->
			warning _loc "will unify after satisfying goal, might not match Prolog semantics"
		| _ -> ());
		env, c,
		if pos then (fun body -> f (wrap _loc call ins outs tst body))
		else
			let nbody = wrap _loc call ins outs tst <:expr< raise $uid:found_name$ >> in
			(fun body -> f (safe_catch _loc nbody body found_name))
	end
;;	

let same_goal _loc (env,c,f) pos t t' =
	let env, c, tst =
		let env', c', tep', tst', a' = unify _loc (env,c,[],[],false) (t,t') in
		let tst' = expand_tests _loc tep' tst' a' in
		if pos then env', c', tst' else env, c, tst'
	in
	env, c,
		if pos then (fun body -> f (apply_test _loc tst body <:expr< () >>))
		else (fun body -> f (apply_test _loc tst <:expr< () >> body))
;;

let egoal acc = function
	| Pos (g,_loc) -> goal acc true g
	| Neg (g,_loc) -> goal acc false g
	| Same (t,t',_loc) -> same_goal _loc acc true t t'
	| Diff (t,t',_loc) -> same_goal _loc acc false t t'
;;

(** Visit rules of a predicate version **)
let rule ev c ((ts,egoals,_loc):'a rule) =
	let t1,t2 = recombine_terms ts ev in
	let env,c,tst = terms _loc empty c t1 in
	let env,c,f = List.fold_left egoal (env,c,(fun body -> body)) egoals in
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
	let body = <:expr< do { $list:rs$ } >> in
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
	[value_type _loc statics; value_repr _loc statics; found_exception _loc]
;;

let prog_rules _loc (prog : 'a prog) =
	let defs = PredMap.fold (fun p (rs,ms) acc ->
		List.append (pred _loc p (List.rev rs) (List.rev ms)) acc
	) prog [] in
	[ <:str_item< value rec $list:defs$ >> ]
;;
