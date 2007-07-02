open Ast ;;
open Mlgen ;;
open Camlp4.PreCast ;;

(** General aux functions **)

let rec fold_range f accu l u =
	if l < u then let u = u - 1 in fold_range f (f accu u) l u else accu
;;

(** Open/closed versions and argument masks **)

let arg_decl_allows a o = match a with
	| ArgOpen _ -> o
	| ArgClosed _ -> not o
	| ArgAny _ -> true
;;

let version_matches_mask v (m,_) =
	let (m,s) = Version.fold (fun (m,s) o ->
		match m with
		| a::m -> m, s && arg_decl_allows a o
		| [] -> assert false
	) (m,true) v in
	assert (m = []); s
;;

(** Aux **)

let int_expr _loc i =
	<:expr< $uid:Names.int_cons$ $int:(string_of_int i)$ >>
;;

let int_patt _loc i =
	<:patt< $uid:Names.int_cons$ $int:(string_of_int i)$ >>
;;

(** Atom/statics translation **)

let comps_contains comps n i =
	try StringMap.find n comps = i
	with Not_found -> false
;;

let excep_decl _loc n =
	<:str_item< exception $uid:n$ >>
;;

let value_type _loc comps =
	let ts = StringMap.fold (fun comp n l ->
		let args = fold_range (fun acc _ -> <:ctyp< $lid:Names.val_type$ >>::acc) [] 1 (n+1) in
		(ctyp_of_cons _loc (Names.comp comp) args)::l
	) comps [ <:ctyp< $uid:Names.int_cons$ of int >> ] in
	<:str_item< type $lid:Names.val_type$ = [ $list:ts$ ] >>
;;

let list_repr _loc comps =
	let cases = [ <:match_case< _ -> raise $uid:Names.notalist_exc$ >> ] in
	let cases = if not (comps_contains comps Names.nil 0) then cases else
		<:match_case< $uid:Names.comp Names.nil$ -> [] >> :: cases in
	let cases = if not (comps_contains comps Names.cons 2) then cases else
		<:match_case< $uid:Names.comp Names.cons$ a b ->
			[ a :: $lid:Names.list_of$ b ] >> :: cases in
	<:str_item< value rec $lid:Names.list_of$ = fun [ $list:cases$ ] >>
;;

let int_repr _loc comps =	
	let cases = [ <:match_case< _ -> raise $uid:Names.notanint_exc$ >> ] in
	let cases = if not (comps_contains comps Names.sub 2) then cases else
		<:match_case< $uid:Names.comp Names.sub$ x y ->
			($lid:Names.int_of$ x) - ($lid:Names.int_of$ y) >> :: cases in
	let cases = if not (comps_contains comps Names.add 2) then cases else
		<:match_case< $uid:Names.comp Names.add$ x y ->
			($lid:Names.int_of$ x) + ($lid:Names.int_of$ y) >> :: cases in
	let cases = <:match_case< $uid:Names.int_cons$ i -> i >> :: cases in
	<:str_item< value rec $lid:Names.int_of$ = fun [ $list:cases$ ] >>
;;

let value_repr _loc comps =
	let cases = StringMap.fold (fun comp n l ->
		let args = fold_range (fun acc i -> (Names.pred_var i)::acc) [] 1 (n+1) in
		let patt = patt_of_cons _loc (Names.comp comp) (List.map (lid_patt _loc) args)
		and expr = match concat_expr ~sep:"," _loc (List.map (fun a ->
			<:expr< $lid:Names.string_of$ $lid:a$ >>
		) args) with
		| None -> <:expr< $str:comp$ >>
		| Some e -> <:expr< $str:comp ^ "("$ ^ $e$ ^ ")" >>
		in
		<:match_case< $patt$ -> $expr$ >> ::l
	) comps [ <:match_case< $uid:Names.int_cons$ i -> string_of_int i >> ] in
	<:str_item< value rec $lid:Names.string_of$ v =
	try
		"[" ^ String.concat "," (List.map $lid:Names.string_of$ ($lid:Names.list_of$ v)) ^ "]"
	with [ $uid:Names.notalist_exc$ -> match v with [ $list:cases$ ] ] >>
;;

let cut_excep_decl _loc = 
	<:str_item< exception $uid:Names.cut_exc$ of int >>
;;

let cut_id_decl _loc =
	<:str_item< value $lid:Names.cut_id$ = ref 0 >>
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
	let c,ev = Version.fold (fun (c,ev) o ->
		if not o then c+1, (Some (Names.pred_var c))::ev else c, None::ev
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
	expr_of_cons _loc (Names.comp c) (goal_outs env ts)
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
	env, c, t, (patt_of_cons _loc (Names.comp cn) in_p)	 
and patt_of_t env c t = function
	| Integer (i,_loc) -> env, c, t, int_patt _loc i
	| Comp (cn,ts,_loc) -> patt_of_comp env c t cn ts _loc
	| Var (v,_loc) ->
		let id = Names.pred_var c and c = c + 1 in
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
			env, c, (lid_expr _loc id, patt_of_cons _loc (Names.comp cn) in_p)::ep, t
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
			let id = Names.pred_var c and c = c + 1 in
			(StringMap.add v id env), c, (te,lid_patt _locv id)::tep, tst, a)
	| Var (v,_locv), Comp (cn,ts,_locc) | Comp (cn,ts,_locc), Var (v,_locv) ->
		(match binding env v with
		| Some id ->
			let env,c,tst,tp = patt_of_comp env c tst cn ts _locc in
			env, c, (lid_expr _locv id,tp)::tep, tst, a
		| None ->
		(try
			let te = goal_out_comp env cn ts _locc in
			let id = Names.pred_var c and c = c + 1 in
			(StringMap.add v id env), c, (te,lid_patt _locv id)::tep, tst, a
		with UnboundVar _ -> raise (OpenUnify _loc)))
;;

(** Visit goals of a rule **)
let pred_goal _loc (env,c,f) n ts =
	let v = Version.reconstruct (List.rev_map (fun t -> not (bound env t)) ts) in
	let call = lid_expr _loc (Names.pred n v) in
	let c,ev = extend_version c (Version.neg v) in
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
	| Comp (n,[e1;e2],_loc) when n = Names.add ->
		let e1 = int_expr_of_term env e1 and e2 = int_expr_of_term env e2 in
		<:expr< $e1$ + $e2$ >>
	| Comp (n,[e1;e2],_loc) when n = Names.sub ->
		let e1 = int_expr_of_term env e1 and e2 = int_expr_of_term env e2 in
		<:expr< $e1$ - $e2$ >>
	| Comp (n,_,_loc) -> Loc.raise _loc (Failure ("Function " ^ n ^ " not supported"))
	| Anon _loc -> raise (UnboundVar ("_",_loc))
	| Var (v,_loc) ->
		try
			let id = lookup env v in
			<:expr< $lid:Names.int_of$ $lid_expr _loc id$ >>
		with Not_found -> raise (UnboundVar (v,_loc))
;;

let relation_goal _loc (env,c,f) r t1 t2 =
	let e1 = int_expr_of_term env t1 and e2 = int_expr_of_term env t2 in
	let tst = <:expr< $lid:r$ $e1$ $e2$ >> in
	env, c, (fun body -> f <:expr< if $tst$ then $body$ else () >>)
;;

let is_goal _loc (env,c,f) t t' =
	let e = <:expr< $uid:Names.int_cons$ $int_expr_of_term env t'$ >> in
	let (env, c, tst, p) = patt_of_t env c [] t in
	let tst = expand_tests _loc [(e,p)] tst false in
	env, c, (fun body -> f (apply_test _loc tst body <:expr< () >>))
;;

let cut_goal _loc (env,c,f) =
	env, c, (fun body -> f <:expr<
		do { $body$; raise ($uid:Names.cut_exc$ $lid:Names.my_cut_id$) }
	>>)
;;

let rec goal acc = function
	| Integer (_,_loc) -> Loc.raise _loc (Failure ("Integer not callable"))
	| Var (_,_loc) | Anon _loc ->
		Loc.raise _loc (Failure ("Meta-call not supported"))
	| Comp (n,[t;t'],_loc) when n = Names.same -> same_goal _loc acc true t t'
	| Comp (n,[t;t'],_loc) when n = Names.diff -> same_goal _loc acc false t t'
	| Comp (n,[t;t'],_loc) when n = Names.is -> is_goal _loc acc t t'
	| Comp (n,[t;t'],_loc) when n = Names.eq -> relation_goal _loc acc "=" t t'
	| Comp (n,[t;t'],_loc) when n = Names.ne -> relation_goal _loc acc "<>" t t'
	| Comp (n,[t;t'],_loc) when n = Names.lt -> relation_goal _loc acc "<" t t'
	| Comp (n,[t;t'],_loc) when n = Names.lte -> relation_goal _loc acc "<=" t t'
	| Comp (n,[t;t'],_loc) when n = Names.gt -> relation_goal _loc acc ">" t t'
	| Comp (n,[t;t'],_loc) when n = Names.gte -> relation_goal _loc acc ">=" t t'
	| Comp (n,[t],_loc) when n = Names.notp -> not_goal _loc acc t
	| Comp (n,[],_loc) when n = Names.cut -> cut_goal _loc acc
	| Comp (n,ts,_loc) -> pred_goal _loc acc n ts
and not_goal _loc (env,c,f) g =
	let (_,_,notf) = goal (env,c,(fun body -> body)) g in
	let nbody = notf <:expr< raise $uid:Names.found_exc$ >> in
	env, c, (fun body -> safe_catch _loc nbody body Names.found_exc)
;;

(** Visit rules of a predicate version **)
let rule ev c ((ts,goals,_loc):'a rule) =
	let t1,t2 = recombine_terms ts ev in
	let env,c,tst = terms _loc empty c t1 in
	let env,c,f = List.fold_left goal (env,c,(fun body -> body)) goals in
	let outs = goal_outs env t2 in
	let body = fun_apply _loc (lid_expr _loc Names.f) outs in
	let body = f body in
	apply_test _loc tst body <:expr< () >>
;;

let rule_has_cut (_,goals,_) =
	List.exists (function
		| Comp (n,[],_) when n = Names.cut -> true
		| _ -> false
	) goals
;;

(** Visit a predicate to produce a certain version **)
let pred_version _loc n rs v =
	let name = lid_patt _loc (Names.pred n v) in
	let c,ev = extend_version 0 v in
	let args = goal_ins _loc ev in
	let rs = List.map (rule ev c) rs and has_cut = List.exists rule_has_cut rs in
	let body = sequence _loc rs in
	let body = if not has_cut then body else
	<:expr<
	 	let $lid:Names.my_cut_id$ = do { incr $lid:Names.cut_id$; ! $lid:Names.cut_id$ } in
		try do { $body$; decr $lid:Names.cut_id$ } with
		[ $uid:Names.cut_exc$ id when id = $lid:Names.my_cut_id$ -> decr $lid:Names.cut_id$
		| e -> do { decr $lid:Names.cut_id$; raise e } ]
	>> in
	let f = fun_args _loc ((lid_patt _loc Names.f)::args) body in
	<:binding< $name$ = $f$ >>
;;

let string_of_pred (name,n) = name ^ "/" ^ (string_of_int n) ;;

(** Visit a predicate to produce all possible versions **)
let pred _loc ((name,n) as p) rs ms =
	if rs = [] then
		Loc.raise (let (_,_loc) = List.hd ms in _loc) (Failure
			("Mask without definition for predicate " ^ (string_of_pred p)))
	else (if List.mem p Names.builtin_preds then
		Loc.raise (let (_,_,_loc) = List.hd rs in _loc) (Failure
			("Can't redefine builtin predicate " ^ (string_of_pred p)))
	else Version.make (fun a v ->
	if ms = [] || List.exists (version_matches_mask v) ms then
		let fname = Names.pred name v in
		try (pred_version _loc name rs v)::a with
		| UnboundVar(var,_loc) ->
			warning _loc (Printf.sprintf "skipping %s, unbound %s" fname var);
			a
		| OpenUnify(_loc) ->
			warning _loc (Printf.sprintf "skipping %s, open unification" fname);
			a
	else a) [] n)
;;

(** Starters **)

let prog_statics _loc (prog : 'a prog) =
	let statics = statics prog in
	[value_type _loc statics;
	excep_decl _loc Names.notalist_exc;
	list_repr _loc statics;
	value_repr _loc statics;
	excep_decl _loc Names.notanint_exc;
	int_repr _loc statics;
	excep_decl _loc Names.found_exc;
	cut_excep_decl _loc;
	cut_id_decl _loc]
;;

let prog_rules _loc (prog : 'a prog) =
	let defs = PredMap.fold (fun p (rs,ms) acc ->
		List.append (pred _loc p (List.rev rs) (List.rev ms)) acc
	) prog [] in
	[ <:str_item< value rec $list:defs$ >> ]
;;
