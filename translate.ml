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
	let cases = if not (comps_contains comps Names.neg 1) then cases else
		<:match_case< $uid:Names.comp Names.neg$ x ->
			-($lid:Names.int_of$ x) >> :: cases in
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

let cut_rule_body _loc body = <:expr<
	let $lid:Names.my_cut_id$ = do { incr $lid:Names.cut_id$; ! $lid:Names.cut_id$ } in
	try do { $body$; decr $lid:Names.cut_id$ } with
	[ $uid:Names.cut_exc$ id when id = $lid:Names.my_cut_id$ -> decr $lid:Names.cut_id$
	| e -> do { decr $lid:Names.cut_id$; raise e } ]
>> ;;

(** Env **)

let rec bound env = function
	| Integer (_,_) -> true
	| Var (v,_loc) -> Env.bound env v
	| Comp (_,ts,_) -> List.for_all (bound env) ts
	| Anon _loc -> false
;;

(** Aux **)

let int_expr _loc i =
	<:expr< $uid:Names.int_cons$ $int:(string_of_int i)$ >>
;;

let int_patt _loc i =
	<:patt< $uid:Names.int_cons$ $int:(string_of_int i)$ >>
;;

(** Rule grouping **)

let rec equiv_t = function
	| Integer (i,_), Integer (i',_) -> i = i'
	| Comp (cn,ts,_), Comp (cn',ts',_) ->
		cn = cn' && List.length ts = List.length ts' && equiv_ts ts ts'
	| Var (v,_), Var (v',_) -> v = v'
	| Anon _, Anon _ -> true
	| _, _ -> false
and equiv_ts ts ts' = List.for_all equiv_t (List.combine ts ts')
;;

let rec exclu_t = function
	| Integer (i,_), Integer (i',_) -> i <> i'
	| Comp (cn,ts,_), Comp (cn',ts',_) ->
		cn <> cn' || List.length ts <> List.length ts' || exclu_ts ts ts'
	| Comp (_,_,_), Integer (_,_) | Integer (_,_), Comp (_,_,_) -> true
	| _, _ -> false
and exclu_ts ts ts' = List.exists exclu_t (List.combine ts ts')
;;

let extend_exclus xs hd bodies = match xs with
	| None -> [hd,bodies], []
	| Some (xs,r) ->
		if List.for_all (fun (hd',_) -> exclu_ts hd hd') xs
		then (hd,bodies)::xs, r
		else [hd,bodies], (List.rev xs)::r
;;

let extend_equivs qs hd body = match qs with
	| None -> hd, [body], None
	| Some (hd',bodies',xs) ->
		if equiv_ts hd hd' then hd', body::bodies', xs
		else hd, [body], Some (extend_exclus xs hd' (List.rev bodies'))
;;

let finish_equivs qs = match qs with
	| None -> []
	| Some (hd,bodies,xs) ->
		let xs, r = extend_exclus xs hd (List.rev bodies) in
		List.rev ((List.rev xs)::r)
;;

let group_rs v (rs:'a rule list) =
	let qs = List.fold_left (fun qs (ts,goals,_loc) ->
		let t1,t2 = Version.partition v ts in
		Some (extend_equivs qs t1 (t2,goals,_loc))
	) None rs in finish_equivs qs
;;

let nogroup_rs v (rs:'a rule list) =
	List.map (fun (ts,goals,_loc) ->
		let t1,t2 = Version.partition v ts in
		[t1, [t2, goals, _loc]]
	) rs
;;

(** Translation aux **)

let arg_ids env v =
	let env, ids = Version.fold (fun (env,ids) o ->
		if o then env, ids
		else let env, id = Env.fresh_id env in env, id::ids
	) (env,[]) v in env, List.rev ids
;;

exception UnboundVar of string * Loc.t;;

(** Prepare exprs from open terms **)
let rec goal_out_comp env c ts _loc =
	expr_of_cons _loc (Names.comp c) (goal_outs env ts)
and goal_out env = function
	| Integer (i, _loc) -> int_expr _loc i
	| Comp (c, ts, _loc) -> goal_out_comp env c ts _loc
	| Var (v, _loc) ->
		(try lid_expr _loc (Env.lookup env v)
		with Not_found -> raise (UnboundVar (v,_loc)))
	| Anon _loc -> raise (UnboundVar ("_",_loc))
and	goal_outs env t2 = List.map (goal_out env) t2 ;;

(** Create patterns from a list of terms, meanwhile update env,c,t **)
let rec patt_of_comp env t cn ts _loc =
	let env,t,in_p = patts_of_ts env t ts in
	env, t, (patt_of_cons _loc (Names.comp cn) in_p)	 
and patt_of_t env t = function
	| Integer (i,_loc) -> env, t, int_patt _loc i
	| Comp (cn,ts,_loc) -> patt_of_comp env t cn ts _loc
	| Var (v,_loc) ->
		let env, t, id = Env.gen_bind_or_test env t v in
		env, t, (lid_patt _loc id)
	| Anon _loc -> env, t, <:patt< _ >>
and patts_of_ts env t ts =
	let env,t,p = List.fold_left (fun (env,t,p) term ->
		let env,t,patt = patt_of_t env t term in
		env,t,(patt::p)
	) (env,t,[]) ts in
	env, t, List.rev p
;;

exception OpenUnify of Loc.t;;

let rec unify _loc (env,tep,tst,a) = function
	| Integer (i,_), Integer (i',_) ->
		if i = i' then env, tep, tst, a
		else env, tep, tst, true
	| Comp (cn,ts,_), Comp (cn',ts',_) ->
		if cn = cn' && List.length ts = List.length ts' then
			(* List.fold_left (unify _loc) (env,tep,tst,a) (List.combine ts ts')
			Unfortunately not valid, since unifications have to be parallel *)
			(if ts = [] then env, tep, tst, a else
				Loc.raise _loc (Failure "Deep compound-to-compound unification unsupported"))	
		else env, tep, tst, true
	| Integer (_,_), Comp (_,_,_) | Comp (_,_,_), Integer (_,_) ->
		env, tep, tst, true
	| Var (v,_), Var (v',_) ->
		(try let env, tst = Env.unify env tst v v' in env, tep, tst, a
		with Not_found -> raise (OpenUnify _loc))
	| Anon _, _ | _, Anon _ -> env, tep, tst, a
	| Var (v,_locv), Integer (i,_loci) | Integer (i,_loci), Var (v,_locv) ->
		Env.dispatch env v (fun id -> (* existing id *)
			env, (lid_expr _locv id, int_patt _loci i)::tep, tst, a
		) (fun env id -> (* fresh id *)
			env, (int_expr _loc i, lid_patt _locv id)::tep, tst, a)
	| Var (v,_locv), Comp (cn,ts,_locc) | Comp (cn,ts,_locc), Var (v,_locv) ->
		Env.dispatch env v (fun id -> (* existing id *)
			let env,tst,tp = patt_of_comp env tst cn ts _locc in
			env, (lid_expr _locv id,tp)::tep, tst, a
		) (fun env id -> (* fresh id *)
			try env, (goal_out_comp env cn ts _locc, lid_patt _locv id)::tep, tst, a
			with UnboundVar _ -> raise (OpenUnify _loc))
;;

(**
	Rules translation:
	pred -> pred_version -> rule (-> terms) -> goal -> terms
**)

let terms _loc env t1 =
	let env, ps, t = List.fold_left (fun (env,ps,t) -> function
		| Integer (i, _loc), _ ->
			env, (int_patt _loc i)::ps, t
		| Comp (cn, ts, _loc), _ ->
			let env,t,p = patt_of_comp env t cn ts _loc in
			env, p::ps, t
		| Var (v, _loc), id ->
			let env,t = Env.bind_or_test env t v id in
			env, <:patt< _ >>::ps, t
		| Anon _loc, _ -> env, <:patt< _ >>::ps, t
	) (env,[],[]) t1 in
	env, List.rev ps, test_expr _loc t
;;

(** Visit goals of a rule **)
let pred_goal _loc (env,f) n ts =
	let v = Version.reconstruct (List.rev_map (fun t -> not (bound env t)) ts) in
	let call = lid_expr _loc (Names.pred n v) and nv = Version.neg v in
	let env,ids = arg_ids env nv and t1,t2 = Version.partition nv ts in
	let ins = List.map (lid_patt _loc) ids and outs =
		try goal_outs env t2
		(* we select a version with only bound vars *)
		with UnboundVar _ -> assert false
	in
	let es = List.map (lid_expr _loc) ids in
	let env, ps, t = terms _loc env (List.combine t1 ids) in
	begin
		if t <> None || List.exists (function | <:patt< _ >> -> false | _ -> true) ps then
			warning _loc "will unify after satisfying goal, might not match Prolog semantics";
		env, (fun body -> f (wrap _loc call ins outs es ps t body))		
	end
;;	

let same_goal _loc (env,f) pos t t' =
	let env', tep, tst, a = unify _loc (env,[],[],false) (t,t') in
	let tst = test_expr _loc tst and nbody = unit_expr _loc in
	if pos then env', (fun body -> f (apply_test _loc tep tst a body nbody))
	else env, (fun body -> f (apply_test _loc tep tst a nbody body))
;;

let rec int_expr_of_term env = function
	| Integer (i,_loc) -> <:expr< $int:string_of_int i$ >>
	| Comp (n,[e1;e2],_loc) when n = Names.add ->
		let e1 = int_expr_of_term env e1 and e2 = int_expr_of_term env e2 in
		<:expr< $e1$ + $e2$ >>
	| Comp (n,[e1;e2],_loc) when n = Names.sub ->
		let e1 = int_expr_of_term env e1 and e2 = int_expr_of_term env e2 in
		<:expr< $e1$ - $e2$ >>
	| Comp (n,[e],_loc) when n = Names.neg ->
		let e = int_expr_of_term env e in <:expr< - $e$ >>
	| Comp (n,_,_loc) -> Loc.raise _loc (Failure ("Function " ^ n ^ " not supported"))
	| Anon _loc -> raise (UnboundVar ("_",_loc))
	| Var (v,_loc) ->
		try
			let id = Env.lookup env v in
			<:expr< $lid:Names.int_of$ $lid_expr _loc id$ >>
		with Not_found -> raise (UnboundVar (v,_loc))
;;

let relation_goal _loc (env,f) r t1 t2 =
	let e1 = int_expr_of_term env t1 and e2 = int_expr_of_term env t2 in
	let tst = <:expr< $lid:r$ $e1$ $e2$ >> in
	env, (fun body -> f <:expr< if $tst$ then $body$ else () >>)
;;

let is_goal _loc (env,f) t t' =
	let e = <:expr< $uid:Names.int_cons$ $int_expr_of_term env t'$ >> in
	let (env, tst, p) = patt_of_t env [] t in
	let tst = test_expr _loc tst and nbody = unit_expr _loc in
	env, (fun body -> f (single_match_expr _loc [e] [p] tst body nbody))
;;

let cut_goal _loc (env,f) =
	env, (fun body -> f <:expr<
		do { $body$; raise ($uid:Names.cut_exc$ $lid:Names.my_cut_id$) }
	>>)
;;

let true_fail_goal _loc (env,f) pos =
	env, if pos then f else
	let body = f (unit_expr _loc) in (fun _ -> body)
;;

let repeat_goal _loc (env,f) =
	env, (fun body -> f <:expr< while True do { $body$ } >>)
;;

let write_goal _loc (env,f) t =
	env, let e = goal_out env t in
	let e = <:expr< print_string ($lid:Names.string_of$ $e$) >> in
	(fun body -> f <:expr< do { $e$; $body$ } >>)
;;

let nl_goal _loc (env,f) = 
	env, (fun body -> f <:expr< do { print_newline (); $body$ } >>)
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
	| Comp (n,[],_loc) when n = Names.truep -> true_fail_goal _loc acc true
	| Comp (n,[],_loc) when n = Names.fail -> true_fail_goal _loc acc false
	| Comp (n,[],_loc) when n = Names.repeat -> repeat_goal _loc acc
	| Comp (n,[t],_loc) when n = Names.write -> write_goal _loc acc t
	| Comp (n,[],_loc) when n = Names.nl -> nl_goal _loc acc
	| Comp (n,ts,_loc) -> pred_goal _loc acc n ts
and not_goal _loc (env,f) g =
	let (_,notf) = goal (env,(fun body -> body)) g in
	let nbody = notf <:expr< raise $uid:Names.found_exc$ >> in
	env, (fun body -> f (safe_catch _loc nbody body Names.found_exc))
;;

let rule_has_cut (_,goals,_) =
	List.exists (function
		| Comp (n,[],_) when n = Names.cut -> true
		| _ -> false
	) goals
;;

let rule_body env (t2,goals,_loc) =
	let env,f = List.fold_left goal (env,(fun body -> body)) goals in
	let outs = goal_outs env t2 in
	let body = fun_apply _loc (lid_expr _loc Names.f) outs in
	f body
;;

let rule_equiv _loc env ids (t1,bodies) =
	let env,ps,t = terms _loc env (List.combine t1 ids) in
	ps, t, sequence _loc (List.map (rule_body env) bodies)
;;

let rule_excl _loc ids env exclus =
	let
		exprs = List.map (lid_expr _loc) ids and
		cases = List.map (rule_equiv _loc env ids) exclus
	in
	match_expr _loc exprs cases (unit_expr _loc)
;;

(** Visit a predicate to produce a certain version **)
let pred_version _loc group_rs name rs v =
	let has_cut = List.exists rule_has_cut rs in
	let rs = group_rs v rs in
	let env,ids = arg_ids (Env.empty Names.pred_var) v in
	let args_patt = List.map (lid_patt _loc) ids in
	let body = sequence _loc (List.map (rule_excl _loc ids env) rs) in
	let body = if not has_cut then body else cut_rule_body _loc body in
	let f = fun_args _loc ((lid_patt _loc Names.f)::args_patt) body in
	<:binding< $lid_patt _loc name$ = $f$ >>
;;

let string_of_pred (name,n) = name ^ "/" ^ (string_of_int n) ;;

(** Visit a predicate to produce all possible versions **)
let pred _loc group_rs ((name,n) as p) rs ms =
	if rs = [] then
		Loc.raise (let (_,_loc) = List.hd ms in _loc) (Failure
			("Mask without definition for predicate " ^ (string_of_pred p)))
	else (if List.mem p Names.builtin_preds then
		Loc.raise (let (_,_,_loc) = List.hd rs in _loc) (Failure
			("Can't redefine builtin predicate " ^ (string_of_pred p)))
	else Version.make (fun a v ->
	if ms = [] || List.exists (version_matches_mask v) ms then
		let fname = Names.pred name v in
		try (pred_version _loc group_rs fname rs v)::a with
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

let prog_rules _loc group_rs (prog : 'a prog) =
	let defs = PredMap.fold (fun p (rs,ms) acc ->
		List.append (pred _loc group_rs p (List.rev rs) (List.rev ms)) acc
	) prog [] in
	[ <:str_item< value rec $list:defs$ >> ]
;;
