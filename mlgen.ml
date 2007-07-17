open Camlp4.PreCast ;;

(** Camlp4 aux function **)

let format_loc _loc =
	Loc.to_string _loc
;;

let warning _loc msg =
	Printf.eprintf "%s:\nWarning: %s\n" (format_loc _loc) msg
;;

(** AST Helpers **)

let lid_patt _loc n = <:patt< $lid:n$ >> ;;
let lid_expr _loc n = <:expr< $lid:n$ >> ;;
let uid_patt _loc n = <:patt< $uid:n$ >> ;;
let uid_expr _loc n = <:expr< $uid:n$ >> ;;

let tuple_expr _loc = function
	| [] -> <:expr< () >> (* empty tuple = unit *)
	| [p] -> p (* singleton tuple = value *)
	| e::es -> <:expr< ($e$,$list:es$) >> (* true tuple *)
;;

let tuple_patt _loc = function
	| [] -> <:patt< () >>
	| [p] -> p
	| p::ps -> <:patt< ($p$,$list:ps$) >>
;;

let unit_expr _loc = <:expr< () >> ;;

let ctyp_of_cons _loc n cs =
	match cs with
	| [] -> <:ctyp< $uid:n$ >>
	| c::cs ->
		let argt = List.fold_left (fun acc c ->
			<:ctyp< $acc$ and $c$ >>
		) c cs in
		<:ctyp< $uid:n$ of $argt$ >>
;;

let patt_of_cons _loc n ps =
	List.fold_left (fun acc p ->
		<:patt< $acc$ $p$ >>
	) <:patt< $uid:n$ >> ps
;;

let expr_of_cons _loc n es =
	List.fold_left (fun acc e ->
		<:expr< $acc$ $e$ >>
	) <:expr< $uid:n$ >> es
;;

let concat_expr ?sep _loc strs =
	List.fold_left (fun acc s ->
		match acc with
		| Some e ->
		begin
			match sep with
			| Some sep -> Some <:expr< $e$ ^ $str:sep$ ^ $s$ >>
			| None -> Some <:expr< $e$ ^ $s$ >> 
		end
		| None -> Some s
	) None strs
;;

let fun_args _loc args body =
	if args = [] then <:expr< fun () -> $body$ >>
	else List.fold_right (fun arg body ->
		<:expr< fun $arg$ -> $body$ >>
	) args body
;;

let fun_apply _loc e args =
	if args = [] then <:expr< $e$ () >>
	else List.fold_left (fun e arg ->
		<:expr< $e$ $arg$ >>
	) e args
;;

let sequence _loc = function
	| [e] -> e
	| es -> <:expr< do { $list:es$ } >>
;;

let test_expr _loc l =
	let l = List.map (fun (a,b) -> (lid_expr _loc a, lid_expr _loc b)) l in
	let rec aux e = function
		| [] -> e
		| (a,b)::l -> aux <:expr< $e$ && $a$ = $b$ >> l
	in match l with
	| [] -> None
	| (a,b)::l -> Some (aux <:expr< $a$ = $b$ >> l)		
;;

let if_expr _loc t body nbody = match t with
	| None -> body
	| Some t -> <:expr< if $t$ then $body$ else $nbody$ >>
;;

let match_expr _loc es cases nbody =
	match es, cases with
	| es, [ ps, t, body ] ->
		let eps = List.combine es ps in
		let eps = List.filter (fun (e,p) -> match p with | <:patt< _ >> -> false | _ -> true) eps in
		(match eps with
		| [] -> if_expr _loc t body nbody
		| _ ->
			let es,ps = List.split eps in
			(match t with
			| None ->
				if List.for_all (function | <:patt< $lid:_$ >> -> true | _ -> false) ps
				then <:expr< let $tuple_patt _loc ps$ = $tuple_expr _loc es$ in $body$ >>	
				else <:expr< match $tuple_expr _loc es$ with [ $tuple_patt _loc ps$ -> $body$ | _ -> $nbody$ ] >>
			| Some t -> <:expr< match $tuple_expr _loc es$ with [ $tuple_patt _loc ps$ when $t$ -> $body$ | _ -> $nbody$ ] >> ))
	| _ ->
	let cases = List.map (fun (ps,t,body) -> match t with
		| None -> <:match_case< $tuple_patt _loc ps$ -> $body$ >>
		| Some t -> <:match_case< $tuple_patt _loc ps$ when $t$ -> $body$ >>
	) cases in
	<:expr< match $tuple_expr _loc es$ with [ $list:cases$ | _ -> $nbody$ ] >>
;;

let single_match_expr _loc es ps t body nbody = match_expr _loc es [ps,t,body] nbody ;;

let apply_test _loc ep t abort pbody nbody =
	if abort then nbody
	else
		let es,ps = List.split ep in
		single_match_expr _loc es ps t pbody nbody
;;

let wrap _loc call ins outs es ps t body =
	let body = single_match_expr _loc es ps t body (unit_expr _loc) in
	let body = fun_args _loc ins body in
	fun_apply _loc call (body::outs)
;;

let safe_catch _loc e1 e2 exc =
	<:expr< try $e1$; fun () -> $e2$ with [ $uid:exc$ -> fun () -> () ] () >> 
;;
