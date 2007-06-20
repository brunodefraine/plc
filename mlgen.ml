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

type ('e, 'p) test = Maybe of 'e * 'p * 'e option | Always | Never ;;

let expand_tests _loc ep t abort =
	if abort then Never
	else if ep = [] && t = [] then Always
	else
		let e,p = List.split ep in
		Maybe (tuple_expr _loc e, tuple_patt _loc p, test_expr _loc t)
;;

let apply_test _loc tst pbody nbody = match tst with
	| Maybe (e,p,None) ->
		(match p with
		| <:patt< $lid:_$ >> -> <:expr< let $p$ = $e$ in $pbody$ >>
		| _ -> <:expr< match $e$ with [ $p$ -> $pbody$ | _ -> $nbody$ ] >>)
	| Maybe (e,p,Some t) ->
		(match (e,p) with
		| <:expr< () >>, <:patt< () >> -> <:expr< if $t$ then $pbody$ else $nbody$ >>
		| _ -> <:expr< match $e$ with [ $p$ when $t$ -> $pbody$ | _ -> $nbody$ ] >>)
	| Always -> pbody
	| Never -> nbody
;;

let wrap _loc call ins outs tst body =
	let body = apply_test _loc tst body <:expr< () >> in
	let body = fun_args _loc ins body in
	fun_apply _loc call (body::outs)
;;

let safe_catch _loc e1 e2 exc =
	<:expr< try $e1$; fun () -> $e2$ with [ $uid:exc$ -> fun () -> () ] () >> 
;;
