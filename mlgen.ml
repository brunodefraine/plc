open Camlp4.PreCast ;;

(** Camlp4 aux function **)

let format_loc _loc =
	Loc.to_string _loc
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

let test_expr _loc l =
	let rec aux e = function
		| [] -> e
		| (a,b)::l -> aux <:expr< $e$ && $a$ = $b$ >> l
	in match l with
	| [] -> None
	| (a,b)::l -> Some (aux <:expr< $a$ = $b$ >> l)		
;;

type test_subject = Test_uid of string | Test_lid of string ;;

let expand_tests _loc l =
	if l = [] then None
	else
		let e,p,t = List.fold_left (fun (e,p,t) -> function
			| id, Test_uid uid ->
				(lid_expr _loc id)::e, (uid_patt _loc uid)::p, t
			| id, Test_lid lid ->
				e, p, (lid_expr _loc id, lid_expr _loc lid)::t
		) ([],[],[]) l in
		Some (tuple_expr _loc e, tuple_patt _loc p, test_expr _loc t)
;;

let apply_test _loc tst body  = match tst with
	| Some (e,p,None) ->
		<:expr< match $e$ with [ $p$ -> $body$ | _ -> () ] >>
	| Some (e,p,Some t) ->
		<:expr< match $e$ with [ $p$ when $t$ -> $body$ | _ -> () ] >>
	| None -> body
;;
