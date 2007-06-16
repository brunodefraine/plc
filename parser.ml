open Ast ;;
open Camlp4.PreCast ;;

let prog = Gram.Entry.mk "prog" ;;
let rule = Gram.Entry.mk "rule" ;;
let goal = Gram.Entry.mk "goal" ;;
let term = Gram.Entry.mk "term" ;;
let mask = Gram.Entry.mk "mask";

type rule_or_mask =
	  Rule of Loc.t goal * Loc.t goal list * Loc.t
	| Mask of pred * Loc.t arg_mask list * Loc.t
;;

EXTEND Gram
GLOBAL: prog rule goal term mask;

prog:
	[ [ rd = LIST0 rule_or_mask ->
		List.fold_left (fun m -> function
		| Rule ((p,ts,_),goals,_loc) ->
			let l1,l2 = try PredMap.find p m with Not_found -> [],[]
			in PredMap.add p ((ts,goals,_loc)::l1,l2) m
		| Mask (p,args,_loc) ->
			let l1,l2 = try PredMap.find p m with Not_found -> [],[]
			in PredMap.add p (l1,(args,_loc)::l2) m
		) PredMap.empty rd
	] ];

rule_or_mask:
	[
		[ (g,gs,l) = rule -> Rule (g,gs,l)
		| (p,a,l) = mask -> Mask (p,a,l) ]
	];

rule:
	[ [ g = goal; c = OPT clauses;  "." ->
		let
			clauses = match c with
			| Some c -> c
			| None -> []
		in
		(g,clauses,_loc)
	] ];

clauses:
	[ [ ":"; "-"; r = LIST1 goal SEP "," -> r ] ];

goal:
	[ [ x = LIDENT; t = OPT args ->
		let terms = match t with
			| Some t -> t
			| None -> []
		in
		((x,List.length terms),terms,_loc)
	] ];

args:
	[ [ "("; r = LIST1 term SEP ","; ")" -> r ] ];

term:
	[
		[ x = LIDENT; t = OPT args ->
			(match (x,t) with
			| ("_",None) -> Anon _loc
			| ("_",Some _) -> Loc.raise _loc (Failure "Anonymous with arguments")
			| (x,None) -> Comp (x,[],_loc)
			| (x,Some t) -> Comp (x,t,_loc))
		| x = UIDENT -> Var (x,_loc) ]
	];

mask:
	[ [ "%:"; x = LIDENT; "("; t = LIST1 arg_mask SEP ","; ")" ->
		((x, List.length t),t,_loc)
	] ];

arg_mask:
	[
		[ "+"; _ = OPT var_name -> ArgClosed _loc
		| "-"; _ = OPT var_name -> ArgOpen _loc
		| "?"; _ = OPT var_name -> ArgAny _loc ]
	];

var_name:
	[ [ x = UIDENT -> x ] ];

END
