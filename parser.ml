open Ast ;;
open Camlp4.PreCast ;;

let prog = Gram.Entry.mk "prog" ;;
let rule = Gram.Entry.mk "rule" ;;
let goal = Gram.Entry.mk "goal" ;;
let term = Gram.Entry.mk "term" ;;

EXTEND Gram
GLOBAL: prog rule goal term;

prog:
	[ [ r = LIST0 rule ->
		List.fold_left (fun m ((p,ts,_),goals,_loc) ->
			let l =
				try PredMap.find p m
				with Not_found -> []
			in PredMap.add p ((ts,goals,_loc)::l) m
		) PredMap.empty r
	] ];

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
		[ x = LIDENT -> if x = "_" then Anon _loc else Atom (x,_loc)
		| x = UIDENT -> Var (x,_loc) ]
	];
END
