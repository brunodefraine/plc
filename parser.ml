open Ast ;;
open Camlp4.PreCast ;;

let prog = Gram.Entry.mk "prog" ;;
let rule = Gram.Entry.mk "rule" ;;
let ext_goal = Gram.Entry.mk "ext_goal" ;;
let goal = Gram.Entry.mk "goal" ;;
let term = Gram.Entry.mk "term" ;;
let expr = Gram.Entry.mk "expr" ;;
let mask = Gram.Entry.mk "mask" ;;

type rule_or_mask =
	  Rule of Loc.t goal * Loc.t ext_goal list * Loc.t
	| Mask of pred * Loc.t arg_mask list * Loc.t
;;

let goal_lid (x,t,_loc) =
	let terms = match t with
	| Some t -> t
	| None -> []
	in
	((x,List.length terms),terms,_loc)
;;

let term_lid (x,t,_loc) =
	(match (x,t) with
	| ("_",None) -> Anon _loc
	| ("_",Some _) -> Loc.raise _loc (Failure "Anonymous with arguments")
	| (x,None) -> Comp (x,[],_loc)
	| (x,Some t) -> Comp (x,t,_loc))
;;

let term_list _loc ts e =
	List.fold_right (fun t c ->
		Comp ("cons",[t;c],_loc)
	) ts (match e with
	| Some t -> t
	| None -> Comp ("nil",[],_loc))
;;

EXTEND Gram
GLOBAL: prog rule ext_goal goal term expr mask;

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
	[ [ ":"; "-"; r = LIST1 ext_goal SEP "," -> r ] ];

ext_goal:
	[
		[ "not"; "("; g = goal ;")" -> Neg (g,_loc)
		| (x,t,l) = ident_args; "="; y = term -> Same (term_lid (x,t,l),y,_loc)
		| x = other_term; "="; y = term -> Same (x,y,_loc)
		| (x,t,l) = ident_args; "\\="; y = term -> Diff (term_lid (x,t,l),y,_loc)
		| x = other_term; "\\="; y = term -> Diff (x,y,_loc)
		| (x,t,l) = ident_args; "is"; y = expr -> Is (term_lid (x,t,l),y,_loc)
		| x = other_term; "is"; y = expr -> Is (x,y,_loc)
		| (x,t,l) = ident_args; "=:="; y = expr -> Eq (Term (term_lid (x,t,l)),y,_loc)
		| x = other_term; "=:="; y = expr -> Eq (Term x,y,_loc)
		| "("; x = expr; ")"; "=:="; y = expr -> Eq (x,y,_loc)
		| (x,t,l) = ident_args; "=\\="; y = expr -> NotEq (Term (term_lid (x,t,l)),y,_loc)
		| x = other_term; "=\\="; y = expr -> NotEq (Term x,y,_loc)
		| "("; x = expr; ")"; "=\\="; y = expr -> NotEq (x,y,_loc) 
		| (x,t,l) = ident_args -> Pos (goal_lid (x,t,l),_loc) ]
	];

ident_args:
	[ [ x = LIDENT; t = OPT args -> x,t,_loc ] ];

var:
	[ [ x = UIDENT -> x,_loc ] ];

goal:
	[ [ (x,t,l) = ident_args -> goal_lid (x,t,l) ] ];

args:
	[ [ "("; r = LIST1 term SEP ","; ")" -> r ] ];

term:
	[
		[ (x,t,l) = ident_args -> term_lid (x,t,l)
		| t = other_term -> t ]
	];

other_term:
	[
		[ x = UIDENT -> Var (x,_loc)
		| x = INT -> Integer (int_of_string x,_loc)
		| "["; t = LIST0 term SEP ","; e = OPT [ "|"; t = term -> t ]; "]" -> term_list _loc t e ]
	];

expr:
	[ "add" LEFTA
		[ x = expr; "+"; y = expr -> Add(x,y,_loc)
		| x = expr; "-"; y = expr -> Sub(x,y,_loc)]
	| "simple" NONA
		[ t = term -> Term t
		| "("; e = expr ;")" -> e ]
	];

mask:
	[ [ "%:"; x = LIDENT; "("; t = LIST1 arg_mask SEP ","; ")" ->
		((x, List.length t),t,_loc)
	] ];

arg_mask:
	[
		[ "+"; _ = OPT var -> ArgClosed _loc
		| "-"; _ = OPT var -> ArgOpen _loc
		| "?"; _ = OPT var -> ArgAny _loc ]
	];

END
