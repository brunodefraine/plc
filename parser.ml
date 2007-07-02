open Ast ;;
open Camlp4.PreCast ;;

let prog = Gram.Entry.mk "prog" ;;
let rule = Gram.Entry.mk "rule" ;;
let term = Gram.Entry.mk "term" ;;
let mask = Gram.Entry.mk "mask" ;;

type rule_or_mask =
	| Rule of pred * Loc.t term list * Loc.t term list * Loc.t
	| Mask of pred * Loc.t arg_mask list * Loc.t
;;

let list_of_list_option = function
	| Some l -> l
	| None -> []
;;

let term_list _loc ts e =
	List.fold_right (fun t c ->
		Comp (Names.cons,[t;c],_loc)
	) ts (match e with
	| Some t -> t
	| None -> Comp (Names.nil,[],_loc))
;;

EXTEND Gram
GLOBAL: prog rule term mask;

prog:
	[ [ rd = LIST0 rule_or_mask ->
		List.fold_left (fun m -> function
		| Rule (p,ts,body,_loc) ->
			let l1,l2 = try PredMap.find p m with Not_found -> [],[]
			in PredMap.add p ((ts,body,_loc)::l1,l2) m
		| Mask (p,args,_loc) ->
			let l1,l2 = try PredMap.find p m with Not_found -> [],[]
			in PredMap.add p (l1,(args,_loc)::l2) m
		) PredMap.empty rd
	] ];

rule_or_mask:
	[
		[ (p,t,b,l) = rule -> Rule (p,t,b,l)
		| (p,a,l) = mask -> Mask (p,a,l) ]
	];

rule:
	[ [ x = LIDENT; t = OPT args; b = OPT body;  "." ->
		let t = list_of_list_option t and b = list_of_list_option b in
		in ((x,List.length t),t,b,_loc)
	] ];

body:
	[ [ ":"; "-"; r = LIST1 term SEP "," -> r ] ];

args:
	[ [ "("; r = LIST1 term SEP ","; ")" -> r ] ];

term:
	[ "relop" NONA
		[ x = term; "="; y = term -> Comp (Names.same,[x;y],_loc)
		| x = term; "\\="; y = term -> Comp (Names.diff,[x;y],_loc)
		| x = term; "is"; y = term -> Comp (Names.is,[x;y],_loc)
		| x = term; "=:="; y = term -> Comp (Names.eq,[x;y],_loc)
		| x = term; "=\\="; y = term -> Comp (Names.ne,[x;y],_loc)
		| x = term; "<"; y = term -> Comp (Names.lt,[x;y],_loc)
		| x = term; "=<"; y = term -> Comp (Names.lte,[x;y],_loc)
		| x = term; ">"; y = term -> Comp (Names.gt,[x;y],_loc)
		| x = term; ">="; y = term -> Comp (Names.gte,[x;y],_loc) ]
	| "add" LEFTA
		[ x = term; "+"; y = term -> Comp (Names.add,[x;y],_loc)
		| x = term; "-"; y = term -> Comp (Names.sub,[x;y],_loc) ]
	| "simple" NONA
		[ x = LIDENT; t = OPT args ->
			(match (x,t) with
			| ("_",None) -> Anon _loc
			| ("_",Some _) -> Loc.raise _loc (Failure "Anonymous with arguments")
			| (x,None) -> Comp (x,[],_loc)
			| (x,Some t) -> Comp (x,t,_loc))
		| "!" -> Comp (Names.cut,[],_loc)
		| x = UIDENT -> Var (x,_loc)
		| x = INT -> Integer (int_of_string x, _loc)
		| "("; t = term; ")" -> t
		| "["; t = LIST0 term SEP ","; e = OPT [ "|"; t = term -> t]; "]" ->
			term_list _loc t e ]
	];

mask:
	[ [ "%:"; x = LIDENT; "("; t = LIST1 arg_mask SEP ","; ")" ->
		((x, List.length t),t,_loc)
	] ];

var:
	[ [ x = UIDENT -> x,_loc ] ];

arg_mask:
	[
		[ "+"; _ = OPT var -> ArgClosed _loc
		| "-"; _ = OPT var -> ArgOpen _loc
		| "?"; _ = OPT var -> ArgAny _loc ]
	];

END
