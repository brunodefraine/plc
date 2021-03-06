
module StringSet = Set.Make(String) ;;
module StringMap = Map.Make(String) ;;

(* e.g. parent/2 *)
type pred = string * int ;;

module Pred =
struct
	type t = pred ;;
	let compare : t -> t -> int = compare ;;
end ;; 

module PredMap = Map.Make(Pred) ;;

(* terms are integers, (anonymous) variables and compound (possibly atoms) *)
type 'loc term =
	| Integer of int * 'loc
	| Var of string * 'loc
	| Anon of 'loc
	| Comp of string * 'loc term list * 'loc
;;

(* e.g. for sibling/2: (X,Y) :- parent(Z,X), parent(Z,Y). *)
type 'loc rule = 'loc term list * 'loc term list * 'loc;;

(* e.g. +X or -Y *)
type 'loc arg_mask = ArgOpen of 'loc | ArgClosed of 'loc | ArgAny of 'loc ;;

(* e.g. for same/2: +X, ?Y *)
type 'loc mask = 'loc arg_mask list * 'loc ;;

(* Complete program: map from pred to rule list + mask list *)
type 'loc prog = ('loc rule list * 'loc mask list) PredMap.t ;;

let rec statics_of_terms acc terms =
	List.fold_left (fun comps -> function
		| Comp (c,ts,_) ->
			let comps =
				let n = List.length ts in
				try
					let n' = StringMap.find c comps in
					if n = n' then comps
					else failwith ("Contradictory arities for " ^ c)
				with Not_found -> StringMap.add c n comps
			in
			statics_of_terms comps ts
		| _ -> comps
	) acc terms
;;

let rec statics_of_goal_terms acc terms =
	List.fold_left (fun comps -> function
		| Comp ("is",[t;_],_loc) -> statics_of_terms comps [t]
		| Comp ("eq",[_;_],_loc) | Comp ("ne",[_;_],_loc)
		| Comp ("lt",[_;_],_loc) | Comp ("lte",[_;_],_loc)
		| Comp ("gt",[_;_],_loc) | Comp ("gte",[_;_],_loc) -> comps
		| Comp ("not",([t] as ts),_loc) -> statics_of_goal_terms comps ts
		| Comp (c,ts,_) ->
			(* same and diff, cut, true and fail, etc. will also match here *)
			statics_of_terms comps ts
		| _ -> comps
	) acc terms
;;

let statics (prog : 'a prog) = PredMap.fold (fun pred (rules,_) acc ->
	List.fold_left (fun acc (terms,goals,_) ->
		statics_of_goal_terms (statics_of_terms acc terms) goals
	) acc rules
) prog StringMap.empty ;;
