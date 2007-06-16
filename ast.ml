
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

(* atoms and integers are constants *)
type 'loc term =
	(*| Integer of int * 'loc *)
	| Var of string * 'loc
	| Anon of 'loc
	| Comp of string * 'loc term list * 'loc
;;

(* e.g. parent(X,maja) *)
type 'loc goal = pred * 'loc term list * 'loc ;;

type 'loc ext_goal =
	| Pos of 'loc goal * 'loc
	| Neg of 'loc goal * 'loc
	| Same of 'loc term * 'loc term * 'loc
;;

(* e.g. for sibling/2: (X,Y) :- parent(Z,X), parent(Z,Y). *)
type 'loc rule = 'loc term list * 'loc ext_goal list * 'loc;;

(* e.g. +X or -Y *)
type 'loc arg_mask = ArgOpen of 'loc | ArgClosed of 'loc | ArgAny of 'loc ;;

(* e.g. for same/2: +X, ?Y *)
type 'loc mask = 'loc arg_mask list * 'loc ;;

(* Complete program: map from pred to rule list + mask list *)
type 'loc prog = ('loc rule list * 'loc mask list) PredMap.t ;;

let rec statics_of_terms acc terms =
	List.fold_left (fun comps term -> match term with
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
		| _ -> acc
	) acc terms
;;

let statics (prog : 'a prog) = PredMap.fold (fun pred (rules,_) acc ->
	List.fold_left (fun acc (terms,egoals,_) ->
		let acc = statics_of_terms acc terms in
		List.fold_left (fun acc -> function
			| Pos ((_,terms,_),_) -> statics_of_terms acc terms
			| Neg ((_,terms,_),_) -> statics_of_terms acc terms
			| Same (t1,t2,_) -> statics_of_terms acc [t1; t2]
		) acc egoals
	) acc rules
) prog StringMap.empty ;;
