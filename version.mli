
(** Open/closed versions **)

type t

(** [make f acc n] Folds [f] over all possible versions of length [n] **)
val make : ('a -> t -> 'a) -> 'a -> int -> 'a

(** [opened v i] returns whether position [i] is open in [v] **)
val opened : t -> int -> bool

(** Make a version from a list of booleans (indicating open) **)
val reconstruct : bool list -> t

(** [fold f acc v] Folds [f] over the positions in [v] **)
val fold : ('a -> bool -> 'a) -> 'a -> t -> 'a

(** [partition v l] will divide the elements of [l] according state (closed/open) in [v]; fails in case of insufficient/excessive elements. **)
val partition : t -> 'a list -> 'a list * 'a list

(** Convert to string **)
val to_string : t -> string

(** Invert open/closed state of all positions **)
val neg : t -> t
