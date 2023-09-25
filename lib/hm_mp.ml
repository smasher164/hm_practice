type id = string

(* Maps a type variable to a list of trait predicates. *)
type pred = { tbl : (id, id list * pred option) Hashtbl.t }
