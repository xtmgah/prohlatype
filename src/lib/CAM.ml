(* CAM = Compressed Allele Map

   Since our PHMM is parameterized by alleles, we have to keep track many
   values on a per allele basis. This module aims to provide an abstraction
   for this map: allele -> 'a.

   It is different than the Alleles.Map module (and perhaps that one should be
   replaced or deprecated) because the implementation tries to be succinct, by
   compressing the values and avoiding O(n) (n = # of alleles) maps/folds.
   Specifically, the operations are performed on the unique values in the map.
*)

open Util

type set = Alleles.set

module type M = sig

  type 'a t

  val empty : 'a t

  val to_string_full : ('a -> string) -> 'a t -> string

  val of_list : ?eq:('a -> 'a -> bool) -> (set * 'a) list -> 'a t

  val singleton : set -> 'a -> 'a t

  val to_list : 'a t -> (set * 'a) list

  (*val domain : 'a t -> set*)

  val length : 'a t -> int

  val add : ?eq:('a -> 'a -> bool) -> set -> 'a -> 'a t -> 'a t

  val join : ?eq:('a -> 'a -> bool) -> 'a t -> 'a t -> 'a t

  val get : set -> 'a t -> 'a t option

  val get_value : set -> 'a t -> 'a option

  exception StillMissing of string

  val get_exn : set -> 'a t -> 'a t

  val iter : 'a t -> f:(set -> 'a -> unit) -> unit

  val iter_values : 'a t -> f:(int -> 'a -> unit) -> unit

  val fold : 'a t -> init:'b -> f:('b -> set -> 'a -> 'b) -> 'b

  val map : 'a t -> f:('a -> 'b) -> 'b t

  (* Not the perfect name for this function. *)
  val concat_map : ?eq:('b -> 'b -> bool)
                  -> 'a t
                  -> f:(set -> 'a -> 'b t)
                  -> 'b t

  val concat_map2 : ?eq:('c -> 'c -> bool)
                    -> 'a t
                    -> by:'b t
                    -> f:(set -> 'a -> 'b -> 'c t)
                    -> 'c t

  val concat_map2_partial : ?eq:('c -> 'c -> bool)
                            -> 'a t
                            -> by:'b t
                            -> f:(set -> 'a -> 'b -> 'c t)
                            -> missing:(set -> 'a -> 'c t)
                            -> 'c t

  val map2 : ?eq:('c -> 'c -> bool)
            -> 'a t
            -> 'b t
            -> f:('a -> 'b -> 'c)
            -> 'c t

  val map3 : ?eq:('d -> 'd -> bool)
            -> 'a t
            -> 'b t
            -> 'c t
            -> f:('a -> 'b -> 'c -> 'd)
            -> 'd t

  val init_everything : 'a -> 'a t

  val map2_partial : ?eq:('c -> 'c -> bool)
                    -> 'a t
                    -> by:'b t
                    -> missing:(set -> 'a -> 'c t)
                    -> f:('a -> 'b -> 'c)
                    -> 'c t

  val map3_partial : ?eq:('d -> 'd -> bool)
                    -> 'a t
                    -> by1:'b t
                    -> missing1:(set -> 'a -> 'b t)
                    -> by2:'c t
                    -> missing2:(set -> 'a -> 'b -> 'c t)
                    -> f:('a -> 'b -> 'c -> 'd)
                    -> 'd t

  val partition_map : 'a t -> f:(set -> 'a -> [< `Fst of 'b | `Snd of 'c ]) ->
     'b t * 'c t

end (* M *)
(*
module Interval : (sig

  type t

  val make : int -> int -> t
  val inter_diff : t -> t -> t option * t list * t list

  val extend : t -> int -> t option
  val merge : t -> t -> t option

end)= struct

  let make s1 e1 =
    if e1 < s1 then invalid_argf "Not in order %d < %d" e1 s1 else (e1, s1)

  let inter_diff (t1  t2 =
    let s1, e1 = t1 in
    let s2, e2 = t2 in
    if s1 = e1 then begin
      if s1 > s2 then begin                     (* S2_1 *)

        if e2 < s1 then                           (* E2_1 *)
          None,     [t1],               [t2]
        else if e2 = s1 then                      (* E2_2 *)
          Some t1,  [],                 [s2, e2 - 1]
        else begin (* e2 > s1 *)                        (* E2_3 *)
          Some t1,  [],                 [s2, s1 - 1; s1 + 1, e2]
        end

      end else if s1 = s2 then begin            (* S2_2 *)

        if e2 < s1 then                           (* E2_1 *)
          invalid_argf  "broken invariant (%d,%d) (%d, %d)" s1 e1 s2 e2
        else if e2 = s1 then                      (* E2_2 *)
          Some t1,  [],                 []
        else begin (* e2 > s1 *)                        (* E2_3 *)
          Some t1,  [],                 [s1 + 1, e2]
        end

      end else (*if s1 < s2 then *) begin            (* S2_3 *)

        if e2 <= s1 then                          (* E2_1, E2_2 *)
          invalid_argf  "broken invariant (%d,%d) (%d, %d)" s1 e1 s2 e2
        else begin (* e2 > s1 *)                        (* E2_3 *)
          None,           [t1],         [t2]
        end
      end

    end else begin (* s1 < e1 *)
      if s1 > s2 then                           (* S2_1 *)
        if e2 < s1 then                           (* E2_1 *)
          None,           [t1],         [t2]
        else if e2 = s1 then                      (* E2_2 *)
          Some (e2, s1),  [s1 + 1, e1], [s2, s1 - 1]
        else if (*e2 > s1 && *) e2 < e1 then      (* E2_3 *)
          Some (s1, e2),  [e2 + 1, e1], [s2, s1 - 1]
        else if e2 = e1 then                      (* E2_4 *)
          Some t1,        [],           [s2, s1 - 1]
        else (* e2 > e1 *)                        (* E2_5 *)
          Some t1,        [],           [s2, s1 - 1; e1 + 1, e2]

      else if s1 = s2 then                      (* S2_2 *)
        if e2 < s1 then                           (* E2_1 *)
          invalid_argf  "broken invariant (%d,%d) (%d, %d)" s1 e1 s2 e2
        else if e2 = s1 then                      (* E2_2 *)
          Some t2,        [s1 + 1, e1], []
        else if (*e2 > s1 && *) e2 < e1 then      (* E2_3 *)
          Some (s1, e2),  [e2 + 1, e1], []
        else if e2 = e1 then                      (* E2_4 *)
          Some t1,        [],           []        (* Perfect alignment! *)
        else (* e2 > e1 *)                        (* E2_5 *)
          Some t1,        [],           [e1 + 1, e2]

      else if s1 < s2 && s2 < e1 then           (* S2_3 *)
        if e2 <= s1 then                           (* E2_1, E2_2 *)
          invalid_argf  "broken invariant (%d,%d) (%d, %d)" s1 e1 s2 e2
        else if (*e2 > s1 && *) e2 < e1 then      (* E2_3 *)
          Some t2,        [s1, s2 - 1; e2 + 1, e1], []
        else if e2 = e1 then                      (* E2_4 *)
          Some t2,        [s1, s2 - 1],             []
        else (* e2 > e1 *)                        (* E2_5 *)
          Some (s2,e1),   [s1, s2 - 1],             [e1+1, e2]

      else if e1 = s2 then                      (* S2_4 *)
        if e2 < e1 then                           (* E2_1, E2_2, E2_3 *)
          invalid_argf  "broken invariant (%d,%d) (%d, %d)" s1 e1 s2 e2
        else if e2 = e1 then                      (* E2_4 *)
          Some t2,        [s1, s2 - 1],             []
        else (* e2 > e1 *)                        (* E2_5 *)
          Some (s2,e1),   [s1, s2 - 1],             [e1+1, e2]

      else (*if e1 < s2 then *)                 (* S2_5 *)
        if e2 <= e1 then                           (* E2_1, E2_2, E2_3, E2_4 *)
          invalid_argf  "broken invariant (%d,%d) (%d, %d)" s1 e1 s2 e2
        else (* e2 > e1 *)                        (* E2_5 *)
          None,           [t1],                     [t2]
    end

  let extend (s, e) n =
    if e + 1 = n then
      Some (s, n)
    else
      None

  let merge p1 p2 =
    let s1, e1 = p1 in
    let s2, e2 = p2 in
    if e1 + 1 = s2 then
      Some (s1, e2)
    else if e2 + 1 = s1 then
      Some (s2, e1)
    else
      None

end (* Interval *)
*)

module Make (Aset : Alleles.Set) : M = struct

  (*
  let intervals_of_allele_set =
    Aset.fold_set_indices ~init:(`Start []) ~f:(fun a i ->
      match a with
      | `Start l -> `State (Interval.make i i, l)
      | `State (interval, l) ->
          match Interval.extend interval i with
          | None    -> `State (Interval.make i i, interval :: l)
          | Some ni -> `State (ni, l))
    |> function
       | `Start l       -> l                (* Only if empty *)
       | `State (i, l)  -> List.rev (i :: l)
       *)


  type 'a mlist =
    | Nil
    | Cons of 'a cell
  and 'a cell =
    { value       : 'a
    ; mutable set : set
    ; mutable tl  : 'a mlist
    }

  type 'a t = 'a mlist

  let empty = Nil

  let allele_set_to_string s = Aset.to_human_readable s

  let rec to_list = function
    | Nil    -> []
    | Cons c -> (c.set, c.value) :: (to_list c.tl)

  let to_string t =
    String.concat ~sep:"\n\t"
      (List.map (to_list t) ~f:(fun (s,_v) ->
        sprintf "%s" (allele_set_to_string s)))

  let to_string_full v_to_s t =
    String.concat ~sep:"\n\t"
      (List.map (to_list t) ~f:(fun (s,v) ->
        sprintf "%s:%s" (allele_set_to_string s) (v_to_s v)))

  (* Union, tail recursive. *)
  (*
  let mutate_or_add ?eq lst ((alleles, value) as p) =
    let eq = Option.value eq ~default:(=) in
    let rec loop acc = function
      | (s, v) :: t when eq v value -> (printf "1\n"); acc @ (Aset.union s alleles, v) :: t
      | h :: t                      -> loop (h :: acc) t
      | []                          -> (printf "2\n"); p :: acc
    in
    loop [] lst
    *)

  let cons set value tl =
    Cons { value; set; tl}

  let mutate_or_add ?eq lst alleles value =
    let eq = Option.value eq ~default:(=) in
    let rec loop c =
      if eq c.value value then
        c.set <- Aset.union c.set alleles
      else match c.tl with
           | Nil     -> c.tl <- cons alleles value c.tl
           | Cons cc -> loop cc
    in
    match lst with
    | Nil     -> cons alleles value lst
    | Cons c  -> loop c; lst

  let add ?eq alleles value l = mutate_or_add ?eq l alleles value

  let singleton set value = cons set value Nil

  let of_list ?eq l =
    List.fold_left l ~init:Nil
      ~f:(fun acc (set, value) -> mutate_or_add ?eq acc set value)

  (*let to_list l = l *)

  let fold_left lst ~init ~f =
    let rec loop acc = function
      | Nil                     -> acc
      | Cons { value; set; tl } -> loop (f acc set value) tl
    in
    loop init lst

  let join ?eq l1 l2 = fold_left l1 ~init:l2 ~f:(mutate_or_add ?eq)

  let map lst ~f =
    let rec loop = function
      | Nil     -> Nil
      | Cons c  -> Cons { value = f c.value
                        ; set = c.set
                        ; tl = loop c.tl
                        }
    in
    loop lst

  (*let domain = function
    | Nil     -> Aset.init ()
    | Cons { hd = (init, _) ; tl } ->
                  fold_left ~init ~f:(fun u s _ -> Aset.union u s) tl*)

  let length l = fold_left ~init:0 ~f:(fun s _ _ -> s + 1) l

  exception StillMissing of string

  let still_missingf fmt =
    ksprintf (fun s -> raise (StillMissing s)) fmt

  let set_assoc_k ?n ?missing to_find lst ~k ~init =
    let rec loop to_find acc = function
      | Nil         -> begin match missing with
                       | None -> still_missingf "%s%s after looking in: %s"
                                  (Option.value ~default:"" n)
                                  (allele_set_to_string to_find) (to_string lst)
                       | Some m -> m to_find acc
                       end
      | Cons { set; value ; tl } ->
          let inter, still_to_find, same_intersect, no_intersect =
            Aset.inter_diff to_find set
          in
          if same_intersect then begin                      (* Found everything *)
            k to_find value acc
          end else if no_intersect then begin                 (* Found nothing. *)
            loop to_find acc tl
          end else begin                                    (* Found something. *)
            let nacc = k inter value acc in
            loop still_to_find nacc tl
          end
    in
    loop to_find init lst

  let set_assoc_exn to_find lst =
    set_assoc_k to_find lst
      ~init:Nil
      ~k:(fun to_find value acc -> cons to_find value acc)

  let set_assoc to_find t =
    try Some (set_assoc_exn to_find t)
    with (StillMissing _) -> None

  let get_exn = set_assoc_exn

  let get = set_assoc

  let get_value s t =
    Option.bind (get s t) ~f:(function
      | Cons { value; _} -> Some value
      | _                -> None)

  let iter l ~f =
    fold_left ~init:() ~f:(fun () set value -> f set value) l

  let iter_values l ~f =
    iter l ~f:(fun set value ->
      Aset.iter_set_indices set ~f:(fun i -> f i value))

  let fold = fold_left

  let absorb ?eq t ~init = fold_left t ~init ~f:(mutate_or_add ?eq)

  let fold_new ~f l = fold_left ~init:Nil ~f l

  let concat_map ?eq l ~f =
    fold_new l ~f:(fun init s a -> absorb ?eq (f s a) ~init)

  (* The order of set arguments matters for performance. Better to fold over
     the longer list and lookup (set_assoc_k) into the shorter one. Remember
     that the lookup requires a Allele.inter_diff per item! Perhaps it makes
     sense to keep track of the length to avoid O(n) lookups and then
     automatically re-order functional arguments as necessary?

     Probably just need a better data structure. *)
  let concat_map2 ?eq l ~by ~f =
    fold_new l ~f:(fun init s a ->
      set_assoc_k s by ~init ~k:(fun intersect b init ->
        absorb ?eq (f intersect a b) ~init))

  let concat_map2_partial ?eq l ~by ~f ~missing =
    fold_new l ~f:(fun init s a ->
      set_assoc_k s by ~init
        ~k:(fun intersect b init -> absorb ?eq (f intersect a b) ~init)
        ~missing:(fun sm init -> absorb ?eq ~init (missing sm a)))

  let map2 ?eq l1 l2 ~f =
    fold_new l1 ~f:(fun init s a ->
      set_assoc_k s l2 ~init ~k:(fun intersect b acc ->
        mutate_or_add ?eq acc intersect (f a b)))

  let map3 ?eq l1 l2 l3 ~f =
    fold_new l1 ~f:(fun init is1 a ->
      set_assoc_k ~n:"1" is1 l2 ~init ~k:(fun is2 b init ->
        set_assoc_k ~n:"2" is2 l3 ~init ~k:(fun intersect c acc ->
          mutate_or_add ?eq acc intersect (f a b c))))

  let map2_partial ?eq l ~by ~missing ~f =
    fold_new l ~f:(fun init s a ->
      set_assoc_k s by ~init
        ~k:(fun intercept b acc -> mutate_or_add ?eq acc intercept (f a b))
        ~missing:(fun sm init -> absorb ?eq ~init (missing sm a)))

  let map3_partial ?eq l ~by1 ~missing1 ~by2 ~missing2 ~f =
    fold_new l ~f:(fun init is1 a ->
      let k is2 b init =
        let k2 intercept c acc = mutate_or_add ?eq acc intercept (f a b c) in
        set_assoc_k is2 by2 ~init ~k:k2
          ~missing:(fun sm init ->
            fold_left (missing2 sm a b) ~init ~f:(fun init s b -> k2 s b init))
      in
      set_assoc_k is1 by1 ~init ~k
        ~missing:(fun sm init ->
          fold_left (missing1 sm a) ~init ~f:(fun init s b -> k s b init)))

  let init_everything v =
    let nothing = Aset.init () in
    singleton (Aset.complement nothing) v

  let partition_map l ~f =
    let rec loop bs cs = function
      | Nil                     -> bs, cs
      | Cons { set; value; tl } ->
          match f set value with
          | `Fst b -> loop (cons set b bs) cs tl
          | `Snd c -> loop bs (cons set c cs) tl
    in
    loop Nil Nil l

end (* Make *)
