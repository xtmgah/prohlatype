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

  val allele_set_to_string : set -> string

  val empty : 'a t

  val to_string_full : ('a -> string) -> 'a t -> string

  val of_list : ?eq:('a -> 'a -> bool) -> (set * 'a) list -> 'a t

  val singleton : set -> 'a -> 'a t

  val to_list : 'a t -> (set * 'a) list

  val domain : 'a t -> set

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

  (* Default to not bijective map *)
  val map : ?bijective:bool -> 'a t -> f:('a -> 'b) -> 'b t

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

module Make (AS : Alleles.Set) : M = struct

  type 'a mlist =
    | Nil
    | Cons of 'a cell
  and 'a cell =
    { mutable hd : 'a
    ; mutable tl : 'a mlist
    }

  type 'a t = (set * 'a) mlist

  let empty = Nil

  let allele_set_to_string s = AS.to_human_readable s

  let rec to_list = function
    | Nil    -> []
    | Cons c -> c.hd :: (to_list c.tl)

  let to_string t =
    String.concat ~sep:"\n\t"
      (List.map (to_list t) ~f:(fun (s,_v) ->
        sprintf "%s" (allele_set_to_string s)))

  let to_string_full v_to_s t =
    String.concat ~sep:"\n\t"
      (List.map (to_list t) ~f:(fun (s,v) ->
        sprintf "%s:%s" (allele_set_to_string s) (v_to_s v)))

  (* let mutate_or_add assoc new_allele_set value =
    let added =
      List.fold assoc ~init:false ~f:(fun added (into, v) ->
        if added then
          added
        else if v = value then begin
          AS.unite ~into new_allele_set;
          true
        end else
          false)
    in
    if added then
      assoc
    else
      (AS.copy new_allele_set, value) :: assoc *)

  (* Union, tail recursive. *)
  (*
  let mutate_or_add ?eq lst ((alleles, value) as p) =
    let eq = Option.value eq ~default:(=) in
    let rec loop acc = function
      | (s, v) :: t when eq v value -> (printf "1\n"); acc @ (AS.union s alleles, v) :: t
      | h :: t                      -> loop (h :: acc) t
      | []                          -> (printf "2\n"); p :: acc
    in
    loop [] lst
    *)

  let cons hd tl =
    Cons { hd; tl}

  let mutate_or_add ?eq lst ((alleles, value) as p) =
    let eq = Option.value eq ~default:(=) in
    let rec loop ({ hd = (s, v); tl } as c) =
      if eq v value then
        c.hd <- AS.union s alleles, v
      else match tl with
           | Nil     -> c.tl <- Cons { hd = p; tl = Nil}
           | Cons cc -> loop cc
    in
    match lst with
    | Nil     -> cons p lst
    | Cons c  -> loop c; lst

  let add ?eq alleles v l = mutate_or_add ?eq l (alleles,v)

  let singleton s a = cons (s,a) Nil

  let of_list ?eq l = List.fold_left l ~init:Nil ~f:(mutate_or_add ?eq)

  (*let to_list l = l *)

  let fold_left ~init ~f lst =
    let rec loop acc = function
      | Nil             -> acc
      | Cons { hd; tl } -> loop (f acc hd) tl
    in
    loop init lst

  let join ?eq l1 l2 = fold_left l1 ~init:l2 ~f:(mutate_or_add ?eq)

  let map ~f lst =
    fold_left ~init:Nil ~f:(fun acc v -> cons (f v) acc)

  let map_snd ~f =
    fold_left ~init:Nil ~f:(fun acc (s, v) -> cons (s, f v) acc)

  let domain = function
    | Nil     -> AS.init ()
    | Cons { hd = (init, _) ; tl } ->
                  fold_left ~init ~f:(fun u (s, _) -> AS.union u s) tl

  let length l = fold_left ~init:0 ~f:(fun s _ -> s + 1) l

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
      | Cons { hd = (s,v) ; tl } ->
          let inter, still_to_find, same_intersect, no_intersect =
            AS.inter_diff to_find s
          in
          if same_intersect then begin                      (* Found everything *)
            k to_find v acc
          end else if no_intersect then begin                 (* Found nothing. *)
            loop to_find acc tl
          end else begin                                    (* Found something. *)
            let nacc = k inter v acc in
            loop still_to_find nacc tl
          end
    in
    loop to_find init lst

  let set_assoc_exn to_find lst =
    set_assoc_k to_find lst
      ~init:Nil
      ~k:(fun to_find v acc -> cons (to_find, v) acc)

  let set_assoc to_find t =
    try Some (set_assoc_exn to_find t)
    with (StillMissing _) -> None

  let get_exn = set_assoc_exn

  let get = set_assoc

  let get_value s t =
    Option.bind (get s t) ~f:(function
      | Cons { hd = (_,v) ; _} -> Some v
      | _                      -> None)

  let iter l ~f = fold_left ~init:() ~f:(fun () (s, v) -> f s v) l

  let iter_values l ~f =
    iter l ~f:(fun a v ->
      AS.iter_set_indices a ~f:(fun i -> f i v))

  let fold l ~init ~f = fold_left l ~init ~f:(fun b (a, s) -> f b a s)

  let map ?bijective l ~f =
    match bijective with
    | Some true         ->                                            (* O(n) *)
        map_snd ~f l
    | Some false | None ->                                          (* O(n^2) *)
        fold_left l ~init:Nil ~f:(fun acc (s, v) -> add s (f v) acc)

  let absorb_k t ~init ~f = fold_left t ~init ~f

  let absorb ?eq t ~init = fold_left t ~init ~f:(mutate_or_add ?eq)

  let fold_new ~f l = fold_left ~init:Nil ~f l

  let concat_map ?eq l ~f =
    fold_new l ~f:(fun init (s, a) -> absorb ?eq (f s a) ~init)

  (* The order of set arguments matters for performance. Better to fold over
     the longer list and lookup (set_assoc_k) into the shorter one. Remember
     that the lookup requires a Allele.inter_diff per item! Perhaps it makes
     sense to keep track of the length to avoid O(n) lookups and then
     automatically re-order functional arguments as necessary?

     Probably just need a better data structure. *)
  let concat_map2 ?eq l ~by ~f =
    (*printf "%d %d\n" (List.length l) (List.length by); *)
    fold_new l ~f:(fun init (s, a) ->
      set_assoc_k s by ~init ~k:(fun intersect b init ->
        absorb ?eq (f intersect a b) ~init))

  let concat_map2_partial ?eq l ~by ~f ~missing =
    fold_new l ~f:(fun init (s, a) ->
      set_assoc_k s by ~init
        ~k:(fun intersect b init -> absorb ?eq (f intersect a b) ~init)
        ~missing:(fun sm init -> absorb ?eq ~init (missing sm a)))

  let map2 ?eq l1 l2 ~f =
    fold_new l1 ~f:(fun init (s, a) ->
      set_assoc_k s l2 ~init ~k:(fun intersect b acc ->
        mutate_or_add ?eq acc (intersect, f a b)))

  let map3 ?eq l1 l2 l3 ~f =
    fold_new l1 ~f:(fun init (is1, a) ->
      set_assoc_k ~n:"1" is1 l2 ~init ~k:(fun is2 b init ->
        set_assoc_k ~n:"2" is2 l3 ~init ~k:(fun intersect c acc ->
          mutate_or_add ?eq acc (intersect, f a b c))))

  let map2_partial ?eq l ~by ~missing ~f =
    fold_new l ~f:(fun init (s, a) ->
      set_assoc_k s by ~init
        ~k:(fun intercept b acc -> mutate_or_add ?eq acc (intercept, f a b))
        ~missing:(fun sm init -> absorb ?eq ~init (missing sm a)))

  let map3_partial ?eq l ~by1 ~missing1 ~by2 ~missing2 ~f =
    fold_new l ~f:(fun init (is1, a) ->
      let k is2 b init =
        let k2 intercept c acc = mutate_or_add ?eq acc (intercept, f a b c) in
        set_assoc_k is2 by2 ~init ~k:k2
          ~missing:(fun sm init ->
            fold_left (missing2 sm a b) ~init ~f:(fun init (s, b) -> k2 s b init))
      in
      set_assoc_k is1 by1 ~init ~k
        ~missing:(fun sm init ->
          fold_left (missing1 sm a) ~init ~f:(fun init (s, b) -> k s b init)))

  let init_everything v =
    let nothing = AS.init () in
    singleton (AS.complement nothing) v

  let partition_map l ~f =
    let rec loop bs cs = function
      | Nil                     -> bs, cs
      | Cons {hd = (s, a); tl } ->
          match f s a with
          | `Fst b -> loop (cons (s, b) bs) cs tl
          | `Snd c -> loop bs (cons (s, c) cs) tl
    in
    loop Nil Nil l

end (* Make *)
