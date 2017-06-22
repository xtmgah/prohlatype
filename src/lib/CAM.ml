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

  (* TODO: Remove/Refactor this method. It is used for the case where set is
           just one allelle, but it doesn't make sense to return _one_ value
           from this map. *)
  val get_value : set -> 'a t -> 'a option

  exception Missing of string

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

module Interval : (sig

  type t = int * int

  val make : int -> int -> t

  val to_string : t -> string

  type inter_diff_res =
    | Before                  (* First interval comes completely before Second interval. *)
    | After                   (* First interval comes completely after Second interval. *)
    | Inter of inter          (* Intersection *)
  and rest =
    | B of t      (* Before the intersection. *)
    | A of t      (* After the intersection. *)
    | S of t * t  (* Split both before and after intersection. *)
    | E           (* Empty *)
  and inter =
    { i : t
    ; fst : rest
    ; snd : rest
    }

  (*val inter_diff : t -> t -> (t * t list * t list) option *)
  val inter_diff : t -> t -> inter_diff_res

  val extend : t -> int -> t option
  val merge : t -> t -> t option

end) = struct

  type t = int * int

  type inter_diff_res =
    | Before
    | After
    | Inter of inter
  and rest =
    | B of t
    | A of t
    | S of t * t
    | E
  and inter =
    { i : t
    ; fst : rest
    ; snd : rest
    }

  let make s1 e1 =
    if e1 < s1 then invalid_argf "Not in order %d < %d" e1 s1 else (e1, s1)

  let to_string (s, e) =
    sprintf "(%d,%d)" s e

  let inter_diff t1  t2 =
    let s1, e1 = t1 in
    let s2, e2 = t2 in
    if s1 = e1 then begin
    (* Handle the cases where the first interval is 1 wide to eliminate some
       corner cases. *)

      if s1 > s2 then begin                                           (* S2_1 *)
        if e2 < s1 then                                               (* E2_1 *)
          After
        else if e2 = s1 then                                          (* E2_2 *)
          Inter { i = t1; fst = E;  snd = B (s2, s1 - 1)                }
        else begin (* e2 > s1 *)                                      (* E2_3 *)
          Inter { i = t1; fst = E;  snd = S ((s2, s1 - 1), (e1 + 1, e2))}
        end

      end else if s1 = s2 then begin                                  (* S2_2 *)
        if e2 < s1 then                                               (* E2_1 *)
          invalid_argf  "broken invariant (%d,%d) (%d, %d)" s1 e1 s2 e2
        else if e2 = s1 then                                          (* E2_2 *)
          Inter { i = t1; fst = E;  snd = E }
        else begin (* e2 > s1 *)                                      (* E2_3 *)
          Inter { i = t1; fst = E;  snd = A (e1 + 1, e2) }
        end

      end else (*if s1 < s2 then *) begin                             (* S2_3 *)
        if e2 <= s1 then                                        (* E2_1, E2_2 *)
          invalid_argf  "broken invariant (%d,%d) (%d, %d)" s1 e1 s2 e2
        else begin (* e2 > s1 *)                                      (* E2_3 *)
          Before
        end
      end

    end else begin (* s1 < e1 *)
      if s1 > s2 then                                                 (* S2_1 *)
        if e2 < s1 then                                               (* E2_1 *)
          After
        else if (*e2 >= s1 && *) e2 < e1 then                   (* E2_2, E2_3 *)
          Inter { i = (s1, e2); fst = A (e2 + 1, e1); snd = B (s2, s1 - 1) }
        else if e2 = e1 then                                          (* E2_4 *)
          Inter { i = t1;       fst = E;              snd = B (s2, s1 - 1) }
        else (* e2 > e1 *)                                            (* E2_5 *)
          Inter { i = t1;       fst = E;              snd = S ((s2, s1 - 1), (e1 + 1, e2)) }

      else if s1 = s2 then                                            (* S2_2 *)
        if e2 < s1 then                                               (* E2_1 *)
          invalid_argf  "broken invariant (%d,%d) (%d, %d)" s1 e1 s2 e2
        else if (*e2 >= s1 && *) e2 < e1 then                   (* E2_2, E2_3 *)
          Inter { i = (s1, e2); fst = A (e2 + 1, e1); snd = E }
        else if e2 = e1 then                                          (* E2_4 *)
          Inter { i = t1;       fst = E;              snd = E }
        else (* e2 > e1 *)                                            (* E2_5 *)
          Inter { i = t1;       fst = E;              snd = A (e1 + 1, e2) }

      else if s1 < s2 && s2 < e1 then                                 (* S2_3 *)
        if e2 <= s1 then                                        (* E2_1, E2_2 *)
          invalid_argf  "broken invariant (%d,%d) (%d, %d)" s1 e1 s2 e2
        else if (*e2 > s1 && *) e2 < e1 then                          (* E2_3 *)
          Inter { i = t2;       fst = S ((s1, s2-1), (e2+1, e1)); snd = E }
        else if e2 = e1 then                                          (* E2_4 *)
          Inter { i = t2;       fst = B (s1, s2-1);               snd = E }
        else (* e2 > e1 *)                                            (* E2_5 *)
          Inter { i = (s2, e1); fst = B (s1, s2-1);               snd = A (e1 + 1, e2) }

      else if e1 = s2 then                                            (* S2_4 *)
        if e2 < e1 then                                   (* E2_1, E2_2, E2_3 *)
          invalid_argf  "broken invariant (%d,%d) (%d, %d)" s1 e1 s2 e2
        else if e2 = e1 then                                          (* E2_4 *)
          Inter { i = t2;       fst = B (s1, s2 - 1); snd = E }
        else (* e2 > e1 *)                                            (* E2_5 *)
          Inter { i = (s2, e1); fst = B (s1, s2 - 1); snd = A (e1 + 1, e2)  }

      else (*if e1 < s2 then *)                                       (* S2_5 *)
        if e2 <= e1 then                            (* E2_1, E2_2, E2_3, E2_4 *)
          invalid_argf  "broken invariant (%d,%d) (%d, %d)" s1 e1 s2 e2
        else (* e2 > e1 *)                                            (* E2_5 *)
          Before
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

module Make (Aset : Alleles.Set) : M = struct

  let intervals_of_allele_set set =
    Aset.fold_set_indices set ~init:None ~f:(fun a i ->
      match a with
      | None                -> Some (Interval.make i i, [])
      | Some (interval, l)  ->
          match Interval.extend interval i with
          | None    -> Some (Interval.make i i, interval :: l)
          | Some ni -> Some (ni, l))
    |> function
        | None        -> []                (* Only if empty *)
        | Some (i, l) -> List.rev (i :: l)

  let interval_to_allele_set (st, en) =
    let i = Aset.index in
    let rec loop j s =
      if j > en then s else loop (j + 1) (Aset.set s i.Alleles.to_allele.(j))
    in
    loop st (Aset.init ())

  type 'a mlist = 'a cell option
  and 'a cell =
    { value         : 'a
    ; set           : Interval.t
    ; mutable prev  : 'a cell
    ; mutable next  : 'a cell
    }

  type 'a t = 'a mlist

  let empty = None

  let allele_set_to_string s = Aset.to_human_readable s

  let interval_set_to_string i =
    allele_set_to_string (interval_to_allele_set i)

  let rec forward_loop endc f cell acc =
    let nacc = f acc cell.set cell.value in
    if cell.next != endc then
      forward_loop endc f cell.next nacc
    else
      nacc

  let rec backward_loop endc f cell acc =
    let nacc = f cell.set cell.value acc in
    if cell.prev != endc then
      backward_loop endc f cell.prev nacc
    else
      nacc

  let fold_left ~init ~f = function
    | None      -> init
    | Some cell -> forward_loop cell f cell init

  let fold_right lst ~init ~f =
    match lst with
    | None      -> init
    | Some cell -> backward_loop cell f cell init

  let sc set value =
    let rec c = { value; set; prev = c; next = c} in
    c

  let map ~f = function
    | None      -> empty
    | Some cell ->
        let first = sc cell.set (f cell.value) in
        let newf prev set value =
          let nc = sc set (f value) in
          nc.prev <- prev;
          prev.next <- nc;
          nc
        in
        let last = forward_loop cell newf cell first in
        first.prev <- last;
        last.next <- first;
        Some first

  let to_list lst = fold_right ~init:[] ~f:(fun s v l -> (s,v) :: l) lst

  let to_string t =
    String.concat ~sep:"\n\t"
      (List.map (to_list t) ~f:(fun (s,_v) ->
        sprintf "%s" (interval_set_to_string s)))

  let to_string_full v_to_s t =
    String.concat ~sep:"\n\t"
      (List.map (to_list t) ~f:(fun (s,v) ->
        sprintf "%s:%s" (interval_set_to_string s) (v_to_s v)))

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

  let insert nc c =
    let last = c.prev in
    nc.prev <- last;
    last.next <- nc;
    nc.next <- c;
    c.prev <- nc

  (* Add to end *)
  let append set value l = match l with
    | None   -> Some (sc set value)
    | Some c -> let nc = sc set value in
                insert nc c;
                l

  (* Add to beginning, since circular the difference is only what is returned. *)
  let prepend set value = function
    | None   -> Some (sc set value)
    | Some c -> let nc = sc set value in
                insert nc c;
                Some nc

(* let mutate_or_add ?eq lst alleles value =
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
    | Cons c  -> loop c; lst *)


  let add ?eq alleles value l = append alleles value l

  let singleton set value = Some (sc set value)

  let of_list ?eq l =
    List.fold_left l ~init:empty
      ~f:(fun acc (set, value) -> append set value acc)

  let of_allele_set s v =
    of_list (List.map ~f:(fun i -> (i, v)) (intervals_of_allele_set s))

  (*let to_list l = l *)

  let join ?eq l1 l2 =
    fold_left l1 ~init:l2 ~f:(fun l set value -> append set value l)

  (*let domain = function
    | Nil     -> Aset.init ()
    | Cons { hd = (init, _) ; tl } ->
                  fold_left ~init ~f:(fun u s _ -> Aset.union u s) tl*)

  let length l =
    fold_left ~init:0 ~f:(fun s _ _ -> s + 1) l

  exception Missing of string

  let missingf fmt =
    ksprintf (fun s -> raise (Missing s)) fmt

  let still_missing f s =
    missingf "%s %s to find alleles: %s"
      (Interval.to_string f) (Interval.to_string s)
      (interval_set_to_string f)

  type 'a find_res =
    | Everything of 'a
    | Rest of (Interval.t * Interval.t list * 'a)

  let find to_find rest ~within ~f ~init =
    let open Interval in
    let rec loop find_me rest acc set =
      match inter_diff find_me set with
      | Before                -> still_missing find_me set
      | After                 -> Rest (find_me, rest, acc)
      | Inter { i; fst; snd } ->
          (*let nacc = append i c.value acc in *)
          let nacc = f i acc in
          match snd with
          | E | B _           -> (* Nothing left so continue fold. *)
            begin match fst with
              | S (m, _)
              | B m                     -> still_missing m set
              | A nfind_me              -> Rest (nfind_me, rest, nacc)
              | E                       ->
                  begin match rest with
                    | []                -> Everything nacc
                    | nfind_me :: nrest -> Rest (nfind_me, nrest, nacc)
                  end
            end
          | S (_, a)
          | A a ->
              begin match fst with
                | S (m, _) (* Case not possible, but for patter matching. *)
                | B m                      -> still_missing m set
                | A _                      -> assert false
                | E                        ->
                    begin match rest with
                      | []                 -> Everything nacc
                      | nto_find  :: nrest -> loop nto_find nrest nacc a
                    end
              end
    in
    loop to_find rest init within

  let get_exn (type a) set l =
    let module M = struct exception Found of a t end in
    match intervals_of_allele_set set with
    | []               -> empty
    | find_me :: rest  ->
      try
        let still_to_find, _, _ =
          fold_left l ~init:(find_me, rest, empty)
            ~f:(fun (find_me, rest, init) within value ->
                  let fr = 
                    find find_me rest ~within ~init
                      ~f:(fun intersect acc -> append intersect value acc)
                  in
                  match fr with
                  | Everything nacc   -> raise (M.Found nacc)
                  | Rest (fm, re, ac) -> (fm, re, ac))
        in
        missingf "didn't find: %s" (interval_set_to_string still_to_find)
      with M.Found s -> s

  let get set l =
    match get_exn set l with
    | exception Missing _ -> None
    | v                   -> Some v

  let get_value s t =
    Option.bind (get s t) ~f:(function
      | Some { value; _} -> Some value
      | _                -> None)

  let iter l ~f =
    fold_left ~init:() ~f:(fun () set value -> f set value) l

  let iter_values l ~f =
    iter l ~f:(fun set value ->
      Aset.iter_set_indices (interval_to_allele_set set)
        ~f:(fun i -> f i value))

  let fold = fold_left

  (*let absorb ?eq t ~init = fold_left t ~init ~f:(mutate_or_add ?eq) 

  let fold_new ~f l = fold_left ~init:Nil ~f l
*)

  let concat_map ?eq l ~f =
    failwith "NI"
    (* fold_new l ~f:(fun init s a -> absorb ?eq (f s a) ~init) *)

  (* The order of set arguments matters for performance. Better to fold over
     the longer list and lookup (set_assoc_k) into the shorter one. Remember
     that the lookup requires a Allele.inter_diff per item! Perhaps it makes
     sense to keep track of the length to avoid O(n) lookups and then
     automatically re-order functional arguments as necessary?

     Probably just need a better data structure. *)

  let concat_map2_partial ?eq l ~by ~f ~missing =
    failwith "NI"
    (* fold_new l ~f:(fun init s a ->
      set_assoc_k s by ~init
        ~k:(fun intersect b init -> absorb ?eq (f intersect a b) ~init)
        ~missing:(fun sm init -> absorb ?eq ~init (missing sm a))) *)

  let map2_gen l1 l2 ~f =
    let dd () = invalid_argf "map: Different domains." in
    match l1, l2 with
    | None,   None    -> None
    | Some _, None
    | None,   Some _  -> dd ()
    | Some a, Some b  ->
        let open Interval in
        let step cs cv ds dv acc =
          match inter_diff cs ds with
          | Before
          | After                 -> dd ()
          | Inter {i; fst; snd }  ->
              let nacc = f i cv dv acc in
              match fst, snd with
              | B _, _
              | S _, _
              | _,   B _
              | _,   S _  -> dd ()
              | E,   E    -> `Full nacc
              | A a, E    -> `First (a, nacc)
              | E,   A a  -> `Second (a, nacc)
              | A _, A _  -> assert false
        in
        let rec loop cs cv cn ds dv dn acc =
          match step cs cv ds dv acc with
          | `Full acc           ->
            if cn == a && dn == b then
              acc (* Done *)
            else if cn <> a && dn <> b then
              loop cn.set cn.value cn.next dn.set dn.value dn.next acc
            else
              dd ()
          | `First (csr, acc)   ->
              if dn <> b then
                loop csr cv cn dn.set dn.value dn.next acc
              else
                dd ()
          | `Second (dsr, acc)  ->
              if cn <> a then
                loop cn.set cn.value cn.next dsr dv dn acc
              else
                dd ()
        in
        loop a.set a.value a.next b.set b.value b.next None

  let map2 ?eq l1 l2 ~f =
    map2_gen l1 l2 ~f:(fun intersect value1 value2 acc ->
      append intersect (f value1 value2) acc)

  let concat_map2 ?eq l ~by ~f =
      map2_gen l by ~f:(fun intersect value1 value2 acc ->
        append intersect (f value1 value2) acc)



  let map3 ?eq l1 l2 l3 ~f =
    map2 ?eq l3 (map2 ?eq l1 l2 ~f:(fun a b -> (a, b)))
      ~f:(fun c (a, b) -> f a b c)
    
  let map2_partial ?eq l ~by ~missing ~f =
    failwith "NI"
    (*fold_new l ~f:(fun init s a ->
      set_assoc_k s by ~init
        ~k:(fun intercept b acc -> mutate_or_add ?eq acc intercept (f a b))
        ~missing:(fun sm init -> absorb ?eq ~init (missing sm a)))*)

  let map3_partial ?eq l ~by1 ~missing1 ~by2 ~missing2 ~f =
    failwith "NI"
    (* fold_new l ~f:(fun init is1 a ->
      let k is2 b init =
        let k2 intercept c acc = mutate_or_add ?eq acc intercept (f a b c) in
        set_assoc_k is2 by2 ~init ~k:k2
          ~missing:(fun sm init ->
            fold_left (missing2 sm a b) ~init ~f:(fun init s b -> k2 s b init))
      in
      set_assoc_k is1 by1 ~init ~k
        ~missing:(fun sm init ->
          fold_left (missing1 sm a) ~init ~f:(fun init s b -> k s b init)))*)

  let init_everything v =
    let nothing = Aset.init () in
    let everything = Aset.complement nothing in
    of_allele_set everything v

  let partition_map l ~f =
    failwith "NI"
    (* let rec loop bs cs = function
      | Nil                     -> bs, cs
      | Cons { set; value; tl } ->
          match f set value with
          | `Fst b -> loop (cons set b bs) cs tl
          | `Snd c -> loop bs (cons set c cs) tl
    in
    loop Nil Nil l *)

end (* Make *)
