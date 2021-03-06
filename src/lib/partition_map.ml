(** A partition map is a data structure for a map over a partition of a set.

  The integer intervals are stored in a sorted order, so that finding
  intersections and merging can be accomplised by traversing the lists in the
  same order. *)

open Util

module Interval : sig

  type t

  val compare : t -> t -> int

  val make : int -> int -> t

  val extend_one : t -> t

  val width : t -> int

  val inside : int -> t -> bool

  val start : t -> int

  val end_ : t -> int

  val to_string : t -> string

  val is_none : t -> bool

  val strict_before : t -> t -> bool

  val before_separate : t -> t -> bool

  val merge : t -> t -> t

  val split_inter_diff2 : t -> t ->
                          t * t * t * t * t
  val split_inter_diff3 : t -> t -> t ->
                          t * t * t * t * t * t * t
  val split_inter_diff4 : t -> t -> t -> t ->
                          t * t * t * t * t * t * t * t * t

  val aligned_inter_diff2 : t -> t ->
                            t * t * t
  val aligned_inter_diff3 : t -> t -> t ->
                            t * t * t * t
  val aligned_inter_diff4 : t -> t -> t -> t ->
                            t * t * t * t * t

  val fold : t -> init:'a -> f:('a -> int -> 'a) -> 'a

  val iter : t -> f:(int -> unit) -> unit

end = struct

(* Start will occupy the higher order bits. This way a comparison can test
 * for equality (the most common case) and determine the Before/After path
 * without looking at end.
 *
 * This means that the new range must start at 1 and 0 is no longer a valid
 * element in our partition. We'll use 0 to encode a None
 *)
type t = int [@@deriving ord]

let none_t = 0

let is_none t =
  t = none_t

(* Masks *)
let lower32 = 4294967295
let upper32 = -4294967296

let start_of_int i =
   (i lsl 32)

let int_of_start  i =
  ((i land upper32) lsr 32)

let start_p t =
  t land upper32

let end_of_int i =
  i

let int_of_end i =
  i

let end_p t =
  t land lower32

let make64 s e =
  s lor e

let start_of_end e =
  start_of_int (int_of_end e)

let end_of_start s =
  end_of_int (int_of_start s)

(* Interfacing to ints *)
let start t =
  (int_of_start (start_p t)) - 1

let end_ t =
  (int_of_end (end_p t)) - 1

let width t =
  (end_ t) - (start t) + 1

let inside i t =
  (start t) <= i && i <= (end_ t)

let to_string t =
  sprintf "(%d,%d)" (start t) (end_ t)

let make s e =
  if e < s then
    invalid_argf "Not in order %d < %d" e s
  else if e < 0 then
    invalid_argf "End %d less than 0" e
  else if s < 0 then
    invalid_argf "Start %d less than 0" e
  else
    let s64 = start_of_int (s + 1) in
    let e64 = end_of_int (e + 1) in
    make64 s64 e64

let extend_one t =
  succ t

let merge t1 t2 =
  let s1 = start_p t1 in
  let s2 = start_p t2 in
  let e1 = end_p t1 in
  let e2 = end_p t2 in
  if succ e1 = (end_of_start s2) then
    make64 s1 e2
  else if succ e2 = (end_of_start s1) then
    make64 s2 e1
  else
    none_t

let merge3 t1 t2 t3 =
  let p1d = merge t1 t2 in
  if is_none p1d then
    none_t
  else
    merge p1d t3

let merge_exn t1 t2 =
  let m = merge t1 t2 in
  if is_none m then
    invalid_argf "not merge-able %s %s"
      (to_string t1) (to_string t2)
  else
    m

let prep p1 p2 =
  if is_none p1 then
    p2
  else if is_none p2 then
    p1
  else
    make64 (start_p p1) (end_p p2)

let strict_before t1 t2 =
  t1 < t2 && (end_p t1) < (end_of_start (start_p t2))

(* This is a very dangerous method, you better be sure that the intervals
 * are separate! *)
let before_separate t1 t2 =
  t1 < t2

let split_inter_diff2 t1 t2 =
  if t1 = t2 then
    (* EmptyEmpty *) none_t, none_t, t1,  none_t, none_t
    (* Only works if s1, s2 < 2^31 otherwise t1, t2 is negative. *)
  else if t1 < t2 then (* s1 <= s2 *)
    begin
      let s1 = start_p t1 in
      let s2 = start_p t2 in
      let e1 = end_p t1 in
      let e2 = end_p t2 in
      if s1 = s2 then (* -> e1 < e2 ----> s1 = s2 <= e1 < e2 *)
        let after = make64 (start_of_end (succ e1)) e2 in
        (* EmptyAfter *)none_t, none_t, t1, none_t, after
      else (* s1 < s2 --------> e1 ? e2  we don't know!*)
        begin
          if e1 = e2 then (* -------> s1 < e1 = s2 = e2 *)
            let before = make64 s1 (pred (end_of_start s2)) in
            (* BeforeEmpty *) before, none_t, t2,  none_t, none_t
          else if e1 < e2 (* ----- s1 <= e1 ? s2 <= e2 *) then
            begin
              if e1 < end_of_start s2 then (* s1 <= e1 < s2 <= e2 *)
                (* Before *) t1, none_t, none_t, none_t, t2
              else (* e1 >= s2 --------> s1 < s2 <= e1 < e2 *)
                let before = make64 s1 (pred (end_of_start s2)) in
                let inter  = make64 s2 e1 in
                let after  = make64 (start_of_end (succ e1)) e2 in
                (* BeforeAfter *) before, none_t, inter,  none_t, after
            end
          else (* e1 > e2    ----- s1 < s2 <= e2 < e1 *)
            let before = make64 s1 (pred (end_of_start s2)) in
            let after  = make64 (start_of_end (succ e2)) e1 in
            (* SplitEmpty *) before, none_t, t2,  after,  none_t
        end
    end
  else (* t1 > t2 ------------ s1 >= s2  --- s2 <= s1 *)
    begin
      let s1 = start_p t1 in
      let s2 = start_p t2 in
      let e1 = end_p t1 in
      let e2 = end_p t2 in
      if s1 = s2 then (* --> e1 > e2 -- e2 < e1  ---- s1 = s2 <= e2 < e1*)
        let after = make64 (start_of_end (succ e2)) e1 in
        (* AfterEmpty *) none_t, none_t, t2,  after,  none_t
      else (* s1 > s2  --- s2 < s1 --> e2 < e1 *)
        begin
          if e1 = e2 then (* -----> s2 < s1 = e1 = e2 *)
            let before = make64 s2 (pred (end_of_start s1)) in
            (* EmptyBefore *) none_t, before, t1,  none_t, none_t
          else if e1 > e2 then (* e2 < e1 ----> s2 <= e2 ? s1 <= e1 *)
            begin
              if e2 < end_of_start s1 then (* s2 <= e2 < s1 <= e2 *)
                (* After *)  none_t, t2,     none_t, t1,     none_t
              else
                let before = make64 s2 (pred (end_of_start s1)) in
                let inter  = make64 s1 e2 in
                let after  = make64 (start_of_end (succ e2)) e1 in
                (* AfterBefore *) none_t, before, inter,  after,  none_t
            end
          else (* e1 < e2       s2 <= s1 <= e1 < e2 *)
            let before = make64 s2 (pred (end_of_start s1)) in
            let after  = make64 (start_of_end (succ e1)) e2 in
            (* EmptySplit *) none_t, before, t1,  none_t, after
        end
    end

let split_inter_diff3 i1 i2 i3 =
  let b1, b2, i, a1, a2 = split_inter_diff2 i1 i2 in
  if is_none i then
    b1, b2, none_t, i, a1, a2, i3
  else
    let b12, b3, i123, a12, a3 = split_inter_diff2 i i3 in
    prep b1 b12,
    prep b2 b12,
    b3,
    i123,
    prep a12 a1,
    prep a12 a2,
    a3

let split_inter_diff4 i1 i2 i3 i4 =
  let b1, b2, b3, i, a1, a2, a3 = split_inter_diff3 i1 i2 i3 in
  if is_none i then
    b1, b2, b3, none_t, i, a1, a2, a3, i4
  else
    let b123, b4, i1234, a123, a4 = split_inter_diff2 i i4 in
    prep b1 b123,
    prep b2 b123,
    prep b3 b123,
    b4,
    i1234,
    prep a123 a1,
    prep a123 a2,
    prep a123 a3,
    a4

let aligned_inter_diff2 t1 t2 =
  if t1 = t2 then
    t1, none_t, none_t    (* EmptyEmpty *)
  (* Only works if s1, s2 < 2^31 otherwise t1, t2 is negative. *)
  else if t1 < t2 then (* s1 = s2 -> e1 < e2 *)
    let e1 = end_p t1 in
    let e2 = end_p t2 in
    let after = make64 (start_of_end (succ e1)) e2 in
    t1, none_t, after     (* EmptyAfter *)
  else (* t1 > t2 ----    s1 = s2 -> e1 > e2 *)
    let e1 = end_p t1 in
    let e2 = end_p t2 in
    let after = make64 (start_of_end (succ e2)) e1 in
    t2, after, none_t     (* AfterEmpty *)

let aligned_inter_diff3 i1 i2 i3 =
  let i, m1, m2 = aligned_inter_diff2 i1 i2 in
  let ni, ma, m3 = aligned_inter_diff2 i i3 in
  ni, prep ma m1, prep ma m2, m3

let aligned_inter_diff4 i1 i2 i3 i4 =
  let i, m1, m2, m3 = aligned_inter_diff3 i1 i2 i3 in
  let ni, ma, m4 = aligned_inter_diff2 i i4 in
  ni, prep ma m1, prep ma m2, prep ma m3, m4

let iter t ~f =
  for i = (start t) to (end_ t) do f i done

let fold t ~init ~f =
  let acc = ref init in
  for i = (start t) to (end_ t) do acc := f !acc i done;
  !acc

end (* Interval *)

module Set = struct

  type t = Interval.t list

  let of_interval i =                 (* This isn't the cleanest abstraction ... *)
    if Interval.is_none i then
      []
    else
      [i]

  let invariant =
    let open Interval in
    let rec loop = function
      | []  -> true
      | h :: [] -> true
      | h1 :: h2 :: t ->
          if strict_before h1 h2 then
            loop (h2 :: t)
          else
            false
    in
    loop

  let to_string  =
    string_of_list ~sep:";" ~f:(fun i -> sprintf "%s" (Interval.to_string i))

  let size = List.fold_left ~init:0 ~f:(fun a i -> a + Interval.width i)

  let inside i l =
    List.exists l ~f:(Interval.inside i)

  let universal = function
    | [i] -> true
    | _   -> false

  let compare s1 s2 =
    match s1, s2 with
    | i1 :: _ , i2 :: _ -> Interval.compare i1 i2
    | _                 -> assert false

  (* Should I make the sets a real pair? *)
  let first_pos = function
    | []      -> assert false
    | s :: _  -> Interval.start s

  let cons_if_nnone o l =
    if Interval.is_none o then l else o :: l

  (* The elements in a set are ordered.  *)
  let split_if_in ii l =
    let open Interval in
    let rec loop = function
      | []      -> None, []
      | h :: t  ->
          let b1, b2, i, a1, a2 = split_inter_diff2 ii h in
          if Interval.is_none i then begin
            if h = a1 then (* After *)
              let o, nt = loop t in
              o, h :: nt
            else (* Before *)
              None, l
          end else
            Some (of_interval b2), (cons_if_nnone a2 t)
    in
    loop l

  (* Zip together two non-intersecting (separate) sets. *)
  let merge_separate =
    let open Interval in
    let rec start l1 l2 = match l1, l2 with
      | _,  []            -> l1
      | [], _             -> l2
      | h1 :: t1
      , h2 :: t2 ->
          if before_separate h1 h2 then
            loop h1 t1 l2
          else
            loop h2 l1 t2
    and loop ps l1 l2 = match l1, l2 with
      | [],       []        ->  [ps]
      | h1 :: t1, []        ->  let m1 = merge ps h1 in
                                if is_none m1 then
                                   ps :: l1
                                else
                                   loop m1 t1 []
      | [],       h2 :: t2  ->  let m2 = merge ps h2 in
                                if is_none m2 then
                                  ps :: l2
                                else
                                  loop m2 [] t2
      | h1 :: t1, h2 :: t2  ->
          if before_separate h1 h2 then begin
            let m1 = merge ps h1 in
            if is_none m1 then
              ps :: loop h1 t1 l2
            else
              loop m1 t1 l2
          end else begin
            let m2 = merge ps h2 in
            if is_none m2 then
              ps :: loop h2 l1 t2
            else
              loop m2 l1 t2
          end
    in
    start

  let all_intersections =
    let open Interval in
    let rec loop l1 l2 = match l1, l2 with
      | _,  []                                   -> [],           l1,              l2
      | [], _                                    -> [],           l1,              l2
      | h1 :: t1
      , h2 :: t2 ->
        let b1, b2, inter, a1, a2 = split_inter_diff2 h1 h2 in
        let i, r1, r2 = loop (cons_if_nnone a1 t1) (cons_if_nnone a2 t2) in
        (cons_if_nnone inter i) , (cons_if_nnone b1 r1) , (cons_if_nnone b2 r2)
    in
    loop

  let must_match_at_beginning s1 s2 =
    match s1, s2 with
    | [], []  -> invalid_argf "Empty sets!"
    | [], s   -> invalid_argf "Different lengths! s2: %s" (to_string s)
    | s , []  -> invalid_argf "Different lengths! s1: %s" (to_string s)
    | h1 :: t1
    , h2 :: t2 ->
      let open Interval in
      let inter, m1, m2 = aligned_inter_diff2 h1 h2 in
      let i, r1, r2 = all_intersections (cons_if_nnone m1 t1) (cons_if_nnone m2 t2) in
      (inter :: i), r1, r2

  let all_intersections3 =
    let rec loop l1 l2 l3 = match l1, l2, l3 with
      | [],  _,  _
      |  _, [],  _
      |  _,  _, []  -> [], l1, l2, l3
      | h1 :: t1
      , h2 :: t2
      , h3 :: t3    ->
        let b1, b2, b3, i, a1, a2, a3 = Interval.split_inter_diff3 h1 h2 h3 in
        let nt1 = cons_if_nnone a1 t1 in
        let nt2 = cons_if_nnone a2 t2 in
        let nt3 = cons_if_nnone a3 t3 in
        let il, r1, r2, r3 = loop nt1 nt2 nt3 in
        cons_if_nnone i il
        , cons_if_nnone b1 r1
        , cons_if_nnone b2 r2
        , cons_if_nnone b3 r3
    in
    loop

  let must_match_at_beginning3 s1 s2 s3 =
    match s1, s2, s3 with
    | [],  _,  _  -> invalid_argf "Empty 1"
    |  _, [],  _  -> invalid_argf "Empty 2"
    |  _,  _, []  -> invalid_argf "Empty 3"
    | h1 :: t1
    , h2 :: t2
    , h3 :: t3    ->
        let inter, ho1, ho2, ho3 = Interval.aligned_inter_diff3 h1 h2 h3 in
        let nt1 = cons_if_nnone ho1 t1 in
        let nt2 = cons_if_nnone ho2 t2 in
        let nt3 = cons_if_nnone ho3 t3 in
        let il, r1, r2, r3 = all_intersections3 nt1 nt2 nt3 in
        inter :: il, r1, r2, r3

  let all_intersections4 =
    let rec loop l1 l2 l3 l4 = match l1, l2, l3, l4 with
      | [],  _,  _,  _
      |  _, [],  _,  _
      |  _,  _, [],  _
      |  _,  _,  _, []  -> [], l1, l2, l3, l4
      | h1 :: t1
      , h2 :: t2
      , h3 :: t3
      , h4 :: t4        ->
        let b1, b2, b3, b4, i, a1, a2, a3, a4 = Interval.split_inter_diff4 h1 h2 h3 h4 in
        let nt1 = cons_if_nnone a1 t1 in
        let nt2 = cons_if_nnone a2 t2 in
        let nt3 = cons_if_nnone a3 t3 in
        let nt4 = cons_if_nnone a4 t4 in
        let il, r1, r2, r3, r4 = loop nt1 nt2 nt3 nt4 in
        cons_if_nnone i il
        , cons_if_nnone b1 r1
        , cons_if_nnone b2 r2
        , cons_if_nnone b3 r3
        , cons_if_nnone b4 r4
    in
    loop

  let must_match_at_beginning4 s1 s2 s3 s4 =
    match s1, s2, s3, s4 with
    | [],  _,  _,  _ -> invalid_argf "Empty 1"
    |  _, [],  _,  _ -> invalid_argf "Empty 2"
    |  _,  _, [],  _ -> invalid_argf "Empty 3"
    |  _,  _,  _, [] -> invalid_argf "Empty 4"
    | h1 :: t1
    , h2 :: t2
    , h3 :: t3
    , h4 :: t4 ->
        let inter, ho1, ho2, ho3, ho4 = Interval.aligned_inter_diff4 h1 h2 h3 h4 in
        let nt1 = cons_if_nnone ho1 t1 in
        let nt2 = cons_if_nnone ho2 t2 in
        let nt3 = cons_if_nnone ho3 t3 in
        let nt4 = cons_if_nnone ho4 t4 in
        let il, r1, r2, r3, r4 = all_intersections4 nt1 nt2 nt3 nt4 in
        inter :: il, r1, r2, r3, r4

  let fold t ~init ~f =
    List.fold_left t ~init ~f:(fun init interval ->
      Interval.fold interval ~init ~f)

  let iter t ~f =
    fold t ~init:() ~f:(fun () i -> f i)

end (* Set *)

type ascending  (*= Ascending*)
type descending (*= Descending*)

(* Things start out in descending order when we construct the partition, but
  when we 'reverse' it they are constructed into an ascending order that is
  better for merging. *)

type +'a asc =
  | E                       (* empty, merging against this will fail! *)
  | U of Set.t * 'a           (* universal, hold size - 1 = end_ *)
  | S of (Set.t * 'a) list

type +'a desc = (Interval.t * 'a) list

type (_, +'a) t =
  | Asc   : 'a asc -> (ascending, 'a) t
  | Desc  : 'a desc -> (descending, 'a) t

let ascending_invariant =
  let rec loop = function
    | []           -> false             (* fail? don't expect empty lists *)
    | (s, _) :: [] -> Set.invariant s
    | (s1, _) :: (s2, v) :: t ->
        Set.invariant s1
        && Set.first_pos s1 < Set.first_pos s2
        && loop ((s2, v) :: t)
  in
  loop

let invariant : type o a. (o, a) t -> bool =
  function
    | Asc E      -> true
    | Asc U _    -> true
    | Asc (S la) -> ascending_invariant la
    | Desc _     -> true                               (* being a bit lazy atm. *)

(* Empty Constructors *)
let empty_d = Desc []
let empty_a = Asc E

(* Initializers *)
let init_first_d v =
  let i = Interval.make 0 0 in
  Desc [i, v]

let init_all_a ~size v =
  let i = Interval.make 0 (size - 1) in
  Asc (U (Set.of_interval i, v))

(* Properties *)
let asc_to_string la to_s =
  string_of_list la ~sep:"; " ~f:(fun (s, v) ->
      sprintf "[%s]:%s" (Set.to_string s) (to_s v))

let desc_to_string ld to_s =
  string_of_list ld ~sep:";" ~f:(fun (i, v) ->
    sprintf "%s:%s" (Interval.to_string i) (to_s v))

let to_string: type o a. (o, a) t -> (a -> string) -> string =
  fun t to_s -> match t with
    | Asc E         -> "Empty!"
    | Asc (U (s,v)) -> sprintf "%s:%s" (Set.to_string s) (to_s v)
    | Asc (S l)     -> asc_to_string l to_s
    | Desc ld       -> desc_to_string ld to_s

let size_a = List.fold_left ~init:0 ~f:(fun a (s, _) -> a + Set.size s)

let size_d = function
  | []            -> 0
  | ((i, _) :: _) -> Interval.end_ i + 1

let size : type o a. (o, a) t -> int = function
  | Asc E          -> 0
  | Asc (U (s, _)) -> Set.size s
  | Asc (S l)      -> size_a l
  | Desc l         -> size_d l

let length : type o a. (o, a) t -> int = function
  | Asc E     -> 0
  | Asc (U _) -> 1
  | Asc (S l) -> List.length l
  | Desc l    -> List.length l

let assoc_remove_and_get el list =
  let rec loop acc = function
    | []                      -> None
    | (e, v) :: t when e = el -> Some (v, (List.rev acc @ t))
    | h :: t                  -> loop (h :: acc) t
  in
  loop [] list

(* Conversion *)

(* [merge_or_add_to_end eq s v l] rebuild the elements of [l] such that if
   any of the values (snd) [eq v] then merge the sets [s] and (fst). If no
   values are equal add to the end of l. *)
let merge_or_add_to_end eq s v l =
  let rec loop = function
    | []     -> [s, v]
    | h :: t ->
        let s0, v0 = h in
        if eq v v0 then
          (Set.merge_separate s0 s, v0) :: t
        else
          h :: loop t
  in
  loop l

let map_with_full_check eq l ~f =
  List.fold_left l ~init:[] ~f:(fun acc (s, v) ->
      merge_or_add_to_end eq s (f v) acc)

let ascending_t eq l =
  List.fold_left l ~init:[] ~f:(fun acc (i, v) ->
    merge_or_add_to_end eq (Set.of_interval i) v acc)
  |> List.sort ~cmp:(fun (s1, _) (s2, _) -> Set.compare s1 s2)

let asc_sets_to_str s =
  asc_to_string s (fun _ -> "")

let ascending eq = function
  | Desc l ->
    let a = ascending_t eq l in                             (* assert (ascending_invariant l); *)
    match a with
    | []      -> invalid_arg "Empty descending!"
    | [s,v]   -> if Set.universal s then
                   Asc (U (s, v))
                 else
                  invalid_argf "Single set but not universal? %s" (Set.to_string s)
    | lst     -> Asc (S lst)

let descending = function
  | Asc E          -> invalid_arg "Can't convert empty to descending"
  | Asc (U (s, v)) -> Desc [List.hd_exn s, v]
  | Asc (S l)      ->
      List.map l ~f:(fun (s, v) -> List.map s ~f:(fun i -> i, v))
      |> List.concat
      |> List.sort ~cmp:(fun (i1, _) (i2, _) -> Interval.compare i2 i1)
      |> fun l -> Desc l

(* Getters/Setters *)
let add v = function
  | Desc []                         -> Desc ((Interval.make 0 0, v) :: [])
  | Desc ((s, ov) :: t) when v = ov -> Desc ((Interval.extend_one s, v) :: t)
  | Desc (((s, _) :: _) as l)       -> let e = 1 + Interval.end_ s in
                                       Desc ((Interval.make e e, v) :: l)


let get t i = match t with
  | Asc E          -> invalid_arg "Can't get from empty"
  | Asc (U (_, v)) -> v
  | Asc (S l)      ->
      let rec loop = function
        | []          -> raise Not_found      (* Need a better failure mode. *)
        | (s, v) :: t ->
            if Set.inside i s then
              v
            else
              loop t
      in
      loop l

let set t i v = match t with
  | Asc E          -> invalid_arg "Can't set from empty"
  | Asc (U (s, _)) -> Asc (U (s, v))
  | Asc (S l)      ->
    let open Interval in
    let ii = make i i in
    let rec loop l = match l with
      | []      -> raise Not_found
      | h :: t  ->
          let s, ov = h in
          if v = ov && Set.inside i s then              (* No use splitting *)
            l
          else
            match Set.split_if_in ii s with
            | None,    _     -> h :: loop t
            | Some [], after -> (Set.of_interval ii, v) :: (after, ov) :: t
            (* Technically this isn't scanning l again to find the
               appropriate set for {v}, we're just inserting it and maintaing
               the invariant that the sets inside are ordered.
               I'm not actually using this method in ParPHMM so I'll avoid
               a better implementation for now. *)
            | Some be, after -> (be @ after, ov) :: (Set.of_interval ii, v) :: t
    in
    Asc (S (loop l))

let insert s v l =
  let sl = Set.first_pos s in
  let rec loop l = match l with
    | []     -> [s, v]
    | h :: t -> let so, _ = h in
                if sl < Set.first_pos so then
                  (s, v) :: l
                else
                  h :: loop t
  in
  loop l

let insert_if_not_empty s v l =
  if s = [] then
    l
  else
    insert s v l

let map_with_just_last_check ~f = function
  | []  -> []
  | (s,v) :: t ->
    let rec loop ps pv = function
      | []         -> [ps, pv]
      | (s,v) :: t ->
          let nv = f v in
          if nv = pv then
            loop (Set.merge_separate ps s) pv t
          else
            (ps, pv) :: loop s nv t
    in
    loop s (f v) t

(* The reason for all this logic. *)
let rec start2 eq f l1 l2 = match l1, l2 with
  | [],     []      -> []
  | [],      s      -> invalid_argf "Different lengths! l2: %s" (asc_sets_to_str s)
  |  s,     []      -> invalid_argf "Different lengths! l1: %s" (asc_sets_to_str s)
  | (s1, v1) :: t1
  , (s2, v2) :: t2  ->
      let intersect, r1, r2 = Set.must_match_at_beginning s1 s2 in
      let nt1 = insert_if_not_empty r1 v1 t1 in
      let nt2 = insert_if_not_empty r2 v2 t2 in
      let acc = [intersect, (f v1 v2)] in
      loop2 eq f acc nt1 nt2
and loop2 eq f acc l1 l2 = match l1, l2 with
  | [],     []      -> acc
  | [],      s      -> invalid_argf "Different lengths! l2: %s" (asc_sets_to_str s)
  |  s,     []      -> invalid_argf "Different lengths! l1: %s" (asc_sets_to_str s)
  | (s1, v1) :: t1
  , (s2, v2) :: t2  ->
      let intersect, r1, r2 = Set.must_match_at_beginning s1 s2 in
      let nt1 = insert_if_not_empty r1 v1 t1 in
      let nt2 = insert_if_not_empty r2 v2 t2 in
      let nv = f v1 v2 in
      let nacc = merge_or_add_to_end eq intersect nv acc in
      loop2 eq f nacc nt1 nt2
(* TODO: There is a bug here where I'm not checking for matching ends.
  * I should functorize or somehow parameterize the construction of these
  * such that I don't worry about this. *)
and merge ~eq t1 t2 f =
  match t1, t2 with
  | Asc E          , _
  | _              , Asc E           -> invalid_argf "Can't merge empty"
  | Asc (U (s, v1)), Asc (U (_s,v2)) -> Asc (U (s, f v1 v2))
  | Asc (U (_, v1)), Asc (S l2)      -> Asc (S (map_with_just_last_check l2 ~f:(fun v2 -> f v1 v2)))
  | Asc (S l1),      Asc (U (_, v2)) -> Asc (S (map_with_just_last_check l1 ~f:(fun v1 -> f v1 v2)))
  | Asc (S l1),      Asc (S l2)      -> Asc (S (start2 eq f l1 l2))

let rec start3 eq f l1 l2 l3 =
  match l1, l2, l3 with
  | [],     [],     []  -> []
  | [],      s,      _  -> invalid_argf "Different lengths! l2: %s" (asc_sets_to_str s)
  |  _,     [],      s  -> invalid_argf "Different lengths! l3: %s" (asc_sets_to_str s)
  |  s,      _,     []  -> invalid_argf "Different lengths! l1: %s" (asc_sets_to_str s)
  | (s1, v1) :: t1
  , (s2, v2) :: t2
  , (s3, v3) :: t3      ->
      let intersect, r1, r2, r3 = Set.must_match_at_beginning3 s1 s2 s3 in
      let nt1 = insert_if_not_empty r1 v1 t1 in
      let nt2 = insert_if_not_empty r2 v2 t2 in
      let nt3 = insert_if_not_empty r3 v3 t3 in
      let acc = [intersect, (f v1 v2 v3)] in
      loop3 eq f acc nt1 nt2 nt3
and loop3 eq f acc l1 l2 l3 =
  match l1, l2, l3 with
  | [],     [],     []  -> acc     (* We insert at the end, thereby preserving order *)
  | [],      s,      _  -> invalid_argf "Different lengths! l2: %s" (asc_sets_to_str s)
  |  _,     [],      s  -> invalid_argf "Different lengths! l3: %s" (asc_sets_to_str s)
  |  s,      _,     []  -> invalid_argf "Different lengths! l1: %s" (asc_sets_to_str s)
  | (s1, v1) :: t1
  , (s2, v2) :: t2
  , (s3, v3) :: t3      ->
      let intersect, r1, r2, r3 = Set.must_match_at_beginning3 s1 s2 s3 in
      let nt1 = insert_if_not_empty r1 v1 t1 in
      let nt2 = insert_if_not_empty r2 v2 t2 in
      let nt3 = insert_if_not_empty r3 v3 t3 in
      let nv = f v1 v2 v3 in
      let nacc = merge_or_add_to_end eq intersect nv acc in
      loop3 eq f nacc nt1 nt2 nt3
and merge3 ~eq t1 t2 t3 f =
  match t1, t2, t3 with
  | Asc E          , _              , _
  | _              , Asc E          , _
  | _              , _              , Asc E           -> invalid_argf "Can't merge3 empty"

  | Asc (U (s, v1)), Asc (U (_, v2)), Asc (U (_, v3)) -> Asc (U (s, f v1 v2 v3))

  | Asc (U (_, v1)), Asc (U (_, v2)), Asc (S l3)      -> Asc (S (map_with_full_check eq l3 ~f:(fun v3 -> f v1 v2 v3)))
  | Asc (U (_, v1)), Asc (S l2),      Asc (U (_, v3)) -> Asc (S (map_with_full_check eq l2 ~f:(fun v2 -> f v1 v2 v3)))
  | Asc (S l1),      Asc (U (_, v2)), Asc (U (_, v3)) -> Asc (S (map_with_full_check eq l1 ~f:(fun v1 -> f v1 v2 v3)))

  | Asc (U (_, v1)), Asc (S l2),      Asc (S l3)      -> Asc (S (start2 eq (fun v2 v3 -> f v1 v2 v3) l2 l3))
  | Asc (S l1),      Asc (U (_, v2)), Asc (S l3)      -> Asc (S (start2 eq (fun v1 v3 -> f v1 v2 v3) l1 l3))
  | Asc (S l1),      Asc (S l2),      Asc (U (_, v3)) -> Asc (S (start2 eq (fun v1 v2 -> f v1 v2 v3) l1 l2))

  | Asc (S l1),      Asc (S l2),      Asc (S l3)      -> Asc (S (start3 eq f l1 l2 l3))

let rec start4 eq f l1 l2 l3 l4 =
  match l1, l2, l3, l4 with
  | [],     [],     [],     []      -> []
  | [],      s,      _,      _      -> invalid_argf "Different lengths! l2: %s" (asc_sets_to_str s)
  |  _,     [],      s,      _      -> invalid_argf "Different lengths! l3: %s" (asc_sets_to_str s)
  |  _,      _,     [],      s      -> invalid_argf "Different lengths! l4: %s" (asc_sets_to_str s)
  |  s,      _,      _,     []      -> invalid_argf "Different lengths! l1: %s" (asc_sets_to_str s)
  | (s1, v1) :: t1
  , (s2, v2) :: t2
  , (s3, v3) :: t3
  , (s4, v4) :: t4                  ->
      let intersect, r1, r2, r3, r4 = Set.must_match_at_beginning4 s1 s2 s3 s4 in
      let nt1 = insert_if_not_empty r1 v1 t1 in
      let nt2 = insert_if_not_empty r2 v2 t2 in
      let nt3 = insert_if_not_empty r3 v3 t3 in
      let nt4 = insert_if_not_empty r4 v4 t4 in
      let acc = [intersect, (f v1 v2 v3 v4)] in
      loop4 eq f acc nt1 nt2 nt3 nt4
and loop4 eq f acc l1 l2 l3 l4 =
  match l1, l2, l3, l4 with
  | [],     [],     [],     []      -> acc     (* We insert at the end, thereby preserving order *)
  | [],      s,      _,      _      -> invalid_argf "Different lengths! l2: %s" (asc_sets_to_str s)
  |  _,     [],      s,      _      -> invalid_argf "Different lengths! l3: %s" (asc_sets_to_str s)
  |  _,      _,     [],      s      -> invalid_argf "Different lengths! l4: %s" (asc_sets_to_str s)
  |  s,      _,      _,     []      -> invalid_argf "Different lengths! l1: %s" (asc_sets_to_str s)
  | (s1, v1) :: t1
  , (s2, v2) :: t2
  , (s3, v3) :: t3
  , (s4, v4) :: t4                  ->
      let intersect, r1, r2, r3, r4 = Set.must_match_at_beginning4 s1 s2 s3 s4 in
      let nt1 = insert_if_not_empty r1 v1 t1 in
      let nt2 = insert_if_not_empty r2 v2 t2 in
      let nt3 = insert_if_not_empty r3 v3 t3 in
      let nt4 = insert_if_not_empty r4 v4 t4 in
      let nv = f v1 v2 v3 v4 in
      let nacc = merge_or_add_to_end eq intersect nv acc in
      loop4 eq f nacc nt1 nt2 nt3 nt4
(* This method is tail recursive, and by default we pay the cost of inserting
   an element at the end, each time, Hopefully, merging, due to {eq}, instead into
   the accumulator-list will effectively constrain the size of the resulting
   list such that the cost is amortized. *)
and merge4 ~eq t1 t2 t3 t4 f =
  match t1, t2, t3, t4 with
  | Asc E,          _,              _,              _
  | _,              Asc E,          _,              _
  | _,              _,              Asc E,          _
  | _,              _,              _,              Asc E           -> invalid_argf "Can't merge empty4"

  (* 0 S's, 4 U's *)
  | Asc (U (s,v1)), Asc (U (_,v2)), Asc (U (_,v3)), Asc (U (_,v4))  -> Asc (U (s, f v1 v2 v3 v4))

  (* 1 S's, 3 U's *)
  | Asc (S l1),     Asc (U (_,v2)), Asc (U (_,v3)), Asc (U (_,v4))  -> Asc (S (map_with_full_check eq l1 ~f:(fun v1 -> f v1 v2 v3 v4)))
  | Asc (U (_,v1)), Asc (S l2),     Asc (U (_,v3)), Asc (U (_,v4))  -> Asc (S (map_with_full_check eq l2 ~f:(fun v2 -> f v1 v2 v3 v4)))
  | Asc (U (_,v1)), Asc (U (_,v2)), Asc (S l3),     Asc (U (_,v4))  -> Asc (S (map_with_full_check eq l3 ~f:(fun v3 -> f v1 v2 v3 v4)))
  | Asc (U (_,v1)), Asc (U (_,v2)), Asc (U (_,v3)), Asc (S l4)      -> Asc (S (map_with_full_check eq l4 ~f:(fun v4 -> f v1 v2 v3 v4)))

  (* 2 S's, 2 U's *)
  | Asc (S l1),     Asc (S l2),     Asc (U (_,v3)), Asc (U (_,v4))  -> Asc (S (start2 eq (fun v1 v2 -> f v1 v2 v3 v4) l1 l2))
  | Asc (S l1),     Asc (U (_,v2)), Asc (S l3),     Asc (U (_,v4))  -> Asc (S (start2 eq (fun v1 v3 -> f v1 v2 v3 v4) l1 l3))
  | Asc (S l1),     Asc (U (_,v2)), Asc (U (_,v3)), Asc (S l4)      -> Asc (S (start2 eq (fun v1 v4 -> f v1 v2 v3 v4) l1 l4))
  | Asc (U (_,v1)), Asc (S l2),     Asc (S l3),     Asc (U (_,v4))  -> Asc (S (start2 eq (fun v2 v3 -> f v1 v2 v3 v4) l2 l3))
  | Asc (U (_,v1)), Asc (S l2),     Asc (U (_,v3)), Asc (S l4)      -> Asc (S (start2 eq (fun v2 v4 -> f v1 v2 v3 v4) l2 l4))
  | Asc (U (_,v1)), Asc (U (_,v2)), Asc (S l3),     Asc (S l4)      -> Asc (S (start2 eq (fun v3 v4 -> f v1 v2 v3 v4) l3 l4))

  (* 3 S's, 1 U's *)
  | Asc (S l1),     Asc (S l2),     Asc (S l3),     Asc (U (_,v4))  -> Asc (S (start3 eq (fun v1 v2 v3 -> f v1 v2 v3 v4) l1 l2 l3))
  | Asc (S l1),     Asc (S l2),     Asc (U (_,v3)), Asc (S l4)      -> Asc (S (start3 eq (fun v1 v2 v4 -> f v1 v2 v3 v4) l1 l2 l4))
  | Asc (S l1),     Asc (U (_,v2)), Asc (S l3),     Asc (S l4)      -> Asc (S (start3 eq (fun v1 v3 v4 -> f v1 v2 v3 v4) l1 l3 l4))
  | Asc (U (_,v1)), Asc (S l2),     Asc (S l3),     Asc (S l4)      -> Asc (S (start3 eq (fun v2 v3 v4 -> f v1 v2 v3 v4) l2 l3 l4))

  (* 4 S's, 0 U's *)
  | Asc (S l1),     Asc (S l2),     Asc (S l3),     Asc (S l4)      -> Asc (S (start4 eq f l1 l2 l3 l4))

let fold_values : type o a. (o, a) t -> init:'b -> f:('b -> a -> 'b) -> 'b =
  fun l ~init ~f -> match l with
    | Desc ld         -> List.fold_left ld ~init ~f:(fun acc (_i, v) -> f acc v)
    | Asc E           -> invalid_arg "Can't fold_values on empty!"
    | Asc (U (_, v))  -> f init v
    | Asc (S la)      -> List.fold_left la ~init ~f:(fun acc (_l, v) -> f acc v)

let fold_set_sizes_and_values : type o a. (o, a) t -> init:'b -> f:('b -> int -> a -> 'b) -> 'b =
  fun l ~init ~f ->
    let ascf = List.fold_left ~init ~f:(fun acc (l, v) -> f acc (Set.size l) v) in
    match l with
    | Desc ld         -> ascf (ascending_t (fun x y -> x = y) ld)     (* TODO: Probably could be faster. *)
    | Asc E           -> invalid_arg "Can't fold_set_sizes_and_values on empty!"
    | Asc (U (s, v))  -> Set.fold s ~init ~f:(fun acc l -> f acc l v)
    | Asc (S la)      -> ascf la

let fold_indices_and_values :
  type o a. (o, a) t -> init:'b -> f:('b -> int -> a -> 'b) -> 'b =
  fun l ~init ~f -> match l with
    | Desc ld -> List.fold_left ld ~init ~f:(fun init (l, v) ->
                    Interval.fold l ~init ~f:(fun acc i -> f acc i v))
    | Asc E          -> invalid_arg "Can't fold_indices_and_values on empty!"
    | Asc (U (s, v)) -> Set.fold s ~init ~f:(fun acc i -> f acc i v)
    | Asc (S la)     -> List.fold_left la ~init ~f:(fun init (s, v) ->
                          Set.fold s ~init ~f:(fun acc i -> f acc i v))


let map : type o a. (o, a) t -> ('b -> 'b -> bool) -> f:(a -> 'b) -> (o, 'b) t =
  fun t eq ~f -> match t with
    | Desc ld         -> Desc (List.map_snd ld ~f)
    | Asc E           -> invalid_argf "Can't map empty!"
    | Asc (U (s, v))  -> Asc (U (s, f v))
    | Asc (S la)      -> Asc (S (map_with_full_check eq la ~f))

let iter_set : type o a. (o, a) t -> f:(int -> a -> unit) -> unit =
  fun t ~f -> match t with
    | Desc ld ->
        List.iter ld ~f:(fun (s, v) ->
          Interval.iter s ~f:(fun i -> f i v))
    | Asc E   -> invalid_argf "Can't iter_set empty"
    | Asc (U (s, v))  -> Set.iter s ~f:(fun i -> f i v)
    | Asc (S la)      -> List.iter la ~f:(fun (l, v) ->
                          List.iter l ~f:(Interval.iter ~f:(fun i -> f i v)))

let to_array = function
  | Asc E           -> invalid_argf "Can't to_array empty"
  | Asc (U (s, v))  -> Array.make (Set.size s) v
  | Asc (S la)      ->
    match la with
    | []  -> [||]
    | h :: t ->
        let s, v = h in
        let n = List.fold_left la ~init:0 ~f:(fun a (s, _) -> a + Set.size s) in
        let r = Array.make n v in
        let fill s v = Set.iter s ~f:(fun i -> r.(i) <- v) in
        fill s v;
        List.iter t ~f:(fun (s, v) -> fill s v);
        r
