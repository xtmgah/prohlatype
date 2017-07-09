open Util

module Pm = Partition_map

(* This is not the prettiest design:
    - The storage is not abstracted but leaks.
    - we have to pass around references, instead of having a cleaner
      buffer that we would access. *)
type 'a t =
  { storage : 'a array ref
  (*; size    : int                         number of unique values. *)
  ; pm      :  (Pm.ascending, int) Pm.t
  }

module type Elements = sig

  type t
  val empty : t
  val is_empty : t -> bool
  val equal : t -> t -> bool
  val to_string : t -> string

end (* Elements *)

module Make (E : Elements) = struct

  (* This method isn't great; it has O(n) (n = # of final unique elements)
     insertion time. The problem with having a smarter insert/lookup:
      1. If we use a tree we'll have to GC it afterwards, and then lookup
         isn't O(1).
      2. If we use an array and have a binary layout, we could allocate too
         much as many of the nodes would be empty.

     The question of _how_ to include this checking logic into the original
     merge. *)
  let insert a v =
    let s = ref (Array.length !a) in
    let rec loop i =
      if i >= !s then begin
        let new_size = 2 * !s + 1 in
        printf "Looking in %d extending to %d\n" i new_size;
        let na = Array.make new_size E.empty in
        Array.blit ~src:!a ~src_pos:0 ~dst:na ~dst_pos:0 ~len:(!s);
        s := new_size;
        a := na;
      end;
      let a_i = !a.(i) in
      if E.is_empty a_i then begin
        !a.(i) <- v;
        i
      end else if E.equal v a_i then
        i
      else
        loop (i + 1)
    in
    loop 0

  (* This is a bit of an 'escape' hatch and kept out of the cached entries
     managed by RtCellCache in ParPHMM. *)
  let of_ascending_pm t =
    let values = Pm.fold_values t ~init:[] ~f:(fun acc v -> v :: acc) in
    let storage = Array.of_list values in
    let pm =
      Pm.map t ~f:(fun v ->
        match Array.findi storage ~f:(fun nv -> E.equal v nv) with
        | None  -> invalid_argf "Something fishy with your equal function, looking for: %s in %s."
                      (E.to_string v)
                      (Array.to_list storage |> List.map ~f:E.to_string |> String.concat ~sep:";");
        | Some i -> i)
    in
    { storage = ref storage; pm}

  let to_regular_pm t =
    let s = !(t.storage) in
    Pm.map t.pm ~f:(fun i -> s.(i))

  let merge storage t1 t2 f =
    Array.fill (!storage) ~pos:0 ~len:(Array.length !storage) E.empty;
    let s1 = !(t1.storage) in
    let s2 = !(t2.storage) in
    let pm =
      Pm.merge t1.pm t2.pm (fun i1 i2 -> insert storage (f s1.(i1) s2.(i2)))
    in
    { storage; pm }

  let merge4 storage t1 t2 t3 t4 f =
    Array.fill (!storage) ~pos:0 ~len:(Array.length !storage) E.empty;
    let s1 = !(t1.storage) in
    let s2 = !(t2.storage) in
    let s3 = !(t3.storage) in
    let s4 = !(t4.storage) in
    let pm =
      Pm.merge4 t1.pm t2.pm t3.pm t4.pm
        (fun i1 i2 i3 i4 -> insert storage (f s1.(i1) s2.(i2) s3.(i3) s4.(i4)))
    in
    { storage; pm = pm }

  let half_merge storage p1 t2 f =
    Array.fill (!storage) ~pos:0 ~len:(Array.length !storage) E.empty;
    let s2 = !(t2.storage) in
    let pm = Pm.merge p1 t2.pm (fun v1 i2 -> insert storage (f v1 s2.(i2))) in
    { storage; pm }

  let quarter_merge4 storage p1 t2 t3 t4 f =
    Array.fill (!storage) ~pos:0 ~len:(Array.length !storage) E.empty;
    let s2 = !(t2.storage) in
    let s3 = !(t3.storage) in
    let s4 = !(t4.storage) in
    let pm =
      Pm.merge4 p1 t2.pm t3.pm t4.pm
        (fun v1 i2 i3 i4 -> insert storage (f v1 s2.(i2) s3.(i3) s4.(i4)))
    in
    { storage; pm }

  let fold_values t ~init ~f =
    let s = !(t.storage) in
    Pm.fold_values t.pm ~init ~f:(fun acc i -> f acc s.(i))

end (* Make *)
