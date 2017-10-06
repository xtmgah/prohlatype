(* Aggregation of the forward passes. *)

open Util

module Pm = Partition_map

let max_arr = Array.fold_left ~init:neg_infinity ~f:max
let max_pm = Pm.fold_values ~init:neg_infinity ~f:max

let higher_value_in_first e1 e2 =
  let r1 = max_pm e1 in
  let r2 = max_pm e2 in
  r1 >= r2

let descending_float_cmp f1 f2 =
  if f1 > f2 then -1
  else if f1 = f2 then 0
  else 1

(* What to do when we know the result of a previous run. *)
module Past_threshold = struct

  open ParPHMM

  type t =
    [ `Don't
    | `Start
    | `Set of float
    ]

  let to_string = function
    | `Don't  -> "Don't"
    | `Start  -> "Start"
    | `Set v  -> sprintf "Set %f" v

  let init b =
    if b then `Start else `Don't

  let new_ prev_threshold proc =
    max prev_threshold (proc.maximum_match ())

  let new_value prev_threshold proc = function
    | Filtered _  -> prev_threshold
    | Completed _ -> new_ prev_threshold proc

  let update prev_threshold proc pr =
    match prev_threshold with
    | `Don't  -> `Don't
    | `Start  -> `Set (new_value neg_infinity proc pr)
    | `Set pv -> `Set (new_value pv proc pr)

end  (* Past_threshold *)

(* Consider a single orientation: either regular or reverse complement. *)
let specific_orientation ?prev_threshold proc pass_result_map reverse_complement read read_errors =
  let open ParPHMM in
  match proc.single ?prev_threshold ~read ~read_errors reverse_complement with
  | Filtered m    -> Filtered m
  | Completed ()  -> Completed (pass_result_map proc reverse_complement)

(* Sometimes (such as in the beginning) we do not know whether to prefer a
   regular or a reverse-complement orientation for read. *)
module Orientation = struct

  open ParPHMM

  type 'a t =
    { regular     : 'a pass_result
    ; complement  : 'a pass_result
    }

  let map ~f t =
    { regular    = f t.regular
    ; complement = f t.complement
    }

  (* The output is ordered so that the left most stat is the most likely.
    We add characters 'R', 'C', 'F' as little annotations. *)
  let to_string ?(sep='\t') ?take_regular completed_to_string t =
    match t.regular, t.complement with
    | Completed r, Completed c  ->
        begin match take_regular with
        | Some p when not (p r c) ->
            sprintf "C%c%s%cR%c%s"
              sep (completed_to_string c) sep sep (completed_to_string r)
        | Some _ | None           ->
            sprintf "R%c%s%cC%c%s"
              sep (completed_to_string r) sep sep (completed_to_string c)
        end
    | Completed r, Filtered m   ->
        sprintf "R%c%s%cF%c%s" sep (completed_to_string r) sep sep m
    | Filtered m, Completed c   ->
        sprintf "C%c%s%cF%c%s" sep (completed_to_string c) sep sep m
    | Filtered mr, Filtered mc  ->
        sprintf "F%c%s%cF%c%s" sep mr sep sep mc

  let most_likely_between ~take_regular t =
    let open ParPHMM in
    match t.regular, t.complement with
    | Filtered mr, Filtered mc -> Filtered (sprintf "Both! %s, %s" mr mc)
    | Filtered _r, Completed c -> Completed (true, c)
    | Completed r, Filtered _c -> Completed (false, r)
    | Completed r, Completed c ->
      if take_regular r c then
        Completed (false, r)
      else
        Completed (true, c)

  (* Compute a specific orientation and label the other as Filtered. *)
  let specific ?prev_threshold proc pass_result_map rc read read_errors =
    if rc then
      { regular     = Filtered "Selected reverse complement"
      ; complement  = specific_orientation ?prev_threshold proc pass_result_map
                        true read read_errors
      }
    else
      { regular     = specific_orientation ?prev_threshold proc pass_result_map
                        false read read_errors
      ; complement  = Filtered "Selected regular"
      }

  (* Consider both orientations. *)
  let check pt pass_result_map proc read read_errors =
    let do_work ?prev_threshold rc =
      specific_orientation ?prev_threshold proc pass_result_map rc read read_errors
    in
    match pt with
    | `Don't ->
        let regular = do_work false in
        let complement = do_work true in
        { regular; complement }, `Don't
    | `Start ->
        let regular = do_work false in
        let prev_threshold = Past_threshold.new_value neg_infinity proc regular in
        let complement = do_work ~prev_threshold true in
        let last_threshold = Past_threshold.new_value prev_threshold proc complement in
        { regular; complement }, `Set last_threshold
    | `Set v ->
        let regular = do_work ~prev_threshold:v false in
        let prev_threshold = Past_threshold.new_value v proc regular in
        let complement = do_work ~prev_threshold true in
        let last_threshold = Past_threshold.new_value prev_threshold proc complement in
        { regular; complement; }, `Set last_threshold

end (* Orientation *)

(* Represent a diagnostc result of reads. *)
module Alleles_and_positions = struct

  open ParPHMM

  (* Likelyhood emission, allele, position of highest emission. *)
  type t = (float * string * int) list

  let to_string (e,a,p) = sprintf "%s,%d,%0.5f" a p e

  let string_of_list =
    string_of_list ~sep:";" ~f:to_string

  (* Descending *)
  let descending_cmp l1 l2 =
    match l1, l2 with
    | [],  _                           -> -1  (* Should error? *)
    | _ , []                           -> 1
    | (e1, _, _) :: _, (e2, _, _) :: _ -> descending_float_cmp e1 e2

end (* Alleles_and_positions *)

(* Storing the log likelihoods of heterozygous pairs.
   Homozygous is equivalent to the individual pairs. *)
module Zygosity_array = struct

  (* Not exactly the triangular number, T_(n-1);
     just have less subtractions this way. *)
  let triangular_number n =
    n * (n - 1) / 2

  let triangular_inverse t =
    let tf = float t in
    (truncate (sqrt (1.0 +. 8.0 *. tf)) - 1) / 2

  let k_n n i j =
    triangular_number n - triangular_number (n - i) + j - i - 1

  let kinv_n n k =
    let tn = triangular_number n in
    let i  = n - 1 - (triangular_inverse (tn - k - 1)) - 1 in
    let j  = k + i + 1 - triangular_number n + triangular_number (n - i) in
    i, j

  (* Test the k <-> i, j mapping logic. *)
  let test n =
    let kn = k_n n in
    let ki = kinv_n n in
    for i = 0 to n - 2 do
      for j = i + 1 to n - 1 do
        let k = kn i j in
        let ni, nj = ki k in
        printf "i: %d\tj: %d\t:k: %d\ ---- ni: %d\tnk: %d %b\n"
          i j k ni nj (i = ni && j = nj)
      done
    done

  (* Top triangle of pair wise comparison *)
  type t =
    { n : int
    ; l : float array
    }

  let storage_size number_alleles =
    triangular_number number_alleles                               (* T_(n-1) *)

  let init number_alleles =
    let s = storage_size number_alleles in
    { n = number_alleles
    ; l = Array.make s 0.
    }

  let add t ~allele1 ~allele2 likelihood =
    let i = min allele1 allele2 in
    let j = max allele1 allele2 in
    let k = k_n t.n i j in
    t.l.(k) <- t.l.(k) +. likelihood

  (* log likelihood, probability, index 1st, index 2nd *)
  let best ?size t likelihood_arr =
    let desired_size = max 1 (Option.value size ~default:(storage_size t.n)) in
    let sorted_insert l i j current_size lst =
      let rec insert lst =
        match lst with
        | []     -> [l, 1, [i,j]]
        | h :: t ->
            let hl, hn, hv = h in
            if l > hl then
              h :: insert t
            else if l = hl then
              (hl, hn + 1, (i,j) :: hv) :: t
            else (* l < hl *)
              (l, 1, [i,j]) :: lst
      in
      match lst with
      | []
      | _ :: [] -> current_size + 1, insert lst
      | h :: t  ->
        let hl, hn, hv = h in
        if l > hl then begin
           if current_size - hn < desired_size then
            current_size + 1, h :: insert t
          else
            current_size + 1 - hn, insert t
        end else if l = hl then
          current_size + 1, ((hl, hn + 1, (i,j) :: hv) :: t)
        else (* l < hl *) begin
          if current_size >= desired_size then
            current_size, lst
          else
            current_size + 1, insert lst
        end
    in
    let _fk, fcs, fres =                                     (* Heterozygous. *)
      Array.fold_left t.l ~init:(0, 0, [])
        ~f:(fun (k, cs, acc) l ->
              let i, j = kinv_n t.n k in
              let ncs, nacc = sorted_insert l i j cs acc in
              (k + 1, ncs, nacc))
    in
    let _fk, _cs, res =                                        (* Homozygous. *)
      Array.fold_left likelihood_arr ~init:(0, fcs, fres)
        ~f:(fun (i, cs, acc) l ->
              let ncs, nacc = sorted_insert l i i cs acc in
              (i + 1, ncs, nacc))
    in
    let most_likely = List.rev_map ~f:(fun (l, _n, ijlst) -> (l, ijlst)) res in
    let maxl, _ = List.hd_exn most_likely in
    let prob l = 10. ** (l -. maxl) in
    let ns =
      let f s l = s +. prob l in
      Array.fold_left ~init:0. ~f t.l
      |> fun init -> Array.fold_left ~init ~f likelihood_arr
    in
    List.map most_likely ~f:(fun (l, ij) -> (l, prob l /. ns, ij))

end (* Zygosity_array *)

module Likelihoods_and_zygosity = struct

  (* TODO: We're opening Util which has likehood defined. *)

  let add_ll state_llhd llhd =
    Pm.iter_set llhd ~f:(fun i v ->
      state_llhd.(i) <- state_llhd.(i) +. v)

  let add_lz zygosity llhd =
    Pm.iter_set llhd ~f:(fun allele1 v1 ->
      Pm.iter_set llhd ~f:(fun allele2 v2 ->
        (* The Zygosity array only stores the upper triangle of the full
           pairwise likelihood matrix. Therefore, ignore the diagonal and
           lower triangular elements to avoid double counting (per read). *)
        if allele1 >= allele2 then
          ()
        else
          Zygosity_array.add zygosity ~allele1 ~allele2 (max v1 v2)))

  (* State is labled because it is modified. *)
  let add_ll_and_lz state_llhd zygosity llhd =
    add_ll state_llhd llhd;
    add_lz zygosity llhd

end (* Likelihoods_and_zygosity *)

(* Outputing results.

   TODO: Expose a separator argument. *)
module Output = struct

  let compare2 (l1, _) (l2, _) =
    descending_float_cmp l1 l2

  let compare4 (l1, r1, _a1, _m1) (l2, r2, _a2, _m1) =
    let lc = descending_float_cmp l1 l2 in
    if lc <> 0 then
      lc
    else
      Nomenclature.compare_by_resolution r1 r2

  let by_likelihood_arr allele_arr final_likelihoods =
    let o =
      Array.mapi allele_arr ~f:(fun i (a, m) ->
        final_likelihoods.(i)
        , Nomenclature.parse_to_resolution_exn a
        , a
        , m)
    in
    Array.sort o ~cmp:compare4;
    o

  let allele_first o oc =
    Array.iter o ~f:(fun (l, _, a, alts) ->
      fprintf oc "%16s\t%0.20f\t%s\n"
        a l (string_of_list ~sep:";" ~f:MSA.Alteration.to_string alts))

  (* Ignore Alter.info *)
  let likelihood_first allele_arr allele_llhd_arr oc =
    let o =
      Array.mapi allele_arr ~f:(fun i (a, _m) -> allele_llhd_arr.(i), a)
      |> Array.to_list
      |> group_by_assoc
      |> List.map ~f:(fun (l, alst) ->
            let clst = Alleles.CompressNames.f alst in
            l, String.concat ~sep:";" clst)
      |> List.sort ~cmp:compare2
    in
    List.iter o ~f:(fun (l, a) -> fprintf oc "%0.20f\t%16s\n" l a)

  let default_zygosity_report_size = 100

  (* Ignore Alter.info *)
  let zygosity ?(size=default_zygosity_report_size) likelihood_first
    allele_arr allele_llhd_arr zt oc =
    fprintf oc "Zygosity:\n";
    let open Zygosity_array in
    let zb = best ~size zt allele_llhd_arr in
    if likelihood_first then
      List.iter zb ~f:(fun (l, p, ijlist) ->
        let alleles_str =
          string_of_list ijlist ~sep:"\t" ~f:(fun (i,j) ->
            sprintf "%s,%s" (fst allele_arr.(i)) (fst allele_arr.(j)))
        in
        fprintf oc "%0.20f\t%0.4f\t%16s\n" l p alleles_str)
    else
      List.iter zb ~f:(fun (l, p, ijlist) ->
        List.iter ijlist ~f:(fun (i, j) ->
          fprintf oc "%16s\t%16s\t%0.20f\t%0.4f\n"
            (fst allele_arr.(i)) (fst allele_arr.(j)) l p))

  let output_likelihood lfirst allele_arr allele_llhd_arr oc =
    let o = by_likelihood_arr allele_arr allele_llhd_arr in
    fprintf oc "Likelihood:\n";
    if lfirst then
      likelihood_first allele_arr allele_llhd_arr oc
    else
      allele_first o oc

  let f lfirst zygosity_report_size allele_arr allele_llhd_arr zt oc =
    output_likelihood lfirst allele_arr allele_llhd_arr oc;
    zygosity ~size:zygosity_report_size lfirst allele_arr
      allele_llhd_arr zt oc

end (* Output *)

(* Enclose the extraction of read errors from FASTQ reads. *)
module Fastq_items = struct

  exception Read_error_parsing of string

  let repf fmt =
    ksprintf (fun s -> raise (Read_error_parsing s)) fmt

  let single fqi ~k =
    let open Core_kernel.Std in
    let open Biocaml_unix.Fastq in
    time (sprintf "updating on single read %s" fqi.name) (fun () ->
      match Fastq.phred_log_probs fqi.qualities with
      | Result.Error e        -> repf "%s" (Error.to_string_hum e)
      | Result.Ok read_errors -> k fqi.name fqi.sequence read_errors)

  let paired fq1 fq2 ~k =
    let open Biocaml_unix.Fastq in
    let open Core_kernel.Std in
    assert (fq1.name = fq2.name);
    time (sprintf "updating on double read %s" fq1.name) (fun () ->
      match Fastq.phred_log_probs fq1.Biocaml_unix.Fastq.qualities with
      | Result.Error e       -> repf "%s" (Error.to_string_hum e)
      | Result.Ok re1 ->
          match Fastq.phred_log_probs fq2.Biocaml_unix.Fastq.qualities with
          | Result.Error e       -> repf "%s" (Error.to_string_hum e)
          | Result.Ok re2 ->
              k fq1.name fq1.sequence re1 fq2.sequence re2)

end (* Fastq_items *)

type single_conf =
  { prealigned_transition_model : bool
  (** Use a transition model (transition probability between hidden states of
      the Markov model that represent Start, End, Match, Insert and Delete),
      that assumes the entire read will fit completely inside the reference
      area. *)

  ; allele                : string option
  (** Perform the operation against only the specified allele instead *)

  ; insert_p              : float option
  (* Override the default insert emission probability. *)

  ; band                  : ParPHMM.band_config option
  (* Perform banded passes. *)

  ; max_number_mismatches : int option
  (* Max number of allowable mismatches to use a threshold filter for the
     forward pass. *)

  ; past_threshold_filter : bool
  (* Use the previous match likelihood, when available (ex. against reverse
     complement), as a threshold filter for the forward pass. *)

  ; check_rc              : bool
  (** Compare against the reverse complement of a read and take the best likelihood. *)

  ; split                 : int option
  (** Split the forward pass to operate over this many segments of the read.
      The value must divide the read_length evenly or an exception is thrown. *)
  }

let single_conf ?allele ?insert_p ?band ?max_number_mismatches ?split
  ~prealigned_transition_model
  ~past_threshold_filter ~check_rc () =
    { prealigned_transition_model
    ; allele
    ; insert_p
    ; band
    ; max_number_mismatches
    ; past_threshold_filter
    ; check_rc
    ; split
    }

type ('state, 'read_result) t =
  { single  : Biocaml_unix.Fastq.item -> 'read_result
  ; paired  : Biocaml_unix.Fastq.item -> Biocaml_unix.Fastq.item -> 'read_result
  ; merge   : 'state -> 'read_result -> unit
  ; output  : 'state -> out_channel -> unit
  }

type forward_opt =
  { likelihood_first     : bool
  ; zygosity_report_size : int
  ; report_size          : int
  }

module Forward = struct

  open ParPHMM

  type stat =
    { aap        : Alleles_and_positions.t
    ; likelihood : float mt
    }

  let proc_to_stat report_size proc _comp =
    { aap        = proc.best_allele_pos report_size
    ; likelihood = proc.per_allele_llhd ()
    }

  let forward report_size past_threshold proc read read_errors =
    time (sprintf "forward of report_size: %d; past_threshold: %s; read: %s"
            report_size (Past_threshold.to_string past_threshold)
              (String.sub_exn read ~index:0 ~length:10))
    (fun () ->
      Orientation.check past_threshold (proc_to_stat report_size) proc read read_errors)

  type per_read =
    { name  : string
    ; aapt  : Alleles_and_positions.t Orientation.t
    }

  type state =
    { per_allele_lhood  : float array
    ; zygosity          : Zygosity_array.t
    ; mutable per_reads : per_read list
    }

  type read_result =
    { name  : string
    ; stat  : stat Orientation.t single_or_paired
    }

  let just_aap = function
    | Filtered m   -> Filtered m
    | Completed rm -> Completed rm.aap

  let just_aap_or = Orientation.map ~f:just_aap

  let take_regular_by_likelihood  r c =
    higher_value_in_first r.likelihood c.likelihood

  let update_state_single t name stat_or =
    let take_regular = take_regular_by_likelihood in
    t.per_reads <- { name; aapt = just_aap_or stat_or } :: t.per_reads;
    let pr = Orientation.most_likely_between stat_or ~take_regular in
    match pr with
    | Filtered m        -> printf "For %s: %s\n" name m
    | Completed (_c, s) ->
        Likelihoods_and_zygosity.add_ll_and_lz
          t.per_allele_lhood t.zygosity s.likelihood

  let output_state likelihood_first zygosity_report_size allele_arr t oc =
    let take_regular r c = Alleles_and_positions.descending_cmp r c <= 0 in
    Output.f likelihood_first zygosity_report_size allele_arr
      t.per_allele_lhood t.zygosity oc;
    fprintf oc "Per Read:\n";
    List.iter t.per_reads ~f:(fun {name; aapt} ->
      fprintf oc "%s\n\t%s\n" name
        (Orientation.to_string ~take_regular
            Alleles_and_positions.string_of_list aapt))

  let to_proc_allele_arr ?allele ?insert_p ?max_number_mismatches ?band ?split
    ~prealigned_transition_model read_length parPHMM_t =
    match allele with
    | None ->
      let proc =
        match split with
        | None  ->
          setup_single_pass ?insert_p ?max_number_mismatches ?band
            ~prealigned_transition_model read_length parPHMM_t
        | Some n ->
          setup_splitting_pass ?insert_p ?max_number_mismatches ?band
            ~prealigned_transition_model read_length n parPHMM_t
      in
      proc, parPHMM_t.alleles
    | Some allele ->
      let proc =
        setup_single_allele_forward_pass ?insert_p ?max_number_mismatches
          ~prealigned_transition_model read_length allele parPHMM_t
      in
      let arr =
        let index_opt = Array.findi parPHMM_t.alleles ~f:(fun (a,_) -> a = allele) in
        match index_opt with
        | None  -> invalid_argf "Allele %s isn't part of gene!" allele
        | Some i -> [| parPHMM_t.alleles.(i) |]
      in
      proc, arr

  type opt = forward_opt

  let init conf ~read_length parPHMM_t opt =
    let { likelihood_first; zygosity_report_size; report_size } = opt in
    let { prealigned_transition_model; allele; insert_p; band
        ; max_number_mismatches; past_threshold_filter ; split; _} = conf
    in
    let open ParPHMM in
    let proc, allele_arr =
      to_proc_allele_arr ?allele ?insert_p ?max_number_mismatches ?band ?split
        ~prealigned_transition_model read_length parPHMM_t
    in
    let initial_pt = Past_threshold.init past_threshold_filter in
    (* Curry away arguments and discard final threshold; can't use it. *)
    let forward pt r re = fst (forward report_size pt proc r re) in
    let rec state = { per_allele_lhood; zygosity; per_reads; }
    and per_allele_lhood = proc.init_global_state ()
    and zygosity = Zygosity_array.init (Array.length allele_arr)
    and per_reads = []
    in
    let rec single fqi =
      Fastq_items.single fqi ~k:(fun name read read_errors ->
        { name; stat = Single (forward initial_pt read read_errors) })
    and paired fq1 fq2 =
      let take_regular = take_regular_by_likelihood in
      Fastq_items.paired fq1 fq2 ~k:(fun name rd1 re1 rd2 re2 ->
        let r1 = forward initial_pt rd1 re1 in
        match Orientation.most_likely_between r1 ~take_regular with
        | Filtered m  ->
            let r2 = forward initial_pt rd2 re2 in
            { name; stat = Paired (r1, r2)}
        | Completed (c, _)  ->
            let r2 = Orientation.specific proc (proc_to_stat report_size)
                      (not c) rd2 re2 in
            { name; stat = Paired (r1, r2)})
    and merge state rr =
      match rr.stat with
      | Single stat_or  -> update_state_single state rr.name  stat_or
      | Paired (s1, s2) -> update_state_single state (rr.name ^ " 1") s1;
                           update_state_single state (rr.name ^ " 2") s2
    and output t oc =
      output_state likelihood_first zygosity_report_size allele_arr t oc
    and t = { single; paired; merge; output }
    in
    t, state

end (* Forward *)

(* A map of reads to a Viterbi decoded path *)
module Viterbi = struct

  open ParPHMM
  open Path

  let center_justify str size =
    let n = String.length str in
    let rem = size - n in
    if rem <= 0 then
      str
    else
      let l = rem / 2 in
      let r = if (rem mod 2) = 1 then l + 1 else l in
      sprintf "%*s%s%*s" l "" str r ""

  let viterbi_result_to_string ?(width=250) ?(labels=("reference ", "read "))
    {reverse_complement; emission; path_list} =
    let separate ?(from="") rc { reference; read; start; end_ } =
      sprintf "Reverse complement: %b, final emission: %f, path length: %d from %d to %d %s\n%s"
        rc emission (List.length path_list) start end_ from
        (manual_comp_display ~width ~labels reference read)
    in
    match to_strings path_list with
    | Single s        -> separate reverse_complement s
    | Paired (r1, r2) ->
        let s1, rc1, f1, s2, rc2, f2 =
          if r1.start < r2.start then
            r1, reverse_complement, "read 1", r2, not reverse_complement, "read 2"
          else
            r2, not reverse_complement, "read2", r1, reverse_complement, "read 1"
        in
        let inner_distance = s2.start - s1.end_ in
        if inner_distance < 0 then
          sprintf "Negative Inner distance:\n%s\n%s"
            (separate ~from:f1 rc1 s1) (separate ~from:f2 rc2 s2)
        else
          let idmsg = sprintf " inner: %d " inner_distance in
          let allele_i = center_justify idmsg inner_distance in
          let actual_size = String.length allele_i in
          let read_i = String.make actual_size '=' in
          let reference = s1.reference ^ allele_i ^ s2.reference in
          let read = s1.read ^ read_i ^ s2.read in
          let msm_offset = - actual_size in
          sprintf "Reverse complement: %b, final emission: %f, path length: %d from %d to %d %s->%s\n%s"
            rc1 emission (List.length path_list) s1.start s2.end_ f1 f2
            (manual_comp_display ~msm_offset ~width ~labels reference read)

  type read_result =
    { name  : string
    ; res   : viterbi_result
    }

  type state =
    { mutable results : read_result list
    }

  type opt = unit

  let init conf ~read_length parPHMM_t () =
    let { prealigned_transition_model; allele; insert_p; _ } = conf in
    let open ParPHMM in
    (* Relying on reference being first in the specified ParPHMM.t allele list. *)
    let allele = Option.value ~default:(fst parPHMM_t.alleles.(0)) allele in
    let labels = allele ^ " ", "read " in
    let s, p =
      setup_single_allele_viterbi_pass ?insert_p ~allele
        ~prealigned_transition_model read_length parPHMM_t
    in
    let state = { results = [] } in
    let rec t = { single; paired; merge; output }
    and single =
      Fastq_items.single ~k:(fun name read read_errors ->
        { name; res = s read read_errors})
    and paired fq1 fq2 =
      Fastq_items.paired fq1 fq2 ~k:(fun name rd1 re1 rd2 re2 ->
        { name; res =  p rd1 re1 rd2 re2})
    and merge state pr =
      state.results <- pr :: state.results
    and output state oc =
      List.iter state.results ~f:(fun {name; res } ->
        fprintf oc "%s:\n%s\n" name (viterbi_result_to_string ~labels res))
    in
    t, state

end (* Viterbi *)

(** Single Loci Drivers **)
module type S = sig

  type state
  type read_result

  type opt

  val init : single_conf
           -> read_length:int
           -> ParPHMM.t
           -> opt
           -> (state, read_result) t * state

end (* S *)

module Make_single (S : S) = struct

  let init = S.init

  let single d fqi = d.single fqi
  let paired d fq1 fq2 = d.paired fq1 fq2
  let merge d s r = d.merge s r
  let output d s oc = d.output s oc

end (* Make_single *)

(* Combine results from multiple loci. *)

type multiple_conf =
  { prealigned_transition_model : bool
  (** Use a transition model (transition probability between hidden states of
      the Markov model that represent Start, End, Match, Insert and Delete),
      that assumes the entire read will fit completely inside the reference
      area. *)

  ; insert_p                : float option
  (* Override the default insert emission probability. *)


  ; band                    : ParPHMM.band_config option
  (* Perform banded passes. *)

  ; max_number_mismatches   : int option
  (* Max number of allowable mismatches to use a threshold filter for the
     forward pass. *)

  ; past_threshold_filter   : bool
  (* Use the previous match likelihood, when available (ex. against reverse
     complement), as a threshold filter for the forward pass. *)

  ; split                   : int option
  (** Split the forward pass to operate over this many segments of the read.
      The value must divide the read_length evenly or an exception is thrown. *)

  ; incremental_pairs       : bool
  (* This option only applies to paired typing. Instead of naively modeling
     the two read pairs at the same time, use the first as guidance of which
     loci is the best, and then apply the second read to only the best loci.
     The default should is false as there seem to always be reads where the
     first is too ambiguous and the error profile shifts such that
     [first_read_best_log_gap] is not good enough. We need a better algorithm
     for this. *)

  ; first_read_best_log_gap : float option
  (** When performing paired read inference, for the sake of expediency we want
      to make a decision about the best (most likely aligned to read) gene
      based upon the first read; then we know the orientation of second read and
      where to measure. Unfortunately, sometimes the first read aligns almost
      equally well to different alleles within 2 genes. This value controls a
      band within which we'll keep the best genes (based on the likelihood of the
      firs read) and afterwards align the second. The likelihoods, for other
      genes, outside of this band are discarded. By default this value is set
      to |log_10 1/100|. *)
  }

let multiple_conf ?insert_p ?band ?max_number_mismatches ?split
  ?first_read_best_log_gap
  ~prealigned_transition_model
  ~past_threshold_filter ~incremental_pairs () =
    { prealigned_transition_model
    ; insert_p
    ; band
    ; max_number_mismatches
    ; past_threshold_filter
    ; incremental_pairs
    ; split
    ; first_read_best_log_gap
    }

module Multiple_loci = struct

  type 'single_result single_or_incremental =
    | SingleRead of 'single_result Orientation.t
    (* We'll test both regular and complement options. *)

    | PairedDependent of
      { first_o : bool
      ; first   : 'single_result
      ; second  : 'single_result ParPHMM.pass_result
      }
    (* Orientation and gene of 2nd read is determined by 1st. There is no
       {pass_result} since we're not going to apply a filter to the 2nd read.
       Note that one could "naturally" combine the result of the first by
       passing the first's emission (via per_allele_hood) into the second
       read's forward pass (this is similar to thinking of the 2 reads as just
       one long read), but that will dramatically slow down the pass (it will
       start out already branched). It is better to keep the two likelihoods
       separate and then just multiply (log -> add) the results together. This
       is the desired outcome for paired reads as it is the most
       descriminative. *)

  let orientation_char_of_bool reverse_complement =
    if reverse_complement then 'C' else 'R'

  let pass_result_to_short_string sep sr_to_string = function
    | ParPHMM.Filtered m -> sprintf "F%c%s" sep m
    | ParPHMM.Completed r -> sr_to_string r

  let soi_to_string ?take_regular ?(sep='\t') sr_to_string soi =
    let ots = Orientation.to_string ?take_regular ~sep sr_to_string in
    match soi with
    | SingleRead ors                             ->
        sprintf "SingleRead%c%s" sep (ots ors)
    | PairedDependent { first_o; first; second } ->
        sprintf "PairedDependent%c%c%c%s%c%s"
          sep (orientation_char_of_bool first_o)
          sep (sr_to_string first)
          sep (pass_result_to_short_string sep sr_to_string second)

  let take_regular = Forward.take_regular_by_likelihood

  let most_likely_orientation or_ =
    Orientation.most_likely_between ~take_regular or_

  (* true if s1 is better than s2 *)
  let better_soi s1 s2 =
    let l s = max_pm s.Forward.likelihood in
    let open ParPHMM in
    match s1, s2 with
    | PairedDependent p1, PairedDependent p2  ->
        begin
          match p1.second, p2.second with
          | Filtered _,    _             -> false
          | _,             Filtered _    -> true
          | Completed ss1, Completed ss2 -> l p1.first +. l ss1 > l p2.first +. l ss2
        end
    | PairedDependent p1, SingleRead sr2      ->
        begin
          match most_likely_orientation sr2 with
          | Filtered  _                   -> true
          | Completed (_, s)  ->
              begin match p1.second with
              | Filtered  _               -> l p1.first >= l s
              | Completed _               -> true
              end
        end
    | SingleRead sr1,     PairedDependent p2  ->
        begin
          match most_likely_orientation sr1 with
          | Filtered _                    -> false
          | Completed (_, s)  ->
              begin match p2.second with
              | Filtered  _               -> l s >= l p2.first
              | Completed _               -> false
              end
        end
    | SingleRead sr1,     SingleRead sr2      ->
        begin
          match most_likely_orientation sr1 with
          | Filtered _                    -> false
          | Completed (_, l1)      ->
            begin match most_likely_orientation sr2 with
            | Filtered  _                 -> true
            | Completed (_, l2)           -> l l1 >= l l2
            end
        end

  type 'single_result paired =
    | FirstFiltered of
      { first   : string
      ; second  : 'single_result Orientation.t
      }
    (* Both orientations of the first read were filtered, so the 2nd read is
       entirely independent of the first. This can occur if we have a filter
       (such as past threshold from another loci) that ignores that loci. *)
    | FirstOrientedSecond of
      { first_o : bool
      ; first   : 'single_result
      ; second  : 'single_result ParPHMM.pass_result
      }
    (* One of the orientations of the first wasn't filtered and we used
       it to orient the second read. There is a {pass_result} for second
       because in the cases where we have a split, those may trigger a
       filter that stops computation. *)

  let pr_to_string ?(sep='\t') sr_to_string pr =
    let ots = Orientation.to_string ~sep sr_to_string in
    match pr with
    | FirstFiltered { first; second}                 ->
        sprintf "FirstFiltered%c%s%c%s" sep first sep (ots second)
    | FirstOrientedSecond { first_o; first; second } ->
        sprintf "FirstOrientedSecond%c%c%c%s%c%s"
          sep (orientation_char_of_bool first_o)
          sep (sr_to_string first)
          sep (pass_result_to_short_string sep sr_to_string second)

  type 'sr potentially_paired =
    | Single_or_incremental of (string * 'sr single_or_incremental) list
    | MPaired of ((string * 'sr paired) list)   (* M for multi to not conflict with Paired *)

  let aap_soi_to_string =
    let take_regular r c = Alleles_and_positions.descending_cmp r c <= 0 in
    soi_to_string ~take_regular

  let pp_to_string ?(sep='\t') sr_to_string = function
    | Single_or_incremental soi_lst ->
        string_of_list soi_lst ~sep:"\n" ~f:(fun (l, s) ->
          sprintf "%s%c%s" l sep (aap_soi_to_string ~sep sr_to_string s))
    | MPaired pr_lst ->
        string_of_list pr_lst ~sep:"\n" ~f:(fun (l, p) ->
          sprintf "%s%c%s" l sep (pr_to_string ~sep sr_to_string p))

  type 'sr per_read =
    { name  : string
    ; rrs   : 'sr potentially_paired
    }

  type per_loci =
    { loci        : string
    ; likelihood  : float array
    ; zygosity    : Zygosity_array.t
    }

  type state =
    { per_loci          : per_loci list

    ; mutable per_read  : Alleles_and_positions.t per_read list
    (* At the final state we'll discard the individual likelihood float array's
       and just store the alleles and positions. *)
    }

  type read_result = Forward.stat per_read

  (* A PairedDependent with completed second should be chosen over any SingleRead's.
     A PairedDependent with a Filtered second should be compared by first.
     Compare 2 PairedDependent by both.
   *)
  let reduce_soi soi_lst =
    let open ParPHMM in
    List.reduce soi_lst ~f:(fun (l1, s1) (l2, s2) ->
      if better_soi s1 s2 then
        l1, s1
      else
        l2, s2)
    |> Option.bind ~f:(fun (loci, soi) ->
        match soi with
        | PairedDependent { first; second; _} ->
            begin match second with
            | Filtered _  -> Some (loci, Single first)
            | Completed s -> Some (loci, Paired (first, s))
            end
        | SingleRead  or_ ->
            begin match most_likely_orientation or_ with
            | Filtered _      -> None             (* After all that! *)
            | Completed (_,s) -> Some (loci, Single s)
            end)

  let map_soi_to_aap lst =
    List.map lst ~f:(fun (loci, soi) ->
      let n =
        match soi with
        | PairedDependent { first_o; first; second } ->
            PairedDependent
              { first_o
              ; first = first.Forward.aap
              ; second = ParPHMM.map_completed ~f:(fun s -> s.Forward.aap) second
              }
        | SingleRead oi                             ->
           SingleRead (Forward.just_aap_or oi)
      in
      (loci, n))

  (* We can only compare based upon the result of the 2nd read, but if a
     FirstOrientedSecond scenario is best, we want to use the likelihood from
     BOTH reads in the inference. *)
  let reduce_mpr pr_lst =
    let update loci stat pr best =
      let l = max_pm stat.Forward.likelihood in
      match best with
      | None                        -> Some (l, loci, pr)
      | Some (bl, _, _) when l > bl -> Some (l, loci, pr)
      | Some _                      -> best
    in
    let open ParPHMM in
    let rec loop best = function
      | []               -> best
      | (loci, pr) :: tl ->
          begin match pr with
          | FirstFiltered { second } ->
              begin match most_likely_orientation second with
              | Filtered  _         -> loop best tl
              | Completed (_, stat) -> loop (update loci stat (Single stat) best) tl
              end
          | FirstOrientedSecond { first; second } ->
              begin match second with
              | Filtered _          -> loop best tl
              | Completed s         -> loop (update loci s (Paired (first, s)) best) tl
              end
          end
    in
    loop None pr_lst

  let map_pr_to_aap lst =
    List.map_snd lst ~f:(function
        | FirstFiltered { first; second } ->
            FirstFiltered { first; second = Forward.just_aap_or second }
        | FirstOrientedSecond { first_o; first; second } ->
            FirstOrientedSecond
              { first_o
              ; first   = first.Forward.aap
              ; second  = ParPHMM.map_completed ~f:(fun s -> s.Forward.aap) second })

  let merge state { name ; rrs } =
    let open ParPHMM in
    let assign_to_per_loci { loci; likelihood; zygosity } = function
      | Single stat ->
          Likelihoods_and_zygosity.add_ll_and_lz
            likelihood zygosity stat.Forward.likelihood
      | Paired (s1, s2) ->
          Likelihoods_and_zygosity.add_ll_and_lz
            likelihood zygosity s1.Forward.likelihood;
          Likelihoods_and_zygosity.add_ll_and_lz
            likelihood zygosity s2.Forward.likelihood
    in
    let assign_to_best best_loci best_stat =
      List.iter state.per_loci ~f:(fun pl ->
        if best_loci = pl.loci then
          assign_to_per_loci pl best_stat)
    in
    match rrs with
    | Single_or_incremental soi_lst ->
        begin match reduce_soi soi_lst with
        | None  -> eprintf "All read results filtered for %s\n%!" name
        | Some (best_loci, best_stat)  ->
            assign_to_best best_loci best_stat
        end;
        let mrs = Single_or_incremental (map_soi_to_aap soi_lst) in
        state.per_read <- { name; rrs = mrs } :: state.per_read
    | MPaired pr_lst ->
        begin match reduce_mpr pr_lst with
        | None -> eprintf "All 2nd read results filtered for %s\n%!" name
        | Some (_bl, best_loci, best_stat)  ->
            assign_to_best best_loci best_stat
        end;
        let mrs = MPaired (map_pr_to_aap pr_lst) in
        state.per_read <- { name; rrs = mrs } :: state.per_read

  let output_per_reads prlst oc =
    fprintf oc "Per Read:\n";
    List.iter prlst ~f:(fun {name; rrs} ->
      fprintf oc "%s\n%s\n" name
        (pp_to_string Alleles_and_positions.string_of_list rrs))

  (* Easier to reason about this as a distance, hence >= 0 *)
  let abs_logp_one_over_hundred = abs_float (log10 0.01)

  type incremental_classification =
    | LessLikely
    | Within
    | MoreLikely

  let classify_likelihood ?(log_gap=abs_logp_one_over_hundred) ~best newl =
    if newl <= best then begin
      if (best -. newl) < log_gap then
        Within
      else
        LessLikely
    end else begin (* newl > best *)
      if (newl -. best) < log_gap then
        Within
      else
        MoreLikely
    end

  let init conf opt read_length parPHMM_t_lst =
    let { likelihood_first; zygosity_report_size; report_size } = opt in
    let { prealigned_transition_model; insert_p; band; max_number_mismatches
        ; split; _ } = conf in
    let paa =
      List.map_snd parPHMM_t_lst ~f:(fun parPHMM_t ->
        let proc, allele_arr =
          Forward.to_proc_allele_arr ?insert_p ?max_number_mismatches ?band
            ?split ~prealigned_transition_model read_length parPHMM_t
        in
        let n = Array.length allele_arr in
        proc, allele_arr, n)
    in
    let initial_pt = Past_threshold.init conf.past_threshold_filter in
    let forward = Forward.forward report_size in
    let specific_orientation p rc r re =
      specific_orientation p (Forward.proc_to_stat report_size) rc r re
    in
    let ordinary_paired name rd1 re1 rd2 re2 =
      let _fpt1, _fpt2, res =
        List.fold_left paa ~init:(initial_pt, initial_pt, [])
          ~f:(fun (pt1, pt2, acc) (loci, (p, _, _)) ->
                let result1, npt1 = forward pt1 p rd1 re1 in
                match most_likely_orientation result1 with
                | ParPHMM.Filtered  m ->
                    let second, npt2 = forward pt2 p rd2 re2 in
                    npt1, npt2, (loci, FirstFiltered { first = m; second }) :: acc
                | ParPHMM.Completed (first_o, first) ->
                    let second = specific_orientation p (not first_o) rd2 re2 in
                    let npt2 = Past_threshold.update pt2 p second in
                    npt1, npt2, (loci, FirstOrientedSecond { first_o; first; second }) :: acc)
      in
      MPaired (List.rev res)
    in
    let decreasing_likelihood = insert_sorted ( < ) in
    let incremental_paired name rd1 re1 rd2 re2 =
      let best, rest, _fpt1 =
        List.fold_left paa ~init:([], [], initial_pt)
          ~f:(fun (best, acc, pt) (loci, (p, _, _)) ->
                let result1, npt = forward pt p rd1 re1 in
                match most_likely_orientation result1 with
                | ParPHMM.Filtered m ->
                    let nacc = (loci, SingleRead result1) :: acc in
                    best, nacc, npt
                | ParPHMM.Completed (c, first) ->
                    let l = max_pm first.Forward.likelihood in
                    let for_second = loci, p, result1, c, first in
                    match best with
                    | []           ->
                            [l, for_second], acc, npt
                    | (bl, (bloci, _,_,_,_)) :: _ ->
                        begin match classify_likelihood ~best:bl l with
                        | LessLikely ->
                            let nacc = (loci, SingleRead result1) :: acc in
                            best, nacc, npt
                        | MoreLikely ->
                            let nacc =
                              List.map best ~f:(fun (_, (l, _, r1, _, _)) -> (l, SingleRead r1))
                              @ acc
                            in
                            [l, for_second], nacc, npt
                        | Within     ->
                            let nbest = decreasing_likelihood l for_second best in
                            nbest, acc, npt
                        end)
      in
      match best with
      | []  ->
          eprintf "All loci were filtered for first read of %s, ignoring second.\n"
            name;
          Single_or_incremental (List.rev rest)
      | lst ->
          let seconds = List.map lst ~f:(fun (_l, (loci, p, _, first_o, first)) ->
            let second = specific_orientation p (not first_o) rd2 re2 in
            (loci, PairedDependent {first_o; first; second}))
          in
          Single_or_incremental (seconds @ (List.rev rest))
    in
    let rec state = { per_loci; per_read = []}
    and per_loci =
      List.map paa ~f:(fun (loci, (p, _, number_alleles)) ->
        { loci
        ; likelihood = p.ParPHMM.init_global_state ()
        ; zygosity = Zygosity_array.init number_alleles
        })
    in
    let rec t = { single; paired; merge; output }
    and single fqi =
      Fastq_items.single fqi ~k:(fun name read read_errors ->
        { name
        ; rrs =
            List.fold_left paa ~init:(initial_pt, [])
                ~f:(fun (pt, acc) (loci, (p, _, _)) ->
                      let r, npt = forward pt p read read_errors in
                      npt, (loci, SingleRead r) :: acc)
            |> snd                                 (* Discard final threshold *)
            |> List.rev                                (* Restore loci order. *)
            |> fun l -> Single_or_incremental l
        })
    and paired fq1 fq2 =
     Fastq_items.paired fq1 fq2 ~k:(fun name rd1 re1 rd2 re2 ->
        { name
        ; rrs =
            if conf.incremental_pairs then
              incremental_paired name rd1 re1 rd2 re2
            else
              ordinary_paired name rd1 re1 rd2 re2
        })
    and output state oc =
      List.iter2 paa state.per_loci
        ~f:(fun (_, (_, allele_arr, _)) { loci; likelihood; zygosity; _} ->
              fprintf oc "%s\n" loci;
              Output.f likelihood_first zygosity_report_size
                allele_arr likelihood zygosity oc);
      output_per_reads state.per_read oc
    in
    t, state

end (* Multiple_loci *)
