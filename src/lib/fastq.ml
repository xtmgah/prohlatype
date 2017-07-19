
module Sset = Set.Make (struct type t = string [@@deriving ord] end)

open Core_kernel.Std

let to_stop = function
  | None   -> fun _ -> false
  | Some n -> fun r -> r >= n

(* read header -> display, stop *)
let to_filter = function
  | []   -> fun _ -> true, false
  | lst  ->
      let s = ref (Sset.of_list lst) in
      begin fun el ->
        if Sset.mem el !s then begin
          s := Sset.remove el !s;
          true, Sset.cardinal !s <= 0
        end else
          false, false
      end

let fold (type a) ?number_of_reads ?(specific_reads=[]) file ~f ~(init : a) =
  let open Biocaml_unix in
  let stop = to_stop number_of_reads in
  let filt = to_filter specific_reads in
  let module M = struct exception Fin of a end in
  try
    Future_unix.Reader.with_file file ~f:(fun rdr ->
      (* Avoid circular dep *)
      let fr = Biocaml_unix.Fastq.read rdr in
      Future_unix.Pipe.fold fr ~init:(0,init) ~f:(fun (c, acc) oe ->
        if stop c then
          raise (M.Fin acc)
        else
          match oe with
          | Error e -> eprintf "%s\n" (Error.to_string_hum e); (c, acc)
          | Ok fqi  -> let display, stop = filt fqi.Biocaml_unix.Fastq.name in
                       match display, stop with
                       | true,        true  -> raise (M.Fin (f acc fqi))
                       | false,       true  -> raise (M.Fin acc)
                       | true,        false -> c + 1, f acc fqi
                       | false,       false -> c, acc))
    |> snd
  with M.Fin m -> m

let all ?number_of_reads file =
  fold ?number_of_reads
    ~f:(fun acc el -> el :: acc)  ~init:[] file
  |> List.rev

let phred_probabilities s =
  let open Biocaml_unix in
  let n = String.length s in
  let a = Array.create ~len:n 0.0 in
  let rec loop i =
    if i = n then Ok a else
      Result.bind (Phred_score.of_char s.[i])
        (fun c -> a.(i) <- Phred_score.to_probability c; loop (i + 1))
  in
  loop 0

let phred_log_probs s =
  let open Biocaml_unix in
  let n = String.length s in
  let a = Array.create ~len:n 0. in
  let rec loop i =
    if i = n then Ok a else
      Result.bind (Phred_score.of_char s.[i])
        (fun c -> a.(i) <- float_of_int (Phred_score.to_int c) /. -10.0;
                  loop (i + 1))
  in
  loop 0

let rec same cmp l1 l2 =
  let rec single_loop search acc = function
    | []                   -> None, acc
    | h :: t when search h -> (Some h), (List.rev acc) @ t
    | h :: t               -> single_loop search (h :: acc) t
  in
  let rec double_loop l2 acc = function
    | []     -> None
    | h :: t ->
        match single_loop (cmp h) [] l2 with
        | None, _     -> double_loop l2 (h :: acc) t
        | Some f, lst -> Some (h, f, (List.rev acc) @ t, lst)
  in
  double_loop l2 [] l1

let name_as_key a = a.Biocaml_unix.Fastq.name

let fold_paired_both ?(to_key=name_as_key) ?number_of_reads ?(specific_reads=[])
   ~f ~init ?ff ?fs file1 file2 =
  let open Biocaml_unix in
  let stop = to_stop number_of_reads in
  let filt = to_filter specific_reads in
  let cmp r1 r2 = (to_key r1) = (to_key r2) in
  let same = same cmp in
  let open Future_unix in
  let open Deferred in
  Reader.with_file file1 ~f:(fun rdr1 ->
    Reader.with_file file2 ~f:(fun rdr2 ->
      (* Avoid circular dep *)
      let fr1 = Biocaml_unix.Fastq.read rdr1 in
      let fr2 = Biocaml_unix.Fastq.read rdr2 in
      let rec single_pipe_fold fr f2 acc =
        Pipe.read fr >>= fun r ->
          match r with
          | `Eof          -> return (`FinishedSingle acc)
          | `Ok (Error e) -> eprintf "%s\n" (Error.to_string_hum e);
                             single_pipe_fold fr f2 acc
          | `Ok (Ok a)    -> single_pipe_fold fr f2 (f2 acc a)
      and two_pipe_fold c s1 s2 acc =
        if stop c then
          return (`DesiredReads acc)
        else
          Pipe.read fr1 >>= fun r1 ->
            Pipe.read fr2 >>= fun r2 ->
              match r1, r2 with
              | `Eof, `Eof                      ->
                  return (`BothFinished acc)
              | `Eof, `Ok eb                    ->
                  let nacc =
                    Option.value_map ff ~default:acc
                      ~f:(fun ff -> List.fold s1 ~init:acc ~f:ff)
                  in
                  begin match fs with
                  | None -> return (`OneReadPairedFinished (1, nacc))
                  | Some fs ->
                      let nacc = List.fold s2 ~init:nacc ~f:fs in
                      begin match eb with
                      | Error e -> eprintf "%s\n" (Error.to_string_hum e);
                                   single_pipe_fold fr2 fs nacc
                      | Ok b    -> single_pipe_fold fr2 fs (fs nacc b)
                      end
                   end
              | `Ok ea, `Eof                    ->
                  let nacc =
                    Option.value_map fs ~default:acc
                      ~f:(fun fs -> List.fold s2 ~init:acc ~f:fs)
                  in
                  begin match ff with
                  | None -> return (`OneReadPairedFinished (2, acc))
                  | Some ff ->
                      let nacc = List.fold s2 ~init:nacc ~f:ff in
                      begin match ea with
                      | Error e ->
                        eprintf "%s\n" (Error.to_string_hum e);
                        single_pipe_fold fr2 ff nacc
                      | Ok a ->
                        single_pipe_fold fr2 ff (ff nacc a)
                      end
                  end
              | `Ok (Error ea), `Ok (Error eb)  ->
                  eprintf "%s\n" (Error.to_string_hum ea);
                  eprintf "%s\n" (Error.to_string_hum eb);
                  two_pipe_fold c s1 s2 acc
              | `Ok (Error ea), `Ok (Ok b)      ->
                  eprintf "%s\n" (Error.to_string_hum ea);
                  two_pipe_fold c s1 (b::s2) acc
              | `Ok (Ok a), `Ok (Error eb)      ->
                  eprintf "%s\n" (Error.to_string_hum eb);
                  two_pipe_fold c (a::s1) s2 acc
              | `Ok (Ok a), `Ok (Ok b)          ->
                  if cmp a b then begin
                    filter_pass a b c s1 s2 acc
                  end else
                    let ns1 = a :: s1 in
                    let ns2 = b :: s2 in
                    match same ns1 ns2 with
                    | Some (r1, r2, ns1, ns2) ->
                        filter_pass r1 r2 c ns1 ns2 acc
                    | None ->
                        two_pipe_fold c ns1 ns2 acc
      and filter_pass a b c s1 s2 acc =
        let display, stop = filt a.Biocaml_unix.Fastq.name in
        match display, stop with
        | true,        true  -> `StoppedByFilter (f acc a b)
        | false,       true  -> `StoppedByFilter acc
        | true,        false -> two_pipe_fold (c + 1) s1 s2 (f acc a b)
        | false,       false -> two_pipe_fold c s1 s2 acc
      in
      two_pipe_fold 0 [] [] init))

let fold_paired ?to_key ?number_of_reads ?specific_reads file1 file2 ~f ~init =
    fold_paired_both ?to_key ?number_of_reads ?specific_reads file1 file2 ~f ~init

let unwrap_cr_ok = function
    | Result.Error _ -> invalid_arg "unwrap_cr_ok: " (*Error.to_string_hum e*)
    | Result.Ok a    -> a

let read_from_pair ~name file1 file2 =
  let res =
    fold_paired
      ~init:None ~f:(fun _ q1 q2 -> Some (q1, q2)) ~specific_reads:[name]
        file1 file2
  in
  let opt =
    match res with
    | `BothFinished o
    | `OneReadPairedFinished (_, o)
    | `FinishedSingle o
    | `StoppedByFilter o
    | `DesiredReads o -> o
  in
  match opt with
  | None -> None
  | Some (r1, r2) ->
            Some ( r1.Biocaml_unix.Fastq.sequence
                 , (phred_probabilities r1.Biocaml_unix.Fastq.qualities |> unwrap_cr_ok)
                 , r2.Biocaml_unix.Fastq.sequence
                 , (phred_probabilities r2.Biocaml_unix.Fastq.qualities |> unwrap_cr_ok))

type paired_reading =
  { both    : (Biocaml_unix.Fastq.item * Biocaml_unix.Fastq.item) list
  ; first   : Biocaml_unix.Fastq.item list
  ; second  : Biocaml_unix.Fastq.item list
  }

let read_both file1 file2 =
  fold_paired_both file1 file2 ~init:([],[],[])
    ~f:(fun (lb, l1, l2) p1 p2  -> (p1,p2) :: lb, l1, l2)
    ~ff:(fun (lb, l1, l2) p1    -> lb, (p1 :: l1), l2)
    ~fs:(fun (lb, l1, l2) p2    -> lb, l1, (p2 :: l2))
  |> function
      | `BothFinished (both, first, second)
      | `FinishedSingle (both, first, second) -> { both; first; second}
      | `OneReadPairedFinished _  -> failwith "Didn't read the rest!"
      | `StoppedByFilter _
      | `DesiredReads _           -> assert false
