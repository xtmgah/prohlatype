(* Typing via a Parametric PHMM. *)
open Util

let app_name = "multi_par"

let (//) = Filename.concat

let to_read_size_dependent
  (* Allele information source *)
    ~alignment_files ~merge_files ~distance
    ~skip_disk_cache =
    let selectors = [] in           (* Selectors NOT supported, on purpose! *)
    let als =
      List.map alignment_files ~f:(Alleles.Input.alignment ~selectors ~distance)
    in
    let mls =
      List.map merge_files ~f:(Alleles.Input.merge ~selectors ~distance)
    in
    match als @ mls with
    | []     -> Error "Neither a merge nor alignment file specified!"
    | inputs ->
      Ok (fun read_size ->
            List.map inputs ~f:(fun input ->
              let name = Alleles.Input.to_string input in
              let par_phmm_arg = Cache.par_phmm_args ~input ~read_size in
              let pt = Cache.par_phmm ~skip_disk_cache par_phmm_arg in
              name, pt))

module Pd = ParPHMM_drivers
module Pdml = Pd.Multiple_loci

module Regular = struct

  let init conf opt read_size rp =
    let ptlst =
      time (sprintf "Setting up ParPHMM transitions with %d read_size" read_size)
        (fun () -> rp read_size)
    in
    time "Allocating forward pass workspaces"
      (fun () -> Pdml.init conf opt read_size ptlst)

  let single conf opt acc fqi =
    match acc with
    | `Setup rp ->
        let read_size = String.length fqi.Biocaml_unix.Fastq.sequence in
        let t, s = init conf opt read_size rp in
        t.Pd.merge s (t.Pd.single fqi);
        `Set (t, s)
    | `Set (t, s) ->
        t.Pd.merge s (t.Pd.single fqi);
        `Set (t, s)

  let paired conf opt acc fq1 fq2 =
    match acc with
    | `Setup rp ->
        let read_size = String.length fq1.Biocaml_unix.Fastq.sequence in
        let t, s = init conf opt read_size rp in
        t.Pd.merge s (t.Pd.paired fq1 fq2);
        `Set (t, s)
    | `Set (t, s) ->
        t.Pd.merge s (t.Pd.paired fq1 fq2);
        `Set (t, s)

  let across_fastq conf opt
    (* Fastq specific arguments. *)
    ?number_of_reads ~specific_reads file init =
    let f = single conf opt in
    try
      Fastq.fold ?number_of_reads ~specific_reads ~init file ~f
      |> function
          | `Setup _    -> eprintf "Didn't find any reads."
          | `Set (t, s) -> t.Pd.output s stdout
    with Pd.Fastq_items.Read_error_parsing e ->
      eprintf "%s" e

  let across_paired ~finish_singles conf opt
      (* Fastq specific arguments. *)
      ?number_of_reads ~specific_reads file1 file2 init =
    let f = paired conf opt in
    try
      begin
        if finish_singles then
          let ff = single conf opt in
          let fs = ff in
          Fastq.fold_paired_both ?number_of_reads ~specific_reads file1 file2
            ~init ~f ~ff ~fs
        else
          Fastq.fold_paired ?number_of_reads ~specific_reads file1 file2 ~init ~f
      end
      |> function
          | `BothFinished o
          | `FinishedSingle o
          | `OneReadPairedFinished (_, o)
          | `StoppedByFilter o
          | `DesiredReads o ->
              match o with
              | `Setup _    -> eprintf "Didn't find any reads."
              | `Set (t, s) -> t.Pd.output s stdout
    with Pd.Fastq_items.Read_error_parsing e ->
      eprintf "%s" e

end (* Regular *)

module Parallel = struct

  let init conf opt read_size rp =
    let ptlst =
      time (sprintf "Setting up ParPHMM transitions with %d read_size" read_size)
        (fun () -> rp read_size)
    in
    time "Allocating forward pass workspaces"
      (fun () -> Pdml.init conf opt read_size ptlst)

  let across_fastq conf opt
    (* Fastq specific arguments. *)
    ?number_of_reads ~specific_reads ~nprocs file driver state =
    let f = single conf opt in
    try
      Fastq.fold ?number_of_reads ~specific_reads ~init file ~f
      |> function
          | `Setup _    -> eprintf "Didn't find any reads."
          | `Set (t, s) -> t.Pd.output s stdout
    with Pd.Fastq_items.Read_error_parsing e ->
      eprintf "%s" e

  let across_paired ~finish_singles conf opt
      (* Fastq specific arguments. *)
      ?number_of_reads ~specific_reads file1 file2 init =
    let f = paired conf opt in
    try
      begin
        if finish_singles then
          let ff = single conf opt in
          let fs = ff in
          Fastq.fold_paired_both ?number_of_reads ~specific_reads file1 file2
            ~init ~f ~ff ~fs
        else
          Fastq.fold_paired ?number_of_reads ~specific_reads file1 file2 ~init ~f
      end
      |> function
          | `BothFinished o
          | `FinishedSingle o
          | `OneReadPairedFinished (_, o)
          | `StoppedByFilter o
          | `DesiredReads o ->
              match o with
              | `Setup _    -> eprintf "Didn't find any reads."
              | `Set (t, s) -> t.Pd.output s stdout
    with Pd.Fastq_items.Read_error_parsing e ->
      eprintf "%s" e


end (* Parallel *)

let type_
  (* Allele information source *)
    class1_gen_dir
    alignment_files merge_files distance
  (* Process *)
    skip_disk_cache
  (* What to do? *)
    fastq_file_lst number_of_reads specific_reads
    do_not_finish_singles
  (* options *)
    insert_p
    do_not_past_threshold_filter
    max_number_mismatches
    read_size_override
    not_band
    warmup
    number
    width
    likelihood_first
    zygosity_report_size
  (* how are we typing *)
    map_depth
    not_incremental_pairs
    forward_accuracy_opt
    number_processes_opt
    =
  Option.value_map forward_accuracy_opt ~default:()
    ~f:(fun fa -> ParPHMM.dx := fa);
  let band     =
    if not_band then
      None
    else
      Some { ParPHMM.warmup; number; width }
  in
  let alignment_files, merge_files =
    match class1_gen_dir with
    | None   -> alignment_files, merge_files
    | Some d -> [ d // "A_gen.txt"
                ; d // "B_gen.txt"
                ; d // "C_gen.txt"
                ], []
  in
  let past_threshold_filter = not do_not_past_threshold_filter in
  let incremental_pairs = not not_incremental_pairs in
  let finish_singles = not do_not_finish_singles in
  let conf = Pd.multiple_conf ~insert_p ?band ?max_number_mismatches
                ~past_threshold_filter ~incremental_pairs ()
  in
  let need_read_size_r =
    to_read_size_dependent
      ~alignment_files ~merge_files ~distance
      ~skip_disk_cache
  in
  let opt =
    { Pd.likelihood_first
    ; zygosity_report_size
    ; report_size = map_depth
    }
  in
  match need_read_size_r with
  | Error e           -> eprintf "%s" e
  | Ok need_read_size ->
      begin match number_processes_opt with
      | None  ->
        let init =
          match read_size_override with
          | None   -> `Setup need_read_size
          | Some r -> `Set (init conf opt r need_read_size)
        in
        begin match fastq_file_lst with
        | []              -> invalid_argf "Cmdliner lied!"
        | [fastq]         -> across_fastq conf opt
                                ?number_of_reads ~specific_reads fastq init
        | [read1; read2]  -> across_paired ~finish_singles conf opt
                                ?number_of_reads ~specific_reads read1 read2 init
        | lst             -> invalid_argf "More than 2, %d fastq files specified!"
                              (List.length lst)
        end
      | Some nprocs ->
          let init = 
      end

let () =
  let open Cmdliner in
  let open Common_options in
  let alignments_arg =
    let docv = "FILE" in
    let doc  = "File to lookup IMGT allele alignments. The alleles found in this \
                file will initially define the set of alleles to be used for \
                named locus. Supply multiple file (or merge) arguments to \
                compute the likelihood of a read against each locus and add to \
                the most likely (highest likelihood)." in
    Arg.(value & opt_all file [] & info ~doc ~docv ["alignments"])
  in
  let max_number_mismatches_arg =
    let docv = "POSITIVE INTEGER" in
    let doc = "Setup a filter on the reads to cancel evaluation once we've \
               seen this many mismatches." in
    Arg.(value & opt (some positive_int) None & info ~doc ~docv
          ["max-mismatches"])
  in
  let class1gen_arg =
    let docv  = "DIRECTORY" in
    let doc   = "Short-cut argument that expands the given dir to look for \
                  A_gen.txt, B_gen.txt and C_gen.txt. This overrides any \
                 alignment files or merge arguments." in
    Arg.(value & opt (some dir) None & info ~doc ~docv ["class1-gen"])
  in
  let do_not_use_incremental_pairs_flag =
    let doc   = "By default when performing paired typing, we use the first \
                 (as specified by the read found in the first file on the \
                 command line) pair, to determine which loci is the most \
                 likely. This is faster but potentially less accurate. \
                 To use both pairs pass this flag. "
    in
    Arg.(value & flag & info ~doc ["do-not-incremental-pair"])
  in
  let type_ =
    let version = "0.0.0" in
    let doc = "Use a Parametric Profile Hidden Markov Model of HLA allele to \
               type fastq samples." in
    let bug =
      sprintf "Browse and report new issues at <https://github.com/hammerlab/%s"
        repo
    in
    let man =
      [ `S "AUTHORS"
      ; `P "Leonid Rozenberg <leonidr@gmail.com>"
      ; `Noblank
      ; `S "BUGS"
      ; `P bug
      ]
    in
    Term.(const type_
            (* Allele information source *)
            $ class1gen_arg
            $ alignments_arg $ merges_arg $ defaulting_distance_flag
            (* What to do ? *)
            $ no_cache_flag
            (* What are we typing *)
            $ fastq_file_arg $ num_reads_arg $ specific_read_args
            $ do_not_finish_singles_flag
            (* options. *)
            $ insert_probability_arg
            $ do_not_past_threshold_filter_flag
            $ max_number_mismatches_arg
            $ read_size_override_arg
            $ not_band_flag
            $ band_warmup_arg
            $ number_bands_arg
            $ band_width_arg
            $ likelihood_first_flag
            $ zygosity_report_size_arg
            (* How are we typing *)
            $ map_depth_arg
            $ do_not_use_incremental_pairs_flag
            $ forward_pass_accuracy_arg
            $ number_processes_arg
            (* $ map_allele_arg
            $ filter_flag $ multi_pos_flag $ stat_flag $ likelihood_error_arg
              $ upto_kmer_hood_arg
              $ allto_kmer_hood_arg
            (* Output *)
            $ print_top_flag
              $ do_not_normalize_flag
              $ bucket_arg
              $ error_output_flag
              $ reduce_resolution_arg *)
        , info app_name ~version ~doc ~man)
  in
  match Term.eval type_ with
  | `Ok ()           -> exit 0
  | `Error _         -> failwith "cmdliner error"
  | `Version | `Help -> exit 0
