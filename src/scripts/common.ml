
(** Common script declarations *)

let time s f =
  let n = Sys.time () in
  let r = f () in
  Printf.printf "%-10s:%f\n" s (Sys.time () -. n);
  r

let (//) = Filename.concat
let imgthla_dir =
  try Sys.getenv "IMGTHLA_DIR"
  with _ -> "../foreign/IMGTHLA"

let to_alignment_file f = imgthla_dir // "alignments" // (f ^ ".txt")
let to_fasta_file f = imgthla_dir // "fasta" // (f ^ ".fasta")
let default_file = to_alignment_file "A_nuc"

let to_merge_prefix p = imgthla_dir // "alignments" // p

let common_alignment_files =
  [ "A_nuc"
  ; "B_nuc"
  ; "C_nuc"
  ; "DMA_nuc"
  ; "DMB_nuc"
  ; "DOA_nuc"
  ; "DOB_nuc"
  ; "DPA1_nuc"
  ; "DPB1_nuc"
  ; "DPB2_nuc"
  ; "DQA1_nuc"
  ; "DQB1_nuc"
  ; "DRA_nuc"
  ; "DRB_nuc"
  ]

let all_alignment_files =
  [ "A_gen"
  ; "A_nuc"
  ; "B_gen"
  ; "B_nuc"
  ; "C_gen"
  ; "C_nuc"
(*  ; "../foreign/IMGTHLA/alignments/ClassI_nuc.txt" screw your broken alignment! *)
  ; "DMA_gen"
  ; "DMA_nuc"
  ; "DMB_gen"
  ; "DMB_nuc"
  ; "DOA_gen"
  ; "DOA_nuc"
  ; "DOB_gen"
  ; "DOB_nuc"
  ; "DPA1_gen"
  ; "DPA1_nuc"
  ; "DPB1_gen"
  ; "DPB1_nuc"
  ; "DPB2_gen"
  ; "DPB2_nuc"
  ; "DQA1_gen"
  ; "DQA1_nuc"
  ; "DQB1_gen"
  ; "DQB1_nuc"
  ; "DRA_gen"
  ; "DRA_nuc"
  ; "DRB1_gen"
  ; "DRB3_gen"
  ; "DRB4_gen"
  ; "DRB_nuc"
  ; "E_gen"
  ; "E_nuc"
  ; "F_gen"
  ; "F_nuc"
  ; "G_gen"
  ; "G_nuc"
  ; "HFE_gen"
  ; "HFE_nuc"
  ; "H_gen"
  ; "H_nuc"
  ; "J_gen"
  ; "J_nuc"
  ; "K_gen"
  ; "K_nuc"
  ; "L_gen"
  ; "L_nuc"
  ; "MICA_gen"
  ; "MICA_nuc"
  ; "MICB_gen"
  ; "MICB_nuc"
  ; "P_gen"
  ; "TAP1_gen"
  ; "TAP1_nuc"
  ; "TAP2_gen"
  ; "TAP2_nuc"
  ; "V_gen"
  ; "V_nuc"
  ; "Y_gen"
  ; "Y_nuc"
  ]
