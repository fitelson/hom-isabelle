theory Goodman_Exact_Frame_Representation_Audit
  imports Goodman_Exact_Frame_Representation
begin

section \<open>Kernel audit of the named frame-representation transfer\<close>

ML \<open>
local
  val names = ["gi_exact_minimal_logical_in_signature",
    "gi_exact_named_in_signature_encoding",
    "gi_exact_named_in_signature_decode_iff",
    "gi_exact_named_in_signature_iff_ssignature",
    "gi_exact_named_sentence_decode",
    "gi_exact_named_sentence_from_signature",
    "gi_exact_named_frame_satisfiable_decode",
    "gi_exact_named_frame_consistent_decode",
    "gi_exact_named_frame_representation_branch",
    "gi_exact_named_frame_representation_diamond",
    "gi_exact_named_frame_satisfiable_at_branch",
    "gi_exact_named_frame_valid_decode",
    "gi_exact_named_frame_completeness_branch",
    "gi_exact_named_frame_completeness_box",
    "gi_exact_named_frame_valid_iff_negation_unsatisfiable",
    "gi_exact_complete_constants_model",
    "pp_e_frame_consistent_iff_model",
    "pp_e_consistent_sentence_enum_range",
    "pp_e_enumerated_sentence_true_at_branch",
    "pp_e_Bacon_consistency_representation",
    "pp_e_Bacon_exact_completeness"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-frame-representation: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-frame-representation: residual obligations in " ^ name)
  val report = "EXACT-FRAME-REPRESENTATION-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Preserved enumeration and frame-completeness snapshots selected (sessions Goodman_Exact_Enumeration, Goodman_Exact_Frame_Completeness) and Bacon's consistency representation transferred to closed named string sentences of the t-generated fragment via the decoder: frame satisfiability (truth at the root of some typed interpretation on the fixed frame) iff truth at some substitution of the glued complete model iff native diamond at its root; companion: frame validity (truth at the root of every typed interpretation) iff truth at every substitution of the complete model iff native box at its root. Consistency here is frame satisfiability, not syntactic H consistency or H completeness. The five pp_e_ rows are the preserved snapshot results now in the selected closure.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-frame-representation-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-frame-representation-statements.txt")) [XML.Text statements]
in end
\<close>

end
