theory Goodman_Binding_Conversion_Audit
  imports Goodman_Named_Root_Conversion Goodman_Vocabulary_Translation_Audit
begin

section \<open>Audit of binding and conversion bridges\<close>

text \<open>
  Scope: expansion substitution/renaming, re-encoding, α alignment, and
  typed named root βη. Raw contextual steps are checked only at the
  intermediate expansion level. This is not H/CEV+ derivation transport.
\<close>

ML \<open>
local
  val names =
    ["gi_closed_code_rename", "gi_closed_code_subst", "gi_closed_code_stack",
     "gi_expand_rename", "gi_expand_shift", "gi_expand_lift_subst",
     "gi_expand_subst", "gi_expand_subst0",
     "gi_to_book_relative_encoding", "gi_chart_is_named_chart", "gi_chart_nth_index",
     "gi_to_book_empty_encoding",
     "gi_expand_beta", "gi_expand_eta", "gi_expand_compatible",
     "gi_expand_beta_context", "gi_expand_eta_context",
     "gi_to_book_rename_alpha", "gi_to_book_shift_alpha",
     "gi_closed_free_for", "gi_translation_free_for", "gi_source_beta_deterministic",
     "gi_to_book_subst0_alpha", "gi_to_book_named_language", "gi_constants_rename",
     "gi_to_book_beta_root", "gi_to_book_eta_root"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Binding/conversion audit: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises="
      ^ string_of_int (Thm.nprems_of thm)
    else error ("Binding/conversion audit: residual kernel obligations in " ^ name)
  val report = "GOODMAN-BINDING-CONVERSION-AUDIT: "
    ^ string_of_int (length facts) ^ " clean endpoints; no proof-system correspondence claim\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "binding-conversion-audit.txt")) [XML.Text report]
  val _ = writeln report
in end
\<close>

end
