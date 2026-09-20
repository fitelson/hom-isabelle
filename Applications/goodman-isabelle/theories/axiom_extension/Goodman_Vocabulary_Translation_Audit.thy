theory Goodman_Vocabulary_Translation_Audit
  imports Goodman_Translation_Support Goodman_Integration_Audit
begin

section \<open>Audit of vocabulary, axiom packages and syntactic translation\<close>

text \<open>
  Scope: candidate full-F/minimal book formulas, their typing and closure,
  and constructor-to-book language preservation. No CEV+ derivation
  preservation, model soundness, or denotational-stock equivalence is claimed.
\<close>

ML \<open>
local
  val names =
    ["gb_signature_countable", "gb_Pure_language", "gb_Fun_language",
     "gb_pure_language", "gb_fun_language", "gb_names_type", "gb_names_distinct",
     "gb_purity_of_pure_language", "gb_purity_of_fun_language", "gb_target_PP_language",
     "gb_application_closure_language", "gb_persistence_language",
     "gb_unique_fundamental_language", "gb_no_fundamentals_language", "gb_basic_axioms_closed",
     "gb_zeroary_recombination_language", "gb_zeroary_exhaustion_language",
     "gb_QLN_guard_language", "gb_QLN_box_language", "gb_QLN_all_language",
     "gb_unary_recombination_language", "gb_unary_exhaustion_language", "gb_QLN_axioms_closed",
     "gb_closed_logical_in_signature", "gb_purity_schema_language", "gb_purity_schema_closed",
     "gb_background_axioms_language", "gb_background_axioms_closed",
     "gb_recombination_PP_language", "gb_recombination_PP_closed",
     "gb_QLN_PP_language", "gb_QLN_PP_closed", "gb_repaired_PP_language", "gb_repaired_PP_closed",
     "gb_persistence_schema_language", "gb_persistence_schema_closed",
     "gb_package_inclusions", "gb_target_PP_necessitated",
     "gb_QLN_consistency_implies_recombination_consistency",
     "gi_chart_extension", "gi_chart_variable", "gi_to_book_language",
     "gi_binder_chart_distinct", "gi_target_PP_shape",
     "gi_to_book_fv_subset", "gi_closed_translation", "gi_closed_logical_translation",
     "gi_translated_logical_purity_instance"]
  val resolved = maps (fn name =>
    map_index (fn (i, thm) => (name ^ "[" ^ string_of_int (i + 1) ^ "]", thm))
      (Proof_Context.get_thms @{context} name)) names
  val _ = if null (Thm_Deps.all_oracles (map #2 resolved)) then ()
    else error "Vocabulary/translation audit: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises="
      ^ string_of_int (Thm.nprems_of thm)
    else error ("Vocabulary/translation audit: residual kernel obligations in " ^ name)
  val report = "GOODMAN-VOCABULARY-TRANSLATION-AUDIT: "
    ^ string_of_int (length resolved) ^ " clean endpoints; syntactic scope only\n"
    ^ cat_lines (map check resolved) ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "vocabulary-translation-audit.txt")) [XML.Text report]
  val _ = writeln report
in end
\<close>

end
