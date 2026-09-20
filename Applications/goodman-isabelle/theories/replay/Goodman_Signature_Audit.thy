theory Goodman_Signature_Audit
  imports Goodman_T6_Restricted_Signature
begin

section \<open>Kernel audit of signature conservativity and its applications\<close>

ML \<open>
local
  val names =
    ["gi_extension_retraction_supportI", "gi_extension_retraction_apply",
     "gi_extension_retraction_support_exists", "gi_goodman_foreign_constants_eliminate",
     "gi_goodman_signature_mono", "gi_goodman_signature_conservativity",
     "gi_goodman_consistency_universal_iff", "gi_CEV_conclusion_language",
     "gi_CEV_axiom_preservation_in_signature", "gi_CEV_closed_refutation_in_signature",
     "gi_native_conclusion_restrict", "gi_background_preservation_in_signature",
     "gi_recombination_PP_preservation_in_signature", "gi_QLN_PP_preservation_in_signature",
     "gi_repaired_PP_preservation_in_signature", "gi_persistent_QLN_language",
     "gi_persistent_QLN_PP_preservation_in_signature",
     "gi_recombination_PP_consistency_in_signature", "gi_QLN_PP_consistency_in_signature",
     "gi_repaired_PP_consistency_in_signature", "gi_persistent_QLN_PP_consistency_in_signature",
     "gi_exists_fun_prime_admitted", "gi_L2_admitted", "gi_Inv_admitted", "gi_TU_admitted",
     "gi_WI_admitted", "gi_strong_L2_admitted", "gi_RS_admitted",
     "gi_T6_extra_inventory_typed", "gi_T6_extra_inventory_admitted",
     "gi_T6_signature_support_language", "gi_T6_image_stocks_in_signature_support",
     "gi_T6_native_stock_in_signature_support", "gi_T6_refutation_restrict",
     "gi_T6_Inv_refutation_in_signature", "gi_T6_TU_refutation_in_signature",
     "gi_T6_WI_refutation_in_signature", "gi_T6_RS_refutation_in_signature",
     "gi_T6_native_Inv_refutation_in_signature", "gi_T6_native_TU_refutation_in_signature",
     "gi_T6_native_WI_refutation_in_signature", "gi_T6_native_RS_refutation_in_signature"]
  val resolved = maps (fn name =>
    map_index (fn (i, thm) => (name ^ "[" ^ string_of_int (i + 1) ^ "]", thm))
      (Proof_Context.get_thms @{context} name)) names
  val _ = if null (Thm_Deps.all_oracles (map #2 resolved)) then ()
    else error "Signature audit: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises="
      ^ string_of_int (Thm.nprems_of thm)
    else error ("Signature audit: residual kernel obligations in " ^ name)
  val report = "GOODMAN-SIGNATURE-AUDIT: "
    ^ string_of_int (length resolved) ^ " clean endpoints\n"
    ^ "SCOPE: C+[T] signature conservativity; requested-signature CEV+ preservation; native packages and all four T6 routes in gb_signature.\n"
    ^ "Axioms and conclusion must be in the target language. No model, consistency, reverse proof, or denotational-stock theorem is inferred.\n"
    ^ cat_lines (map check resolved) ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "signature-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) =>
    name ^ ":\n" ^ XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) resolved)
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "signature-statements.txt")) [XML.Text statements]
in end
\<close>

end
