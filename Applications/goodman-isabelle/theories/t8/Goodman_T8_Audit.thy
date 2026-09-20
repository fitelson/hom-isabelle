theory Goodman_T8_Audit
  imports Goodman_T8_Transfer
begin

section \<open>T8a–c: actual object-language conclusions and exact premises\<close>

ML \<open>
local
  val names = ["gi_T8_same_kind_admitted", "gi_T8_base_admitted", "gi_T8_representation_admitted",
    "gi_T8_not_same_all_admitted", "gi_T8_pairwise_kind_admitted", "gi_T8_base_kind_claim_admitted",
    "gi_T8_disjoin_admitted", "gi_T8_kind_atom_admitted", "gi_T8_kind_property_admitted",
    "gi_T8_growth_operator_admitted", "gi_T8_neq_all_admitted", "gi_T8_pairwise_distinct_admitted",
    "gi_T8_growth_claim_admitted", "gi_T8_growth_result_admitted", "gi_T8b_kind_uniqueness_translated",
    "gi_T8a_pair_core", "gi_T8a_pair_empty", "gi_T8a_Id_Box_translated", "gi_T8a_Id_Diamond_translated",
    "gi_T8a_Box_Diamond_translated", "gi_T8a_Id_Ktop_translated", "gi_T8a_Box_Ktop_translated",
    "gi_T8a_Diamond_Ktop_translated", "gi_T8a_Id_Kbot_translated", "gi_T8a_Box_Kbot_translated",
    "gi_T8a_Diamond_Kbot_translated", "gi_T8a_Ktop_Kbot_translated", "gi_T8a_five_kinds_translated",
    "gi_T8_stocks_as_T7", "gi_T8_L2_native_preservation", "gi_T8c_growth_translated",
    "gi_T8c_operator_purity", "gi_T8_neq_all_translation", "gi_T8_pairwise_distinct_translation",
    "gi_T8c_listed_operators_pure", "gi_T8_growth_terms_length", "gi_T8_growth_values_length",
    "gi_T8_growth_claim_translation", "gi_T8c_growth", "gi_T8c_closed_translated",
    "gi_T8_growth_result_translation", "gi_T8c_closed", "gi_T8_full_to_repaired",
    "gi_T8c_repaired_central_stock"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "t8: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("t8: residual obligations in " ^ name)
  val report = "T8-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: T8b over L2 alone; ten T8a pair separations and combined five-kind claim retain original stocks and fun-prime antecedents. T8c proves 31 operator and 31 value inequalities, with separate purity theorem. No 31 kinds or iteration/infinitude claim; repaired central stock retains L2.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t8-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t8-statements.txt")) [XML.Text statements]
in end
\<close>

end
