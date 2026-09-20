theory Goodman_Native_T6_Extras_Audit
  imports Goodman_Native_T6_Extras
begin

section \<open>Kernel audit and full statements for the independent native extras\<close>

ML \<open>
local
  val names = ["gi_T6_identity_native_translation",
    "gi_T6_negation_native_translation",
    "gi_T6_compose_variables_native_translation",
    "gi_T6_fun_prime_variable_native_translation",
    "gi_T6_reversible_variable_native_translation",
    "gi_T6_group_variable_native_translation",
    "gi_T6_same_kind_variables_native_translation",
    "gi_T6_strong_kind_variables_native_translation",
    "gi_T6_truth_preserving_variable_native_translation",
    "gi_T6_truth_flipping_variable_native_translation",
    "gi_T6_biconditional_builder_native_translation",
    "gi_T6_biconditional_operator_variable_native_translation",
    "gi_T6_biconditional_member_variable_native_translation",
    "gi_T6_spec_instantiated_variable_native_translation",
    "gi_T6_spec_only_fun_prime_variable_native_translation",
    "gi_T6_spec_rigid_variable_native_translation",
    "gi_T6_rigid_specification_variable_native_translation",
    "gi_L2_native_translation",
    "gi_strong_L2_native_translation",
    "gi_Inv_native_translation",
    "gi_WI_native_translation",
    "gi_TU_native_translation",
    "gi_RS_native_translation",
    "gi_native_T6_extra_language_closed",
    "gb_L2_language_closed",
    "gb_strong_L2_language_closed",
    "gb_Inv_language_closed",
    "gb_WI_language_closed",
    "gb_TU_language_closed",
    "gb_RS_language_closed"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "native-T6-extras: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("native-T6-extras: residual obligations in " ^ name)
  val report = "NATIVE-T6-EXTRAS-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Independent named L2,strongL2,Inv,WI,TU,RS with literal earlier-encoding correspondence and declared-signature typing/closedness. Native group requires pure operator and pure two-sided inverse; same-kind composition is on input side; strongL2 retains q=Zp; RS retains nonempty pure selector, only-fun-prime and both selected arguments in rigidity. Material biconditional explicitly expands to two implications, not propositional identity. Variable correspondence uses protected binder charts; no arbitrary-argument literal shift claim or derivation of extras from PP.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "native-t6-extras-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "native-t6-extras-statements.txt")) [XML.Text statements]
in end
\<close>

end

