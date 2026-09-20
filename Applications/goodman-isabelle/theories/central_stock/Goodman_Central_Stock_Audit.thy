theory Goodman_Central_Stock_Audit
  imports Goodman_Central_Stock_T6
begin

section \<open>Audit the native witness and the four repaired-stock routes\<close>

ML \<open>
local
  val integration_names =
    ["gb_fun_prime_with_names_language", "gb_fun_prime_with_names_fv",
     "gb_exists_fun_prime_names", "gb_exists_fun_prime_language", "gb_exists_fun_prime_closed",
     "gi_exists_fun_prime_translation", "gi_repaired_native_exists_fun_prime",
     "gi_central_T6_language", "gi_central_T6_support", "gi_central_T6_refutation_transfer",
     "gi_central_T6_Inv_refutation", "gi_central_T6_TU_refutation",
     "gi_central_T6_WI_refutation", "gi_central_T6_RS_refutation"]
  val replay_names =
    ["CEV_QSS_modal_core_from_recombination",
     "CEV_QSS_from_recombination_with_zeroary_exhaustion_parameter",
     "CEV_QSS_from_recombination_with_zeroary_exhaustion",
     "CEV_exists_fun_prime_from_QSS_and_unique_fundamentality",
     "CEV_exists_fun_prime_from_recombination_with_zeroary_exhaustion",
     "CEV_Goodman_T6_Inv_repaired_central_stock", "CEV_Goodman_T6_TU_repaired_central_stock",
     "CEV_Goodman_T6_WI_repaired_central_stock", "CEV_Goodman_T6_RS_repaired_central_stock"]
  val names = integration_names @ replay_names
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Central-stock audit: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises="
      ^ string_of_int (Thm.nprems_of thm)
    else error ("Central-stock audit: residual kernel obligations in " ^ name)
  val report = "GOODMAN-CENTRAL-STOCK-AUDIT: "
    ^ string_of_int (length integration_names) ^ " clean integration endpoints; "
    ^ string_of_int (length replay_names) ^ " clean historical replay endpoints (counted separately)\n"
    ^ "SCOPE: native existence of fun-prime from the repaired central stock; four T6 refutations with route extras retained.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "central-stock-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) =>
    name ^ ":\n" ^ XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "central-stock-statements.txt")) [XML.Text statements]
in end
\<close>

end
