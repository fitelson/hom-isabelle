theory Goodman_T45_Audit
  imports Goodman_T45_Transfer
begin

section \<open>T4 and T5: exact statements and kernel trust checks\<close>

ML \<open>
local
  val names = ["gi_T4_source_stock", "gi_T4_fun_prime_at_admitted", "gi_T4_parameter_admitted",
    "gi_T4_quantified_admitted", "gi_T4_parameter_translated", "gi_T4_quantified_translated",
    "gb_T4_fun_prime_at_proposition", "gi_T4_fun_prime_application_translation",
    "gi_T4_claim_translation", "gi_T4_no_higher_fun_prime", "gi_T5_source_stock",
    "gi_T5_proliferation_admitted", "gi_T5_no_two_admitted", "gi_T5_proliferation_translated",
    "gi_T5_no_two_translated", "gi_T5_fun_prime_head_translation", "gi_T5_claim_translation",
    "gi_T5_no_two_claim_translation", "gi_T5_proliferation", "gi_T5_no_two"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm)) (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "t45: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("t45: residual obligations in " ^ name)
  val report = "T45-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: T4 over logical purity/application only, with explicit higher-type purity antecedent. T5 over purity/application/PP with fun-prime antecedent retained. No consistency or unconditional existence claim.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t45-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t45-statements.txt")) [XML.Text statements]
in end
\<close>

end
