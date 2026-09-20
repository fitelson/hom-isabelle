theory Goodman_T2bc_Audit
  imports Goodman_T2bc_Transfer
begin

section \<open>Audit of the displayed integration endpoints\<close>

ML \<open>
local
  val names = ["gi_T2_min_axioms_closed",
    "gb_T2_min_axioms_language",
    "gb_T2_min_axioms_closed",
    "gi_T2_min_stock_inclusion",
    "gi_T2_min_axiom_from_native",
    "gi_T2_min_native_preservation",
    "gi_T2_fun_prime_admitted",
    "gi_T2b_nontriviality_admitted",
    "gi_T2c_parameter_admitted",
    "gi_T2c_quantified_admitted",
    "gi_T2b_nontriviality_translated",
    "gi_T2b_truth_not_fun_prime_translated",
    "gi_T2b_falsity_not_fun_prime_translated",
    "gi_T2c_parameter_translated",
    "gi_T2c_quantified_translated",
    "gb_T2_fun_prime_binders",
    "gb_T2_fun_prime_at_language",
    "gb_T2_fun_prime_at_fv",
    "gi_T2_fun_prime_var_translation",
    "gi_T2b_claim_translation",
    "gi_T2b_nontriviality",
    "gi_T2_diamond_translation",
    "gb_T2c_proposition_binders_distinct",
    "gi_T2c_claim_translation",
    "gi_T2c_attainment"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "t2bc: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("t2bc: residual obligations in " ^ name)
  val report = "T2BC-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: T2b/T2c in the minimal native purity/application stock; fun-prime antecedents retained; source truth/modal representatives explicit.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t2bc-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t2bc-statements.txt")) [XML.Text statements]
in end
\<close>

end

