theory Goodman_Granularity_Audit
  imports Goodman_Granularity_Transfer
begin
ML \<open>
local
  val names = ["gi_granularity_logical_builder_pure",
    "gi_granularity_pure_agreement",
    "gi_granularity_pure_disagreement",
    "gi_granularity_conditional_source",
    "gi_granularity_source_closed",
    "gb_granularity_axioms_language",
    "gi_granularity_axiom_from_native",
    "gi_granularity_admitted",
    "gi_granularity_iff_truth_uniform",
    "pp_surjective_truth_fibre_congruence_imp_uniform",
    "pp_bijective_truth_fibre_congruence_imp_uniform",
    "pp_fregean_granularity_imp_uniform",
    "pp_fregean_granularity_excludes_third_proposition",
    "pp_QLN_truth_uniform_iff_agreement_noncontingent",
    "pp_attack2_kind_sized_group_refutes_attack3",
    "pp_attack2_kind_bounded_descriptions_refute_attack3",
    "pp_attack2_countable_group_refutes_attack3"]
  val entries = map (fn n => (n, Proof_Context.get_thm @{context} n)) names
  val _ = if null (Thm_Deps.all_oracles (map #2 entries)) then () else error "granularity oracle"
  fun check (n,t) = if null (Thm.hyps_of t) andalso null (Thm.tpairs_of t)
    then n ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of t)
    else error ("granularity residual obligations: " ^ n)
  val report = "GRANULARITY-AUDIT: " ^ string_of_int (length entries) ^ " clean endpoints\n"
    ^ "SCOPE: native logical purity/application/unary QLN with Pure(Z) and Fun(r) as local antecedents. No PP, Persistence or zeroary Exhaustion added. Separate historical HOL cardinal results retain explicit surjectivity, truth/congruence and size premises.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "granularity-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (n,t) => n ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of t)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "granularity-statements.txt")) [XML.Text statements]
in end
\<close>
end
