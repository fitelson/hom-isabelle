theory Goodman_Control_Audit
  imports Goodman_Control_Transfer
begin
ML \<open>
local
  val names = ["gi_control_source_closed",
    "gb_control_axioms_language",
    "gi_control_axiom_from_native",
    "gi_control_native_preservation",
    "gi_control_J_admitted",
    "gi_control_S_admitted",
    "gi_control_square_admitted",
    "gi_control_E_admitted",
    "gi_control_classifier_pure",
    "gi_control_operator_pure",
    "gi_control_J_squared_false",
    "gi_control_nonuniform_at_fun_prime",
    "gi_control_cube",
    "gi_control_square_idempotent",
    "gi_control_range_implies_identity",
    "gi_control_range_iff_identity",
    "gi_control_no_range_negative_square",
    "gi_control_fun_prime_heredity",
    "gi_control_reflects_fun_prime"]
  val entries = map (fn n => (n, Proof_Context.get_thm @{context} n)) names
  val _ = if null (Thm_Deps.all_oracles (map #2 entries)) then () else error "control oracle"
  fun check (n,t) = if null (Thm.hyps_of t) andalso null (Thm.tpairs_of t)
    then n ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of t)
    else error ("control residual obligations: " ^ n)
  val report = "CONTROL-AUDIT: " ^ string_of_int (length entries) ^ " clean endpoints\n"
    ^ "SCOPE: native PP core for J/S purity and nonuniformity implication; add zeroary Exhaustion for iteration/range/heredity. Existence and E antecedents retained; targets explicitly translated, no range existence/model claim.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "control-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (n,t) => n ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of t)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "control-statements.txt")) [XML.Text statements]
in end
\<close>
end
