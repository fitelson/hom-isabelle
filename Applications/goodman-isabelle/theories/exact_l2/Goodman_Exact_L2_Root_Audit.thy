theory Goodman_Exact_L2_Root_Audit
  imports Goodman_Exact_L2_Root_Semantics
begin

ML \<open>
local
  val names = ["gi_exact_root_eqv", "gi_exact_root_logical_stock",
    "gi_exact_root_unary_stock", "gi_exact_raw_at_extract",
    "gi_exact_raw_operator_injective", "gi_exact_raw_operator_eq_iff",
    "gi_exact_raw_application_eq_iff", "gi_exact_eval_compose",
    "gi_exact_value_compose_member", "gi_exact_raw_value_compose"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-l2-root: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-l2-root: residual obligations in " ^ name)
  val report = "EXACT-L2-ROOT-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: Actual equality and literal denotation stock only at the root; faithful raw unary representation and exact composition. Typed carrier premises retained. These helpers alone do not evaluate L2. HOL-ZF foundations retained.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-l2-root-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-l2-root-statements.txt")) [XML.Text statements]
in end
\<close>

end
