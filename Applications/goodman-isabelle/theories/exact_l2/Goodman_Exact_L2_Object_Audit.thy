theory Goodman_Exact_L2_Object_Audit
  imports Goodman_Exact_L2_Object_Refutation
begin

ML \<open>
local
  val names = ["gi_exact_L2_root_instance", "gi_exact_L2_root_implies_fixed_stock",
    "gi_exact_generic_L2_false_at_root", "gi_exact_native_L2_formula_false_at_root",
    "gi_exact_native_L2_formula_not_global", "gi_exact_QLN_background_not_proves_L2"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-l2-object: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-l2-object: residual obligations in " ^ name)
  val report = "EXACT-L2-OBJECT-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: Actual old and translated native L2 formula false at root under generic exact Pure/Fun; global validity fails and the explicit no-PP QLN background does not derive it. Complete fixed logical stock, typed native assignment and rich names retained. Not all-world falsity, arbitrary enlarged stock, PP model, or PP contradiction. HOL-ZF foundations retained.\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-l2-object-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-l2-object-statements.txt")) [XML.Text statements]
in end
\<close>

end
