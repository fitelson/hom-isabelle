theory Goodman_T9_Cardinal_Audit
  imports Goodman_T9_Cardinal
begin

section \<open>Kernel audit of T9 for actual exact values and kinds\<close>

ML \<open>
local
  val names = ["gi_T9_infinite_product_bound",
    "gi_T9_product_power_dichotomy",
    "gi_T9_native_purity.gi_T9_pure_kind_member",
    "gi_T9_native_purity.gi_T9_cardinal_code_injective",
    "gi_T9_native_purity.gi_T9_cardinal_code_range",
    "gi_T9_native_purity.gi_T9_pure_le_kinds_times_group",
    "gi_T9_native_purity.gi_T9_kind_selector_range",
    "gi_T9_native_purity.gi_T9_powerset_kinds_le_pure",
    "gi_T9_native_purity.gi_T9_native_counting_bound",
    "gi_T9_native_purity.gi_T9_native_cardinal_dichotomy",
    "gi_T9_native_purity.gi_T9_infinite_kinds_group_bound"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "T9-cardinal: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("T9-cardinal: residual obligations in " ^ name)
  val report = "T9-CARDINAL-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Actual exact root-pure unary values P, actual right-composition kinds K and actual pure invertible group: |Pow K|<=|P|<=|K times Group|, hence finite K or |Pow K|<=|Group|. Native-purity locale, full external unary PC, semantic root L2 and typed fun-prime witness retained. No abstract fibre-code or selector assumption remains. Infinitude itself is not claimed; last corollary displays it as a premise. No model existence; HOL-ZF foundations retained.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-cardinal-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-cardinal-statements.txt")) [XML.Text statements]
in end
\<close>

end

