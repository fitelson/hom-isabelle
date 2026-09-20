theory Goodman_T9_Kind_Selector_Audit
  imports Goodman_T9_Kind_Selector
begin

ML \<open>
local
  val names = map (fn n => "gi_T9_native_purity." ^ n)
    ["gi_T9_union_kinds_pure", "gi_T9_member_kind_iff",
     "gi_T9_member_union_kinds_iff", "gi_T9_kind_selector_pure",
     "gi_T9_kind_selector_spec", "gi_T9_kind_selector_injective"]
  val entries = map (fn n => (n, Proof_Context.get_thm @{context} n)) names
  val _ = if null (Thm_Deps.all_oracles (map #2 entries)) then () else error "T9 kind selector oracle"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("T9 kind selector residual obligations: " ^ name)
  val report = "T9-KIND-SELECTOR-AUDIT: " ^ string_of_int (length entries) ^ " clean endpoints\n"
    ^ "SCOPE: actual kinds and pure unary values; full external unary PC, semantic root L2 and typed fun-prime witness retained. Powerset selector injection, not model existence.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-kind-selector-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-kind-selector-statements.txt")) [XML.Text statements]
in end
\<close>

end
