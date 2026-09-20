theory Goodman_M5_Object_Audit
  imports Goodman_M5_Object_Transfer
begin

ML \<open>
local
  val names = ["CEV_Goodman_M5_collision", "CEV_M5_inverse_witness_injective",
    "CEV_M5_reversible_injective", "CEV_Goodman_M5_collision_operator_not_reversible",
    "gi_M5_collision_source", "gi_M5_collision_in_signature", "gi_M5_nonreversible_in_signature",
    "gi_M5_inverse_witness_injective", "gi_M5_reversible_injective"]
  val entries = map (fn n => (n, Proof_Context.get_thm @{context} n)) names
  val _ = if null (Thm_Deps.all_oracles (map #2 entries)) then () else error "M5 object oracle dependency"
  fun check (n,t) = if null (Thm.hyps_of t) andalso null (Thm.tpairs_of t)
    then n ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of t)
    else error ("M5 object residual obligations: " ^ n)
  val report = "M5-OBJECT-AUDIT: " ^ string_of_int (length entries) ^ " clean endpoints\n"
    ^ "SCOPE: inverse/reversible injectivity in empty native extension; collision/nonreversibility in explicit closed image axiom stocks. No discharge of fun-prime added axiom to a local antecedent. Arbitrary admitted target signatures.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-object-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (n,t) => n ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of t)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "m5-object-statements.txt")) [XML.Text statements]
in end
\<close>

end
