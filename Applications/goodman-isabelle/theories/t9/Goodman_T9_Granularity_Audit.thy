theory Goodman_T9_Granularity_Audit
  imports Goodman_T9_Granularity_Bounds
begin
ML \<open>
local
  val names = map (fn n => "gi_T9_native_purity." ^ n)
    ["gi_T9_kind_sized_group_impossible", "gi_T9_kind_bounded_descriptions_impossible", "gi_T9_countable_group_impossible"]
  val entries = map (fn n => (n, Proof_Context.get_thm @{context} n)) names
  val _ = if null (Thm_Deps.all_oracles (map #2 entries)) then () else error "T9 granularity oracle"
  fun check (n,t) = if null (Thm.hyps_of t) andalso null (Thm.tpairs_of t)
    then n ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of t)
    else error ("T9 granularity residual obligations: " ^ n)
  val report = "T9-GRANULARITY-AUDIT: " ^ string_of_int (length entries) ^ " clean endpoints\n"
    ^ "SCOPE: actual group/kinds; native PP core, full external PC, L2, exists-fun-prime; additional cardinal ceilings explicit.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-granularity-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (n,t) => n ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of t)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-granularity-statements.txt")) [XML.Text statements]
in end
\<close>
end
