theory Goodman_T9_L2_Semantics_Audit
  imports Goodman_T9_L2_Semantics
begin

ML \<open>
local
  val global_names = ["gi_T9_L2_vocabulary", "gi_T9_native_L2_language"]
  val local_names = ["gi_T9_pure_formula_root_iff", "gi_T9_reversible_body_root",
    "gi_T9_reversible_formula_root_iff", "gi_T9_group_formula_root_iff",
    "gi_T9_same_kind_formula_root_iff", "gi_T9_L2_root_instance",
    "gi_T9_native_L2_root_implies_source", "gi_T9_native_L2_root_instance",
    "gi_T9_L2_formula_implies_root_L2", "gi_T9_native_L2_implies_root_L2"]
  val names = global_names @ map (fn name => "pp_e_constants." ^ name) local_names
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 12 then () else error "T9-L2-semantics: unexpected count"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "T9-L2-semantics: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("T9-L2-semantics: residual obligations in " ^ name)
  val report = "T9-L2-SEMANTICS-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Arbitrary typed C on Bacon's exact carriers, not the fixed generic interpretation. Root Pure/reversible/group/same-kind evaluation matches actual root-pure value definitions. The actual L2 formula implies the value-level condition used by the T9 selector; native translated-L2 input has explicit names/environment guards, source vocabulary and derived target-language membership. Pure-inverse existence is not confused with purity of its argument. HOL-ZF and pp_e_constants assumptions retained; no proof of L2 from PP, no PC or consistency claim.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-l2-semantics-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t9-l2-semantics-statements.txt")) [XML.Text statements]
in end
\<close>

end
