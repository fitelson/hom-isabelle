theory Goodman_T3_Audit
  imports Goodman_T3_Transfer
begin

section \<open>T3: kernel proof objects and exact repaired statements\<close>

ML \<open>
local
  val names = ["gi_T3_modal_source_closed", "gi_T3_min_source_closed",
    "gb_T3_modal_axioms_language", "gb_T3_exhaustion_axioms_language",
    "gi_T3_modal_axiom_from_native", "gi_T3_exhaustion_axiom_from_native",
    "gi_T3_modal_result_admitted", "gi_T3_modal_core",
    "gi_T3_heredity_admitted", "gi_T3_heredity_translation",
    "gi_T3_heredity_with_exhaustion", "gi_T3_pure_eq_rigidity_admitted",
    "gi_T3_pure_eq_rigidity_translation", "gb_T3_pure_eq_rigidity_language",
    "gb_T3_rigid_axioms_language", "gi_T3_rigid_source_closed",
    "gi_T3_rigid_axiom_from_native", "gi_T3_heredity_with_pure_rigidity",
    "gi_T3_possible_identity_source_closed", "gi_T3_possible_identity_source_admitted",
    "gi_T3_heredity_with_all_unary_rigidity_image_stock"]
  fun expand name = map_index (fn (i, thm) =>
    (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map #2 entries
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "t3: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("t3: residual obligations in " ^ name)
  val report = "T3-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: possible identity from QSS and unary Persistence; native Heredity only with zeroary Exhaustion or pure-unary-identity rigidity. The stronger older all-unary rigidity repair retains an explicit image stock. No uncorrected Heredity derivation, full-theory countermodel, or consistency claim.\n"
    ^ cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t3-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "t3-statements.txt")) [XML.Text statements]
in end
\<close>

end
