theory Goodman_Exact_Invariant_Basis_Audit
  imports Goodman_Exact_Invariant_Basis
begin

ML \<open>
local
  val short_names = ["gi_basis_pure_member", "gi_basis_pureI", "gi_basis_pure_persistent",
    "gi_basis_pure_admissible", "gi_basis_pure_application_closed", "gi_basis_pure_logical_denotation",
    "gi_basis_contains_logical_eval", "gi_basis_contains_native_closed_logical",
    "gi_basis_pure_classifier_member", "gi_basis_pure_iff_action_member", "gi_basis_pure_root_iff",
    "gi_basis_pure_all_worlds_iff_root"]
  val names = map (fn name => "gi_exact_invariant_basis." ^ name) short_names
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 12 then () else error "exact-invariant-basis: unexpected count"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "exact-invariant-basis: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("exact-invariant-basis: residual obligations in " ^ name)
  val report = "EXACT-INVARIANT-BASIS-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Conditional on the explicit typed, invariant, countable, application-closed basis containing all old closed logical denotations. Local-identity saturation is admissible, persistent and application-closed, contains every native closed logical denotation, and equals action-to-basis membership on typed values. Exact carriers and HOL-ZF foundation unchanged. Locale premises are retained, not counted as discharged instantiation obligations; no PP or full-model claim.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-invariant-basis-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-invariant-basis-statements.txt")) [XML.Text statements]
in end
\<close>

end
