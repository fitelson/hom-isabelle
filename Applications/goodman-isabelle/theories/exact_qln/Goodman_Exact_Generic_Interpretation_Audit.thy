theory Goodman_Exact_Generic_Interpretation_Audit
  imports Goodman_Exact_Generic_Interpretation
begin

section \<open>Kernel checks and exact statement export for the generic background\<close>

ML \<open>
local
  val names = [
    "gi_exact_generic_constants",
    "gi_exact_generic_native_denote_type",
    "gi_exact_generic_Pure_denotation",
    "gi_exact_generic_Fun_denotation",
    "gi_exact_generic_pure_denotation",
    "gi_exact_generic_fun_denotation",
    "gi_exact_generic_native_pure_holds",
    "gi_exact_generic_native_fun_holds",
    "gi_exact_generic_logical_purity_gvalid",
    "gi_exact_generic_purity_schema_gvalid",
    "gi_exact_generic_closed_shape_gvalid",
    "gi_exact_generic_application_gvalid",
    "gi_exact_generic_application_schema_gvalid",
    "gi_exact_generic_unique_fundamental_gvalid",
    "gi_exact_generic_no_fundamentals_gvalid",
    "gi_exact_generic_no_other_fundamentals_schema_gvalid",
    "gi_exact_generic_background_gvalid"]
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 17 then ()
    else error "exact-generic-background: unexpected endpoint count"
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-generic-background: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-generic-background: residual obligations in " ^ name)
  val report = "EXACT-GENERIC-BACKGROUND-AUDIT: " ^ string_of_int (length facts) ^
    " clean endpoints\n" ^
    "SCOPE: Native Pure/Fun value and truth clauses under the specified generic moving-seed interpretation; complete native logical-purity schema, application schema, unique proposition-level fundamentality, no other fundamentals, and gb_background_axioms. HOL-ZF foundations and displayed language/environment/richness guards retained. No PP, QLN directions, Theorem-10.1 fixed glued constant identification, or enlarged-stock model is asserted here.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-generic-background-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "exact-generic-background-statements.txt")) [XML.Text statements]
in end
\<close>

end
