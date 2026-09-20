theory Goodman_Exact_Basis_Native_Background_Audit
  imports Goodman_Exact_Basis_Native_Background
begin

ML \<open>
local
  val short_names = ["gi_basis_native_denote_member", "gi_basis_native_pure_denotation",
    "gi_basis_native_fun_denotation", "gi_basis_native_pure_holds", "gi_basis_native_fun_holds",
    "gi_basis_native_logical_purity_gvalid", "gi_basis_native_purity_schema_gvalid",
    "gi_basis_application_holds_iff", "gi_basis_application_holds", "gi_basis_unique_fundamental_holds",
    "gi_basis_no_fundamentals_holds", "gi_basis_native_closed_shape_gvalid",
    "gi_basis_native_application_gvalid", "gi_basis_native_application_schema_gvalid",
    "gi_basis_native_unique_fundamental_gvalid", "gi_basis_native_no_fundamentals_gvalid",
    "gi_basis_native_no_other_fundamentals_schema_gvalid", "gi_basis_native_background_gvalid"]
  val names = map (fn name => "gi_exact_invariant_basis." ^ name) short_names
  fun expand name = map_index
    (fn (i, thm) => (name ^ "(" ^ string_of_int (i + 1) ^ ")", thm))
    (Proof_Context.get_thms @{context} name)
  val entries = maps expand names
  val facts = map snd entries
  val _ = if length facts = 18 then () else error "basis-native-background: unexpected count"
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "basis-native-background: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("basis-native-background: residual obligations in " ^ name)
  val report = "BASIS-NATIVE-BACKGROUND-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Under the explicit invariant-basis locale, native Pure/Fun truth and global validity of every native closed-logical purity instance, application closure at all represented types, one fundamental proposition, no fundamentals elsewhere, and gb_background_axioms. The basis is not identified with the old closed-logical stock. Locale, language, environment and richness premises retained. Native Pure/Fun language only: fresh k still needs its intended value assigned separately. No QLN, PP, or unqualified completed expanded-language model claim. HOL-ZF foundations retained.\n" ^
    cat_lines (map check entries) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "basis-native-background-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) entries)
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "basis-native-background-statements.txt")) [XML.Text statements]
in end
\<close>

end
