theory Goodman_Exact_Goodman_Translation_Audit
  imports Goodman_Exact_Goodman_Translation
begin

section \<open>Kernel audit of the vocabulary-guarded native Goodman translation\<close>

ML \<open>
local
  val names = ["gi_typed_name_map_or",
    "gi_typed_name_map_exists",
    "gi_typed_name_map_translation",
    "gi_translation_constant_agreement",
    "gi_goodman_string_name_recovers",
    "gi_goodman_translation_string_roundtrip",
    "pp_e_constants.gi_exact_goodman_denotation_translation",
    "pp_e_constants.gi_exact_goodman_closed_denotation_translation"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "exact-goodman-translation: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^
      string_of_int (Thm.nprems_of thm)
    else error ("exact-goodman-translation: residual obligations in " ^ name)
  val report = "EXACT-GOODMAN-TRANSLATION-AUDIT: " ^
    string_of_int (length facts) ^ " clean endpoints\n" ^
    "SCOPE: Native Goodman translation preserves exact values at every represented type under the explicit Pure/Fun source-name restriction and gi_goodman_names premise. Source typing, typed distinct chart, rich variable stock, typed assignment, pp_e_constants, and HOL-ZF qualifications retained. Target signature admission is not substituted for the source-name restriction. No arbitrary-name roundtrip or PP consistency assertion.\n" ^
    cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "exact-goodman-translation-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm))))
    (names ~~ facts))
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "exact-goodman-translation-statements.txt")) [XML.Text statements]
in end
\<close>

end
