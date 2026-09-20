theory Goodman_Constant_Map_Audit
  imports Goodman_Extension_Constant_Map
begin

section \<open>Audit of exact statements and kernel proof objects\<close>

ML \<open>
local
  val names = ["gi_goodman_typed_constant_map",
    "gi_goodman_string_signature_map",
    "gi_goodman_string_signature_exact",
    "gi_goodman_string_signature_predicate",
    "gi_goodman_string_signature_nonpredicate",
    "gi_goodman_string_term_language",
    "gi_goodman_string_term_fv",
    "gi_goodman_string_term_Pure",
    "gi_goodman_string_term_Fun",
    "gi_goodman_string_proof_preservation"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then () else error "constant-map: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises=" ^ string_of_int (Thm.nprems_of thm)
    else error ("constant-map: residual obligations in " ^ name)
  val report = "CONSTANT-MAP-AUDIT: " ^ string_of_int (length facts) ^ " clean endpoints\n"
    ^ "SCOPE: Typed constant-map proof preservation in C+[T], with mapped stocks and declared signatures; no reflection inferred.\n" ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "constant-map-audit.txt")) [XML.Text report]
  val _ = writeln report
  val statements = cat_lines (map (fn (name, thm) => name ^ ":\n" ^
    XML.content_of (YXML.parse_body (Syntax.string_of_term @{context} (Thm.prop_of thm)))) (names ~~ facts))
  val _ = Export.export @{theory} (Path.binding0 (Path.basic "constant-map-statements.txt")) [XML.Text statements]
in end
\<close>

end

