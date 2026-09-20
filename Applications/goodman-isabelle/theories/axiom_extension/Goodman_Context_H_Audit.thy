theory Goodman_Context_H_Audit
  imports Goodman_H_Universal_Instantiation Goodman_Binding_Conversion_Audit
begin

section \<open>Audit of contextual conversion and the first H-rule transfers\<close>

text \<open>
  The H conjunction certificate uses the upstream H completeness theorem.
  Its conclusion is actual book_H theoremhood. This audit does not certify
  whole-proof H preservation, CEV+ preservation, or Goodman's axiom stock.
\<close>

ML \<open>
local
  val names =
    ["gi_chart_encoding_lookup", "gi_chart_encoding_type", "gi_expand_language",
     "gi_decoder_alignment", "gi_named_conversion_from_expansion",
     "gi_to_book_beta_context", "gi_to_book_eta_context",
     "gi_H_conversion_pair", "gi_goodman_conversion_transport", "gi_goodman_conversion_iff",
     "gi_H_beta_context_implications", "gi_H_eta_context_implications", "gi_H_MP",
     "gi_H_and_certificate", "gi_H_and_intro", "gi_H_beta_schema", "gi_H_eta_schema",
     "gi_H_UI"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Context/H audit: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises="
      ^ string_of_int (Thm.nprems_of thm)
    else error ("Context/H audit: residual kernel obligations in " ^ name)
  val report = "GOODMAN-CONTEXT-H-AUDIT: "
    ^ string_of_int (length facts) ^ " clean endpoints; partial H-rule transfer only\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "context-h-audit.txt")) [XML.Text report]
  val _ = writeln report
in end
\<close>

end
