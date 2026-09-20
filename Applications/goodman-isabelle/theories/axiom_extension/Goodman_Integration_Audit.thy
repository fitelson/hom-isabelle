theory Goodman_Integration_Audit
  imports Goodman_Book_Extension_Closure
begin

section \<open>Kernel-object checks for the initial integration bridge\<close>

text \<open>
  This audit checks the displayed candidate calculus and closure results.
  It does not certify an old-CEV+ translation, source fidelity of the
  Goodman stock, global soundness, or an answer to the consistency question.
  The theorem statements retain their rich-variable-stock hypotheses.
\<close>

ML \<open>
local
  val names =
    ["goodman_book_proves_language", "goodman_book_empty_iff",
     "goodman_book_cut", "goodman_book_mono",
     "goodman_book_necessitation", "goodman_book_added_axiom_necessitation",
     "goodman_book_contains_theory_derivation", "goodman_book_contains_C_theory",
     "goodman_book_ordinary_consequence_in_extension",
     "goodman_book_closure_theory_iff", "goodman_book_closure_consistency_iff",
     "goodman_book_closure_idempotent"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Integration audit: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises="
      ^ string_of_int (Thm.nprems_of thm)
    else error ("Integration audit: residual kernel obligations in " ^ name)
  val rows = map check (names ~~ facts)
  val report = "GOODMAN-INTEGRATION-AUDIT: " ^ string_of_int (length facts)
    ^ " clean endpoints; candidate book extension only\n" ^ cat_lines rows ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "integration-audit.txt")) [XML.Text report]
  val _ = writeln report
in end
\<close>

end
