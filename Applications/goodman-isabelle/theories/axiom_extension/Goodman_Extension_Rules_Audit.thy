theory Goodman_Extension_Rules_Audit
  imports Goodman_Translated_Extension_Rules Goodman_H_Preservation_Audit
begin

section \<open>Regression checks with premises supplied as added axioms\<close>

lemma gi_PE_added_axiom_regression:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
  shows "goodman_book_proves \<Sigma> G {book_and G (book_imp A B) (book_imp B A)}
    (book_leibniz G Prop A B)"
proof (rule gi_goodman_expanded_PE[OF rich al bl])
  show "goodman_book_proves \<Sigma> G {book_and G (book_imp A B) (book_imp B A)}
    (book_and G (book_imp A B) (book_imp B A))"
    by (rule goodman_book_proves.Axiom; (simp | rule book_and_language[
      OF rich book_imp_language[OF al bl] book_imp_language[OF bl al]]))
qed

lemma gi_Inst_added_axiom_regression:
  assumes rich: "sg_rich G" and pl: "book_theory_formula \<Sigma> G P"
    and ql: "book_theory_formula \<Sigma> G Q" and fresh: "n \<notin> named_fv Q"
  shows "goodman_book_proves \<Sigma> G {book_imp P Q} (book_imp (book_exists G n P) Q)"
proof (rule gi_goodman_Inst[OF rich pl ql fresh])
  show "goodman_book_proves \<Sigma> G {book_imp P Q} (book_imp P Q)"
    by (rule goodman_book_proves.Axiom; (simp | rule book_imp_language[OF pl ql]))
qed

section \<open>Kernel-object audit; not a whole-proof CEV+ certificate\<close>

ML \<open>
local
  val names =
    ["gi_H_expanded_iff_to_book", "gi_goodman_expanded_PE", "gi_goodman_translated_PE",
     "gi_goodman_generalize", "gi_goodman_function_identity_rule", "gi_goodman_vector_equivalence",
     "gi_old_rename_identity", "gi_old_closed_weaken", "gi_closed_expansion",
     "gi_closed_chart_alpha", "gi_goodman_closed_axiom",
     "gi_H_quantified_Inst_certificate", "gi_goodman_Inst", "gi_goodman_alpha_transport",
     "gi_goodman_translated_Gen", "gi_goodman_translated_Inst",
     "gi_PE_added_axiom_regression", "gi_Inst_added_axiom_regression"]
  val facts = map (Proof_Context.get_thm @{context}) names
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Extension-rule audit: oracle dependency"
  fun check (name, thm) =
    if null (Thm.hyps_of thm) andalso null (Thm.tpairs_of thm)
    then name ^ ": oracles=0 residual_hyps=0 flex_flex=0 statement_premises="
      ^ string_of_int (Thm.nprems_of thm)
    else error ("Extension-rule audit: residual kernel obligations in " ^ name)
  val report = "GOODMAN-EXTENSION-RULES-AUDIT: "
    ^ string_of_int (length facts) ^ " clean endpoints; no whole-proof CEV+ claim\n"
    ^ cat_lines (map check (names ~~ facts)) ^ "\n"
  val _ = Export.export @{theory}
    (Path.binding0 (Path.basic "extension-rules-audit.txt")) [XML.Text report]
  val _ = writeln report
in end
\<close>

end
