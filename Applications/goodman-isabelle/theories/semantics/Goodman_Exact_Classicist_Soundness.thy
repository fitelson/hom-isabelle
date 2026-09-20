theory Goodman_Exact_Classicist_Soundness
  imports Goodman_Exact_Global_Validity Goodman_Exact_Modal_Functionality
    "Goodman_Integration_Proof.Goodman_Book_Extension_Closure"
begin

section \<open>Global soundness of full C and the actual axiom extension\<close>

context pp_e_constants
begin

lemma gi_exact_MF_global_valid:
  assumes rich: "sg_rich G"
  shows "gi_exact_global_valid C G (book_MF_axiom G \<sigma> \<tau>)"
proof (rule gi_exact_global_validI)
  fix w g assume typed: "book_env_typed gi_exact_domain G g"
  show "gi_exact_valuation w (gi_exact_named_denote C G g (book_MF_axiom G \<sigma> \<tau>))"
    using gi_exact_MF_axiom_holds[OF rich typed, where w=w and \<sigma>=\<sigma> and \<tau>=\<tau>]
    by (simp only: gi_exact_valuation_def)
qed

theorem gi_exact_C_global_sound:
  assumes rich: "sg_rich G" and derivation: "book_full_C_proves \<Sigma> G A"
  shows "gi_exact_global_valid C G A"
  using derivation
proof (induction rule: book_full_C_proves.induct)
  case H
  show ?case by (rule gi_exact_H_global_sound[OF rich H.hyps])
next
  case MF
  show ?case by (rule gi_exact_MF_global_valid[OF rich])
next
  case (MP A B)
  have al: "book_theory_formula \<Sigma> G A" by (rule book_full_C_proves_language[OF rich MP.hyps(1)])
  show ?case by (rule gi_exact_global_MP[OF rich al MP.hyps(3) MP.IH])
next
  case Gen
  show ?case by (rule gi_exact_global_Gen[OF rich Gen.hyps(2,3,4) Gen.IH])
next
  case PE
  show ?case by (rule gi_exact_global_PE[OF rich PE.hyps(2,3) PE.IH])
qed

theorem gi_exact_extension_global_sound:
  assumes rich: "sg_rich G" and derivation: "goodman_book_proves \<Sigma> G T A"
    and axioms: "\<And>B. B \<in> T \<Longrightarrow> gi_exact_global_valid C G B"
  shows "gi_exact_global_valid C G A"
  using derivation
proof (induction rule: goodman_book_proves.induct)
  case Axiom
  show ?case by (rule axioms[OF Axiom.hyps(1)])
next
  case Base
  show ?case by (rule gi_exact_C_global_sound[OF rich Base.hyps])
next
  case (MP A B)
  have al: "book_theory_formula \<Sigma> G A" by (rule goodman_book_proves_language[OF rich MP.hyps(1)])
  show ?case by (rule gi_exact_global_MP[OF rich al MP.hyps(3) MP.IH])
next
  case Gen
  show ?case by (rule gi_exact_global_Gen[OF rich Gen.hyps(2,3,4) Gen.IH])
next
  case PE
  show ?case by (rule gi_exact_global_PE[OF rich PE.hyps(2,3) PE.IH])
qed

lemma gi_exact_bottom_not_global:
  assumes rich: "sg_rich G"
  shows "\<not> gi_exact_global_valid C G (book_bottom G)"
proof
  assume valid: "gi_exact_global_valid C G (book_bottom G)"
  have typed: "book_env_typed gi_exact_domain G (gi_exact_default_assignment G)"
    by (rule gi_exact_default_assignment_typed)
  have true_bottom: "gi_exact_valuation []
    (gi_exact_named_denote C G (gi_exact_default_assignment G) (book_bottom G))"
    by (rule gi_exact_global_validD[OF valid typed])
  have false_bottom: "\<not> gi_exact_valuation []
    (gi_exact_named_denote C G (gi_exact_default_assignment G) (book_bottom G))"
    by (rule book_full_minimal_model.book_bottom_false[OF gi_exact_book_minimal_model[OF rich] rich typed])
  show False by (rule notE[OF false_bottom true_bottom])
qed

theorem gi_exact_consistent_of_global_axioms:
  assumes rich: "sg_rich G"
    and axioms: "\<And>B. B \<in> T \<Longrightarrow> gi_exact_global_valid C G B"
  shows "goodman_book_consistent \<Sigma> G T"
proof (unfold goodman_book_consistent_def, intro notI)
  assume refutation: "goodman_book_proves \<Sigma> G T (book_bottom G)"
  have valid: "gi_exact_global_valid C G (book_bottom G)"
    by (rule gi_exact_extension_global_sound[OF rich refutation axioms])
  show False by (rule notE[OF gi_exact_bottom_not_global[OF rich] valid])
qed

end

text \<open>
  This induction includes native all-result-type MF and theorem-level PE
  above globally valid added axioms. It does not use old CEV soundness as
  a surrogate for new full-C soundness. The evaluator currently has string
  constant names; the Goodman two-name presentation requires its explicit
  constant-map bridge. No purity/classifier interpretation is supplied by
  the conditional consistency theorem, and PP has not been validated.
\<close>

end
