theory Bacon_Source_Relational_Classicism_A2_Local
  imports Bacon_Source_Relational_Classicism_A2_MP
begin

section \<open>Local H consequences preserve the abstraction-to-truth property\<close>

text \<open>
  Suppose every usable premise B in S has (λv⃗.B)=(λv⃗.⊤)
  provable in C for every R prefix. Then every local H consequence
  of S has the same property. We follow exactly Assumption, Theorem,
  and MP. The strengthened induction hypothesis supplies every prefix
  required by the closed-prefix MP argument.

  Source role: Appendix A.2, pp.65–66. This is not an unrestricted
  deduction theorem through Gen or Inst. The local premise set may
  be arbitrary; only typed premises actually used acquire obligations.
\<close>

theorem paper_R_classicism_A2_local_H:
  assumes rich: "paper_R_rich G" and derivation: "paper_R_named_derivable \<Sigma> G S A"
    and binders: "list_all paper_R_type (map G ns)"
    and source_premises: "\<And>B ms. B \<in> S \<Longrightarrow> paper_R_in_language \<Sigma> G B Prop \<Longrightarrow>
      list_all paper_R_type (map G ms) \<Longrightarrow>
      paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ms) Prop)
        (named_lam_vec ms B) (named_lam_vec ms (paper_R_named_top G)))"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns A) (named_lam_vec ns (paper_R_named_top G)))"
  using derivation binders source_premises
proof (induction arbitrary: ns rule: paper_R_named_derivable.induct)
  case (Assumption A S)
  show ?case by (rule Assumption.prems(2)[OF Assumption.hyps Assumption.prems(1)])
next
  case (Theorem A S)
  show ?case by (rule paper_R_classicism_A2_H[OF rich Theorem.hyps Theorem.prems(1)])
next
  case (MP S Q P)
  have ql: "paper_R_in_language \<Sigma> G Q Prop"
    by (rule paper_R_named_derivable_language[OF MP.hyps(1)])
  have first: "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ms) Prop)
      (named_lam_vec ms Q) (named_lam_vec ms (paper_R_named_top G)))"
    if "list_all paper_R_type (map G ms)" for ms
    by (rule MP.IH(1)[OF that MP.prems(2)])
  have second: "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ms) Prop)
      (named_lam_vec ms (named_paper_imp G Q P)) (named_lam_vec ms (paper_R_named_top G)))"
    if "list_all paper_R_type (map G ms)" for ms
    by (rule MP.IH(2)[OF that MP.prems(2)])
  show ?case by (rule paper_R_classicism_A2_MP[OF rich MP.hyps(3) ql MP.prems(1) first second])
qed

end
