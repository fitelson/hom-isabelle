theory Bacon_Book_Lambda_I_Finite_Support
  imports Bacon_Book_Lambda_I_Closed_Deduction
begin

section \<open>Each derivation uses finitely many assumptions\<close>

lemma book_lambda_I_empty_finite_support:
  assumes derivation: "book_lambda_I_derivable \<Sigma> G {} A"
  shows "\<exists>U. finite U \<and> U \<subseteq> S \<and> book_lambda_I_derivable \<Sigma> G U A"
  by (rule exI[where x="{}"], rule conjI[OF finite.emptyI],
    rule conjI[OF empty_subsetI derivation])

theorem book_lambda_I_derivable_finite_support:
  assumes derivation: "book_lambda_I_derivable \<Sigma> G S A"
  shows "\<exists>U. finite U \<and> U \<subseteq> S \<and> book_lambda_I_derivable \<Sigma> G U A"
  using derivation
proof (induction rule: book_lambda_I_derivable.induct)
  case (Assumption A S)
  have finite: "finite {A}" by simp
  have subset: "{A} \<subseteq> S" using Assumption.hyps(1) by simp
  have native: "book_lambda_I_derivable \<Sigma> G {A} A"
    by (rule book_lambda_I_derivable.Assumption[OF insertI1 Assumption.hyps(2)])
  show ?case by (rule exI[where x="{A}"], rule conjI[OF finite conjI[OF subset native]])
next
  case PC1
  show ?case by (rule book_lambda_I_empty_finite_support, rule book_lambda_I_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_lambda_I_empty_finite_support, rule book_lambda_I_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_lambda_I_empty_finite_support, rule book_lambda_I_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_lambda_I_empty_finite_support, rule book_lambda_I_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_lambda_I_empty_finite_support, rule book_lambda_I_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_lambda_I_empty_finite_support, rule book_lambda_I_derivable.Eta[OF Eta.hyps])
next
  case (MP S A B)
  obtain U where uf: "finite U" and us: "U \<subseteq> S" and left: "book_lambda_I_derivable \<Sigma> G U A"
    using MP.IH(1) by (elim exE conjE)
  obtain W where wf: "finite W" and ws: "W \<subseteq> S"
    and right: "book_lambda_I_derivable \<Sigma> G W (book_imp A B)"
    using MP.IH(2) by (elim exE conjE)
  have finite: "finite (U \<union> W)" by (rule finite_UnI[OF uf wf])
  have subset: "U \<union> W \<subseteq> S" by (rule Un_least[OF us ws])
  have left': "book_lambda_I_derivable \<Sigma> G (U \<union> W) A"
    by (rule book_lambda_I_derivable_mono[OF left Un_upper1])
  have right': "book_lambda_I_derivable \<Sigma> G (U \<union> W) (book_imp A B)"
    by (rule book_lambda_I_derivable_mono[OF right Un_upper2])
  have native: "book_lambda_I_derivable \<Sigma> G (U \<union> W) B"
    by (rule book_lambda_I_derivable.MP[OF left' right' MP.hyps(3)])
  show ?case by (rule exI[where x="U \<union> W"], rule conjI[OF finite conjI[OF subset native]])
next
  case (Gen S A B n)
  obtain U where uf: "finite U" and us: "U \<subseteq> S"
    and premise: "book_lambda_I_derivable \<Sigma> G U (book_imp A B)"
    using Gen.IH by (elim exE conjE)
  have native: "book_lambda_I_derivable \<Sigma> G U (book_imp A (book_all G n B))"
    by (rule book_lambda_I_derivable.Gen[OF premise Gen.hyps(2,3,4,5)])
  show ?case by (rule exI[where x=U], rule conjI[OF uf conjI[OF us native]])
qed

section \<open>Cut\<close>

lemma book_lambda_I_derivable_cut:
  assumes derivation: "book_lambda_I_derivable \<Sigma> G T A"
    and replacements: "\<And>B. B \<in> T \<Longrightarrow> book_lambda_I_derivable \<Sigma> G S B"
  shows "book_lambda_I_derivable \<Sigma> G S A"
  using derivation replacements
proof (induction rule: book_lambda_I_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case PC1
  show ?case by (rule book_lambda_I_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_lambda_I_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_lambda_I_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_lambda_I_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_lambda_I_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_lambda_I_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_lambda_I_derivable.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_lambda_I_derivable.Gen[OF Gen.IH[OF Gen.prems] Gen.hyps(2,3,4,5)])
qed

end
