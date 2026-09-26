theory Bacon_Book_Lambda_I_Propositional_Negation
  imports Bacon_Book_Lambda_I_Propositional_Certificates Bacon_Book_Lambda_I_Negation_Conversion
begin

section \<open>Weakening the local assumptions of a certificate\<close>

lemma book_lambda_I_certificate_mono:
  assumes certificate: "book_lambda_I_certificate \<Sigma> G S A"
    and inclusion: "S \<subseteq> T"
  shows "book_lambda_I_certificate \<Sigma> G T A"
  using certificate inclusion
proof (induction rule: book_lambda_I_certificate.induct)
  case Assumption
  show ?case by (rule book_lambda_I_certificate.Assumption[
    OF subsetD[OF Assumption.prems Assumption.hyps(1)] Assumption.hyps(2)])
next
  case Theorem
  show ?case by (rule book_lambda_I_certificate.Theorem[OF Theorem.hyps])
next
  case MP
  show ?case by (rule book_lambda_I_certificate.MP[
    OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
qed

section \<open>Literal negation inside MP-only certificates\<close>

text \<open>
  ¬A and A→⊥ remain distinct formulas. The checked β implications
  between them supply folding and unfolding steps inside a certificate.
  Source: Bacon, Table 4.1, p.93, and Definition 5.1, pp.97–98.
  Representation: theorem leaves below have empty theory premises.
  Status: only the existing certificate MP rule is used.
\<close>

lemma book_lambda_I_certificate_not_fold:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
    and expanded: "book_lambda_I_certificate \<Sigma> G S (book_imp A (book_bottom G))"
  shows "book_lambda_I_certificate \<Sigma> G S (book_not G A)"
proof -
  have bottom: "book_lambda_I_formula \<Sigma> G (book_bottom G)"
    by (rule book_lambda_I_bottom_language[OF rich])
  have nal: "book_lambda_I_formula \<Sigma> G (book_not G A)"
    by (rule book_lambda_I_not_language[OF rich al])
  have expanded_language: "book_lambda_I_formula \<Sigma> G (book_imp A (book_bottom G))"
    by (rule book_lambda_I_imp_language[OF al bottom])
  have implication: "book_lambda_I_derivable \<Sigma> G {}
    (book_imp (book_imp A (book_bottom G)) (book_not G A))"
    by (rule book_lambda_I_not_fold[OF rich al])
  have folding: "book_lambda_I_certificate \<Sigma> G S
    (book_imp (book_imp A (book_bottom G)) (book_not G A))"
    by (rule book_lambda_I_certificate.Theorem[
      OF implication book_lambda_I_imp_language[OF expanded_language nal]])
  show ?thesis by (rule book_lambda_I_certificate.MP[OF expanded folding nal])
qed

lemma book_lambda_I_certificate_not_unfold:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
    and negative: "book_lambda_I_certificate \<Sigma> G S (book_not G A)"
  shows "book_lambda_I_certificate \<Sigma> G S (book_imp A (book_bottom G))"
proof -
  have bottom: "book_lambda_I_formula \<Sigma> G (book_bottom G)"
    by (rule book_lambda_I_bottom_language[OF rich])
  have nal: "book_lambda_I_formula \<Sigma> G (book_not G A)"
    by (rule book_lambda_I_not_language[OF rich al])
  have expanded_language: "book_lambda_I_formula \<Sigma> G (book_imp A (book_bottom G))"
    by (rule book_lambda_I_imp_language[OF al bottom])
  have implication: "book_lambda_I_derivable \<Sigma> G {}
    (book_imp (book_not G A) (book_imp A (book_bottom G)))"
    by (rule book_lambda_I_not_unfold[OF rich al])
  have unfolding_step: "book_lambda_I_certificate \<Sigma> G S
    (book_imp (book_not G A) (book_imp A (book_bottom G)))"
    by (rule book_lambda_I_certificate.Theorem[
      OF implication book_lambda_I_imp_language[OF nal expanded_language]])
  show ?thesis by (rule book_lambda_I_certificate.MP[OF negative unfolding_step expanded_language])
qed

theorem book_lambda_I_certificate_not_intro:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
    and contradiction: "book_lambda_I_certificate \<Sigma> G (insert A S) (book_bottom G)"
  shows "book_lambda_I_certificate \<Sigma> G S (book_not G A)"
proof -
  have conditional: "book_lambda_I_certificate \<Sigma> G S (book_imp A (book_bottom G))"
    by (rule book_lambda_I_certificate_deduction[OF contradiction al])
  show ?thesis by (rule book_lambda_I_certificate_not_fold[OF rich al conditional])
qed

theorem book_lambda_I_certificate_not_elim:
  assumes rich: "sg_rich G"
    and positive: "book_lambda_I_certificate \<Sigma> G S A"
    and negative: "book_lambda_I_certificate \<Sigma> G S (book_not G A)"
  shows "book_lambda_I_certificate \<Sigma> G S (book_bottom G)"
proof -
  have al: "book_lambda_I_formula \<Sigma> G A"
    by (rule book_lambda_I_certificate_language[OF positive])
  have conditional: "book_lambda_I_certificate \<Sigma> G S (book_imp A (book_bottom G))"
    by (rule book_lambda_I_certificate_not_unfold[OF rich al negative])
  show ?thesis by (rule book_lambda_I_certificate.MP[
    OF positive conditional book_lambda_I_bottom_language[OF rich]])
qed

section \<open>Classical reductio within a certificate\<close>

text \<open>
  If S∪{¬A} ⊢ₚ ⊥, then S ⊢ₚ A.
  Let T=¬⊥, an independently proved empty-premise theorem. Under ¬A,
  the contradiction yields T→⊥ and hence ¬T. Certificate discharge
  gives ¬A→¬T. The exact PC3 instance (¬A→¬T)→(T→A), followed
  by MP with the theorem T, yields A.

  This is classical RAA for MP-only certificates. In particular, the
  discharge step does not range over arbitrary theory derivations with
  Gen. No model, H judgment, or completeness result is imported.
\<close>

theorem book_lambda_I_certificate_RAA:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
    and contradiction: "book_lambda_I_certificate \<Sigma> G (insert (book_not G A) S) (book_bottom G)"
  shows "book_lambda_I_certificate \<Sigma> G S A"
proof -
  let ?T = "book_not G (book_bottom G)"
  have bottom: "book_lambda_I_formula \<Sigma> G (book_bottom G)"
    by (rule book_lambda_I_bottom_language[OF rich])
  have tl: "book_lambda_I_formula \<Sigma> G ?T"
    by (rule book_lambda_I_not_language[OF rich bottom])
  have ntl: "book_lambda_I_formula \<Sigma> G (book_not G ?T)"
    by (rule book_lambda_I_not_language[OF rich tl])
  have nal: "book_lambda_I_formula \<Sigma> G (book_not G A)"
    by (rule book_lambda_I_not_language[OF rich al])
  have weakened: "book_lambda_I_certificate \<Sigma> G (insert (book_not G A) S)
    (book_imp ?T (book_bottom G))"
    by (rule book_lambda_I_certificate_weaken[OF contradiction tl])
  have negated_T: "book_lambda_I_certificate \<Sigma> G (insert (book_not G A) S) (book_not G ?T)"
    by (rule book_lambda_I_certificate_not_fold[OF rich tl weakened])
  have discharged: "book_lambda_I_certificate \<Sigma> G S
    (book_imp (book_not G A) (book_not G ?T))"
    by (rule book_lambda_I_certificate_deduction[OF negated_T nal])
  have antecedent: "book_lambda_I_formula \<Sigma> G
    (book_imp (book_not G A) (book_not G ?T))"
    by (rule book_lambda_I_imp_language[OF nal ntl])
  have consequent: "book_lambda_I_formula \<Sigma> G (book_imp ?T A)"
    by (rule book_lambda_I_imp_language[OF tl al])
  have pc3: "book_lambda_I_derivable \<Sigma> G {}
    (book_imp (book_imp (book_not G A) (book_not G ?T)) (book_imp ?T A))"
    by (rule book_lambda_I_derivable.PC3[OF al tl])
  have schema: "book_lambda_I_certificate \<Sigma> G S
    (book_imp (book_imp (book_not G A) (book_not G ?T)) (book_imp ?T A))"
    by (rule book_lambda_I_certificate.Theorem[
      OF pc3 book_lambda_I_imp_language[OF antecedent consequent]])
  have implication: "book_lambda_I_certificate \<Sigma> G S (book_imp ?T A)"
    by (rule book_lambda_I_certificate.MP[OF discharged schema consequent])
  have theorem_T: "book_lambda_I_derivable \<Sigma> G {} ?T"
    by (rule book_lambda_I_not_bottom[OF rich])
  have certificate_T: "book_lambda_I_certificate \<Sigma> G S ?T"
    by (rule book_lambda_I_certificate.Theorem[OF theorem_T tl])
  show ?thesis by (rule book_lambda_I_certificate.MP[OF certificate_T implication al])
qed

end
