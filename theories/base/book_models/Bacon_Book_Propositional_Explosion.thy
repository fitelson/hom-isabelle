theory Bacon_Book_Propositional_Explosion
  imports Bacon_Book_Propositional_Certificates
begin

section \<open>Contradictory local premises imply every formula\<close>

text \<open>
  From S ⊢ₚ A and S ⊢ₚ ¬A derive S ⊢ₚ B. PC1 first gives
  ¬B→¬A. The printed PC3 instance (¬B→¬A)→(A→B), followed
  by two applications of MP, gives B.
  Source: Bacon, Definition 5.1, pp.97–98.

  Representation: ¬A is the literal book_not G A application. It is
  neither unfolded nor identified with another operator. Richness of G
  supplies the language guard for ¬B. Status: an MP-only certificate
  construction, with no semantic argument or additional object rule.
\<close>

lemma book_prop_certificate_explosion:
  assumes positive: "book_prop_certificate \<Sigma> G S A"
    and negative: "book_prop_certificate \<Sigma> G S (book_not G A)"
    and bl: "book_theory_formula \<Sigma> G B"
    and rich: "sg_rich G"
  shows "book_prop_certificate \<Sigma> G S B"
proof -
  have al: "book_theory_formula \<Sigma> G A"
    by (rule book_prop_certificate_language[OF positive])
  have nal: "book_theory_formula \<Sigma> G (book_not G A)"
    by (rule book_prop_certificate_language[OF negative])
  have nbl: "book_theory_formula \<Sigma> G (book_not G B)"
    by (rule book_not_language[OF rich bl])
  have antecedent: "book_theory_formula \<Sigma> G
    (book_imp (book_not G B) (book_not G A))"
    by (rule book_imp_language[OF nbl nal])
  have abl: "book_theory_formula \<Sigma> G (book_imp A B)"
    by (rule book_imp_language[OF al bl])
  have weakened: "book_prop_certificate \<Sigma> G S
    (book_imp (book_not G B) (book_not G A))"
    by (rule book_prop_certificate_weaken[OF negative nbl])
  have pc3: "book_theory_derivable \<Sigma> G {}
    (book_imp (book_imp (book_not G B) (book_not G A)) (book_imp A B))"
    by (rule book_theory_derivable.PC3[OF bl al])
  have schema: "book_prop_certificate \<Sigma> G S
    (book_imp (book_imp (book_not G B) (book_not G A)) (book_imp A B))"
    by (rule book_prop_certificate.Theorem[OF pc3 book_imp_language[OF antecedent abl]])
  have implication: "book_prop_certificate \<Sigma> G S (book_imp A B)"
    by (rule book_prop_certificate.MP[OF weakened schema abl])
  show ?thesis by (rule book_prop_certificate.MP[OF positive implication bl])
qed

section \<open>A curried theorem from two certificate discharges\<close>

text \<open>
  ∅ ⊢ ¬A→(A→B) follows by first discharging A and then ¬A
  INSIDE the MP-only certificate calculus, and finally embedding the
  empty certificate in theory derivability. No deduction theorem for
  arbitrary theory derivations is used.
\<close>

theorem book_theory_explosion_curried:
  assumes rich: "sg_rich G"
    and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
  shows "book_theory_derivable \<Sigma> G {}
    (book_imp (book_not G A) (book_imp A B))"
proof -
  let ?S = "insert A (insert (book_not G A) {})"
  have nal: "book_theory_formula \<Sigma> G (book_not G A)"
    by (rule book_not_language[OF rich al])
  have positive: "book_prop_certificate \<Sigma> G ?S A"
    by (rule book_prop_certificate.Assumption[OF insertI1 al])
  have negative_member: "book_not G A \<in> ?S" by simp
  have negative: "book_prop_certificate \<Sigma> G ?S (book_not G A)"
    by (rule book_prop_certificate.Assumption[OF negative_member nal])
  have contradiction: "book_prop_certificate \<Sigma> G ?S B"
    by (rule book_prop_certificate_explosion[OF positive negative bl rich])
  have first_discharge: "book_prop_certificate \<Sigma> G (insert (book_not G A) {})
    (book_imp A B)"
    by (rule book_prop_certificate_deduction[OF contradiction al])
  have second_discharge: "book_prop_certificate \<Sigma> G {}
    (book_imp (book_not G A) (book_imp A B))"
    by (rule book_prop_certificate_deduction[OF first_discharge nal])
  show ?thesis by (rule book_prop_certificate_embeds[OF second_discharge])
qed

end
