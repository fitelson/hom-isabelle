theory Bacon_Book_Conjunction_Currying
  imports Bacon_Book_Conjunction_Certificates
begin

section \<open>Currying through the expanded conjunction formula\<close>

text \<open>
  Put D = ¬(C→¬A). We derive (C→(A→B))→(D→B) and its
  converse in the empty-premise theory, then apply them under an arbitrary
  theory premise set S. Source: Bacon's propositional schemas and MP,
  pp.97–98; this is propositional infrastructure for the discharge
  argument discussed with Theorem 15.2, p.318.

  Representation. D is the displayed formula built from literal negation
  applications, not a primitive conjunction constructor or an operator
  identity. The temporary hypotheses below belong only to MP-only
  certificates. Their deduction theorem produces empty-premise theory
  theorems before we use a derivation from S. No unrestricted open
  deduction theorem for the theory calculus, or semantic premise, is used.
\<close>

lemma book_theory_conj_uncurry_schema:
  assumes rich: "sg_rich G"
    and cl: "book_theory_formula \<Sigma> G C"
    and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
  shows "book_theory_derivable \<Sigma> G {}
    (book_imp (book_imp C (book_imp A B))
      (book_imp (book_not G (book_imp C (book_not G A))) B))"
proof -
  let ?D = "book_not G (book_imp C (book_not G A))"
  let ?H = "book_imp C (book_imp A B)"
  have dl: "book_theory_formula \<Sigma> G ?D"
    by (rule book_not_language[OF rich book_imp_language[OF cl book_not_language[OF rich al]]])
  have abl: "book_theory_formula \<Sigma> G (book_imp A B)"
    by (rule book_imp_language[OF al bl])
  have hl: "book_theory_formula \<Sigma> G ?H"
    by (rule book_imp_language[OF cl abl])
  have hcert: "book_prop_certificate \<Sigma> G (insert ?D {?H}) ?H"
    by (rule book_prop_certificate.Assumption[OF _ hl]; simp)
  have dcert: "book_prop_certificate \<Sigma> G (insert ?D {?H}) ?D"
    by (rule book_prop_certificate.Assumption[OF _ dl]; simp)
  have ccert: "book_prop_certificate \<Sigma> G (insert ?D {?H}) C"
    by (rule book_prop_certificate_conj_left[OF rich cl al dcert])
  have acert: "book_prop_certificate \<Sigma> G (insert ?D {?H}) A"
    by (rule book_prop_certificate_conj_right[OF rich cl al dcert])
  have abcert: "book_prop_certificate \<Sigma> G (insert ?D {?H}) (book_imp A B)"
    by (rule book_prop_certificate.MP[OF ccert hcert abl])
  have bcert: "book_prop_certificate \<Sigma> G (insert ?D {?H}) B"
    by (rule book_prop_certificate.MP[OF acert abcert bl])
  have discharge_d: "book_prop_certificate \<Sigma> G {?H} (book_imp ?D B)"
    by (rule book_prop_certificate_deduction[OF bcert dl])
  have discharge_h: "book_prop_certificate \<Sigma> G {} (book_imp ?H (book_imp ?D B))"
    by (rule book_prop_certificate_deduction[OF discharge_d hl])
  show ?thesis by (rule book_prop_certificate_embeds[OF discharge_h])
qed

lemma book_theory_conj_curry_schema:
  assumes rich: "sg_rich G"
    and cl: "book_theory_formula \<Sigma> G C"
    and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
  shows "book_theory_derivable \<Sigma> G {}
    (book_imp (book_imp (book_not G (book_imp C (book_not G A))) B)
      (book_imp C (book_imp A B)))"
proof -
  let ?D = "book_not G (book_imp C (book_not G A))"
  let ?K = "book_imp ?D B"
  have dl: "book_theory_formula \<Sigma> G ?D"
    by (rule book_not_language[OF rich book_imp_language[OF cl book_not_language[OF rich al]]])
  have kl: "book_theory_formula \<Sigma> G ?K"
    by (rule book_imp_language[OF dl bl])
  have kcert: "book_prop_certificate \<Sigma> G (insert A (insert C {?K})) ?K"
    by (rule book_prop_certificate.Assumption[OF _ kl]; simp)
  have ccert: "book_prop_certificate \<Sigma> G (insert A (insert C {?K})) C"
    by (rule book_prop_certificate.Assumption[OF _ cl]; simp)
  have acert: "book_prop_certificate \<Sigma> G (insert A (insert C {?K})) A"
    by (rule book_prop_certificate.Assumption[OF _ al]; simp)
  have dcert: "book_prop_certificate \<Sigma> G (insert A (insert C {?K})) ?D"
    by (rule book_prop_certificate_conj_intro[OF rich ccert acert])
  have bcert: "book_prop_certificate \<Sigma> G (insert A (insert C {?K})) B"
    by (rule book_prop_certificate.MP[OF dcert kcert bl])
  have discharge_a: "book_prop_certificate \<Sigma> G (insert C {?K}) (book_imp A B)"
    by (rule book_prop_certificate_deduction[OF bcert al])
  have discharge_c: "book_prop_certificate \<Sigma> G {?K} (book_imp C (book_imp A B))"
    by (rule book_prop_certificate_deduction[OF discharge_a cl])
  have discharge_k: "book_prop_certificate \<Sigma> G {}
    (book_imp ?K (book_imp C (book_imp A B)))"
    by (rule book_prop_certificate_deduction[OF discharge_c kl])
  show ?thesis by (rule book_prop_certificate_embeds[OF discharge_k])
qed

section \<open>Derived rules under unchanged theory premises\<close>

theorem book_theory_conj_uncurry:
  assumes rich: "sg_rich G"
    and cl: "book_theory_formula \<Sigma> G C"
    and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
    and derivation: "book_theory_derivable \<Sigma> G S (book_imp C (book_imp A B))"
  shows "book_theory_derivable \<Sigma> G S
    (book_imp (book_not G (book_imp C (book_not G A))) B)"
proof -
  let ?D = "book_not G (book_imp C (book_not G A))"
  have dl: "book_theory_formula \<Sigma> G ?D"
    by (rule book_not_language[OF rich book_imp_language[OF cl book_not_language[OF rich al]]])
  have schema: "book_theory_derivable \<Sigma> G {}
    (book_imp (book_imp C (book_imp A B)) (book_imp ?D B))"
    by (rule book_theory_conj_uncurry_schema[OF rich cl al bl])
  have lifted: "book_theory_derivable \<Sigma> G S
    (book_imp (book_imp C (book_imp A B)) (book_imp ?D B))"
    by (rule book_theory_derivable_mono[OF schema empty_subsetI])
  show ?thesis by (rule book_theory_derivable.MP[OF derivation lifted book_imp_language[OF dl bl]])
qed

theorem book_theory_conj_curry:
  assumes rich: "sg_rich G"
    and cl: "book_theory_formula \<Sigma> G C"
    and al: "book_theory_formula \<Sigma> G A"
    and bl: "book_theory_formula \<Sigma> G B"
    and derivation: "book_theory_derivable \<Sigma> G S
      (book_imp (book_not G (book_imp C (book_not G A))) B)"
  shows "book_theory_derivable \<Sigma> G S (book_imp C (book_imp A B))"
proof -
  let ?D = "book_not G (book_imp C (book_not G A))"
  have schema: "book_theory_derivable \<Sigma> G {}
    (book_imp (book_imp ?D B) (book_imp C (book_imp A B)))"
    by (rule book_theory_conj_curry_schema[OF rich cl al bl])
  have lifted: "book_theory_derivable \<Sigma> G S
    (book_imp (book_imp ?D B) (book_imp C (book_imp A B)))"
    by (rule book_theory_derivable_mono[OF schema empty_subsetI])
  have result_language: "book_theory_formula \<Sigma> G (book_imp C (book_imp A B))"
    by (rule book_imp_language[OF cl book_imp_language[OF al bl]])
  show ?thesis by (rule book_theory_derivable.MP[OF derivation lifted result_language])
qed

end
