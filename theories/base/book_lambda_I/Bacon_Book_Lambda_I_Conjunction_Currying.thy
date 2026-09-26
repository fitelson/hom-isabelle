theory Bacon_Book_Lambda_I_Conjunction_Currying
  imports Bacon_Book_Lambda_I_Conjunction_Certificates
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

lemma book_lambda_I_conj_uncurry_schema:
  assumes rich: "sg_rich G"
    and cl: "book_lambda_I_formula \<Sigma> G C"
    and al: "book_lambda_I_formula \<Sigma> G A"
    and bl: "book_lambda_I_formula \<Sigma> G B"
  shows "book_lambda_I_derivable \<Sigma> G {}
    (book_imp (book_imp C (book_imp A B))
      (book_imp (book_not G (book_imp C (book_not G A))) B))"
proof -
  let ?D = "book_not G (book_imp C (book_not G A))"
  let ?H = "book_imp C (book_imp A B)"
  have dl: "book_lambda_I_formula \<Sigma> G ?D"
    by (rule book_lambda_I_not_language[OF rich book_lambda_I_imp_language[OF cl book_lambda_I_not_language[OF rich al]]])
  have abl: "book_lambda_I_formula \<Sigma> G (book_imp A B)"
    by (rule book_lambda_I_imp_language[OF al bl])
  have hl: "book_lambda_I_formula \<Sigma> G ?H"
    by (rule book_lambda_I_imp_language[OF cl abl])
  have hcert: "book_lambda_I_certificate \<Sigma> G (insert ?D {?H}) ?H"
    by (rule book_lambda_I_certificate.Assumption[OF _ hl]; simp)
  have dcert: "book_lambda_I_certificate \<Sigma> G (insert ?D {?H}) ?D"
    by (rule book_lambda_I_certificate.Assumption[OF _ dl]; simp)
  have ccert: "book_lambda_I_certificate \<Sigma> G (insert ?D {?H}) C"
    by (rule book_lambda_I_certificate_conj_left[OF rich cl al dcert])
  have acert: "book_lambda_I_certificate \<Sigma> G (insert ?D {?H}) A"
    by (rule book_lambda_I_certificate_conj_right[OF rich cl al dcert])
  have abcert: "book_lambda_I_certificate \<Sigma> G (insert ?D {?H}) (book_imp A B)"
    by (rule book_lambda_I_certificate.MP[OF ccert hcert abl])
  have bcert: "book_lambda_I_certificate \<Sigma> G (insert ?D {?H}) B"
    by (rule book_lambda_I_certificate.MP[OF acert abcert bl])
  have discharge_d: "book_lambda_I_certificate \<Sigma> G {?H} (book_imp ?D B)"
    by (rule book_lambda_I_certificate_deduction[OF bcert dl])
  have discharge_h: "book_lambda_I_certificate \<Sigma> G {} (book_imp ?H (book_imp ?D B))"
    by (rule book_lambda_I_certificate_deduction[OF discharge_d hl])
  show ?thesis by (rule book_lambda_I_certificate_embeds[OF discharge_h])
qed

lemma book_lambda_I_conj_curry_schema:
  assumes rich: "sg_rich G"
    and cl: "book_lambda_I_formula \<Sigma> G C"
    and al: "book_lambda_I_formula \<Sigma> G A"
    and bl: "book_lambda_I_formula \<Sigma> G B"
  shows "book_lambda_I_derivable \<Sigma> G {}
    (book_imp (book_imp (book_not G (book_imp C (book_not G A))) B)
      (book_imp C (book_imp A B)))"
proof -
  let ?D = "book_not G (book_imp C (book_not G A))"
  let ?K = "book_imp ?D B"
  have dl: "book_lambda_I_formula \<Sigma> G ?D"
    by (rule book_lambda_I_not_language[OF rich book_lambda_I_imp_language[OF cl book_lambda_I_not_language[OF rich al]]])
  have kl: "book_lambda_I_formula \<Sigma> G ?K"
    by (rule book_lambda_I_imp_language[OF dl bl])
  have kcert: "book_lambda_I_certificate \<Sigma> G (insert A (insert C {?K})) ?K"
    by (rule book_lambda_I_certificate.Assumption[OF _ kl]; simp)
  have ccert: "book_lambda_I_certificate \<Sigma> G (insert A (insert C {?K})) C"
    by (rule book_lambda_I_certificate.Assumption[OF _ cl]; simp)
  have acert: "book_lambda_I_certificate \<Sigma> G (insert A (insert C {?K})) A"
    by (rule book_lambda_I_certificate.Assumption[OF _ al]; simp)
  have dcert: "book_lambda_I_certificate \<Sigma> G (insert A (insert C {?K})) ?D"
    by (rule book_lambda_I_certificate_conj_intro[OF rich ccert acert])
  have bcert: "book_lambda_I_certificate \<Sigma> G (insert A (insert C {?K})) B"
    by (rule book_lambda_I_certificate.MP[OF dcert kcert bl])
  have discharge_a: "book_lambda_I_certificate \<Sigma> G (insert C {?K}) (book_imp A B)"
    by (rule book_lambda_I_certificate_deduction[OF bcert al])
  have discharge_c: "book_lambda_I_certificate \<Sigma> G {?K} (book_imp C (book_imp A B))"
    by (rule book_lambda_I_certificate_deduction[OF discharge_a cl])
  have discharge_k: "book_lambda_I_certificate \<Sigma> G {}
    (book_imp ?K (book_imp C (book_imp A B)))"
    by (rule book_lambda_I_certificate_deduction[OF discharge_c kl])
  show ?thesis by (rule book_lambda_I_certificate_embeds[OF discharge_k])
qed

section \<open>Derived rules under unchanged theory premises\<close>

theorem book_lambda_I_conj_uncurry:
  assumes rich: "sg_rich G"
    and cl: "book_lambda_I_formula \<Sigma> G C"
    and al: "book_lambda_I_formula \<Sigma> G A"
    and bl: "book_lambda_I_formula \<Sigma> G B"
    and derivation: "book_lambda_I_derivable \<Sigma> G S (book_imp C (book_imp A B))"
  shows "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_not G (book_imp C (book_not G A))) B)"
proof -
  let ?D = "book_not G (book_imp C (book_not G A))"
  have dl: "book_lambda_I_formula \<Sigma> G ?D"
    by (rule book_lambda_I_not_language[OF rich book_lambda_I_imp_language[OF cl book_lambda_I_not_language[OF rich al]]])
  have schema: "book_lambda_I_derivable \<Sigma> G {}
    (book_imp (book_imp C (book_imp A B)) (book_imp ?D B))"
    by (rule book_lambda_I_conj_uncurry_schema[OF rich cl al bl])
  have lifted: "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_imp C (book_imp A B)) (book_imp ?D B))"
    by (rule book_lambda_I_derivable_mono[OF schema empty_subsetI])
  show ?thesis by (rule book_lambda_I_derivable.MP[OF derivation lifted book_lambda_I_imp_language[OF dl bl]])
qed

theorem book_lambda_I_conj_curry:
  assumes rich: "sg_rich G"
    and cl: "book_lambda_I_formula \<Sigma> G C"
    and al: "book_lambda_I_formula \<Sigma> G A"
    and bl: "book_lambda_I_formula \<Sigma> G B"
    and derivation: "book_lambda_I_derivable \<Sigma> G S
      (book_imp (book_not G (book_imp C (book_not G A))) B)"
  shows "book_lambda_I_derivable \<Sigma> G S (book_imp C (book_imp A B))"
proof -
  let ?D = "book_not G (book_imp C (book_not G A))"
  have schema: "book_lambda_I_derivable \<Sigma> G {}
    (book_imp (book_imp ?D B) (book_imp C (book_imp A B)))"
    by (rule book_lambda_I_conj_curry_schema[OF rich cl al bl])
  have lifted: "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_imp ?D B) (book_imp C (book_imp A B)))"
    by (rule book_lambda_I_derivable_mono[OF schema empty_subsetI])
  have result_language: "book_lambda_I_formula \<Sigma> G (book_imp C (book_imp A B))"
    by (rule book_lambda_I_imp_language[OF cl book_lambda_I_imp_language[OF al bl]])
  show ?thesis by (rule book_lambda_I_derivable.MP[OF derivation lifted result_language])
qed

end
