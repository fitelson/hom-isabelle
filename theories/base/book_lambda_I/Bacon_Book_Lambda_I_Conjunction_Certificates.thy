theory Bacon_Book_Lambda_I_Conjunction_Certificates
  imports Bacon_Book_Lambda_I_Propositional_Negation Bacon_Book_Lambda_I_Propositional_Explosion
begin

section \<open>Certificates for the expanded conjunction formula\<close>

text \<open>
  Write D = ¬(C→¬A). From C and A infer D; from D infer each of C
  and A. The Boolean expansion comes from Table 4.1, p.93; the
  certificates below use only the printed propositional schemas and
  previously proved β implications (Bacon, pp.97–98).

  Representation. D is kept as this expanded formula. It is not identified
  with the application of the closed λ-defined conjunction operator.
  All assumption discharge and reductio take place in MP-only
  book_lambda_I_certificate, not in unrestricted theory derivability.
  No global open deduction theorem, semantic truth premise, or new rule
  is assumed.
\<close>

theorem book_lambda_I_certificate_conj_intro:
  assumes rich: "sg_rich G"
    and first: "book_lambda_I_certificate \<Sigma> G S C"
    and second: "book_lambda_I_certificate \<Sigma> G S A"
  shows "book_lambda_I_certificate \<Sigma> G S (book_not G (book_imp C (book_not G A)))"
proof -
  let ?Q = "book_imp C (book_not G A)"
  let ?T = "insert ?Q S"
  have cl: "book_lambda_I_formula \<Sigma> G C" by (rule book_lambda_I_certificate_language[OF first])
  have al: "book_lambda_I_formula \<Sigma> G A" by (rule book_lambda_I_certificate_language[OF second])
  have nal: "book_lambda_I_formula \<Sigma> G (book_not G A)" by (rule book_lambda_I_not_language[OF rich al])
  have ql: "book_lambda_I_formula \<Sigma> G ?Q" by (rule book_lambda_I_imp_language[OF cl nal])
  have inclusion: "S \<subseteq> ?T" by blast
  have first_local: "book_lambda_I_certificate \<Sigma> G ?T C"
    by (rule book_lambda_I_certificate_mono[OF first inclusion])
  have second_local: "book_lambda_I_certificate \<Sigma> G ?T A"
    by (rule book_lambda_I_certificate_mono[OF second inclusion])
  have conditional: "book_lambda_I_certificate \<Sigma> G ?T ?Q"
    by (rule book_lambda_I_certificate.Assumption[OF insertI1 ql])
  have negative: "book_lambda_I_certificate \<Sigma> G ?T (book_not G A)"
    by (rule book_lambda_I_certificate.MP[OF first_local conditional nal])
  have contradiction: "book_lambda_I_certificate \<Sigma> G ?T (book_bottom G)"
    by (rule book_lambda_I_certificate_not_elim[OF rich second_local negative])
  show ?thesis by (rule book_lambda_I_certificate_not_intro[OF rich ql contradiction])
qed

theorem book_lambda_I_certificate_conj_left:
  assumes rich: "sg_rich G"
    and cl: "book_lambda_I_formula \<Sigma> G C"
    and al: "book_lambda_I_formula \<Sigma> G A"
    and conjunction: "book_lambda_I_certificate \<Sigma> G S (book_not G (book_imp C (book_not G A)))"
  shows "book_lambda_I_certificate \<Sigma> G S C"
proof -
  let ?Q = "book_imp C (book_not G A)"
  let ?T = "insert (book_not G C) S"
  let ?U = "insert C ?T"
  have ncl: "book_lambda_I_formula \<Sigma> G (book_not G C)"
    by (rule book_lambda_I_not_language[OF rich cl])
  have nal: "book_lambda_I_formula \<Sigma> G (book_not G A)"
    by (rule book_lambda_I_not_language[OF rich al])
  have positive_C: "book_lambda_I_certificate \<Sigma> G ?U C"
    by (rule book_lambda_I_certificate.Assumption[OF insertI1 cl])
  have negative_member: "book_not G C \<in> ?U" by simp
  have negative_C: "book_lambda_I_certificate \<Sigma> G ?U (book_not G C)"
    by (rule book_lambda_I_certificate.Assumption[OF negative_member ncl])
  have negative_A: "book_lambda_I_certificate \<Sigma> G ?U (book_not G A)"
    by (rule book_lambda_I_certificate_explosion[OF positive_C negative_C nal rich])
  have conditional: "book_lambda_I_certificate \<Sigma> G ?T ?Q"
    by (rule book_lambda_I_certificate_deduction[OF negative_A cl])
  have inclusion: "S \<subseteq> ?T" by blast
  have negative_Q: "book_lambda_I_certificate \<Sigma> G ?T (book_not G ?Q)"
    by (rule book_lambda_I_certificate_mono[OF conjunction inclusion])
  have contradiction: "book_lambda_I_certificate \<Sigma> G ?T (book_bottom G)"
    by (rule book_lambda_I_certificate_not_elim[OF rich conditional negative_Q])
  show ?thesis by (rule book_lambda_I_certificate_RAA[OF rich cl contradiction])
qed

theorem book_lambda_I_certificate_conj_right:
  assumes rich: "sg_rich G"
    and cl: "book_lambda_I_formula \<Sigma> G C"
    and al: "book_lambda_I_formula \<Sigma> G A"
    and conjunction: "book_lambda_I_certificate \<Sigma> G S (book_not G (book_imp C (book_not G A)))"
  shows "book_lambda_I_certificate \<Sigma> G S A"
proof -
  let ?Q = "book_imp C (book_not G A)"
  let ?T = "insert (book_not G A) S"
  have nal: "book_lambda_I_formula \<Sigma> G (book_not G A)"
    by (rule book_lambda_I_not_language[OF rich al])
  have negative_A: "book_lambda_I_certificate \<Sigma> G ?T (book_not G A)"
    by (rule book_lambda_I_certificate.Assumption[OF insertI1 nal])
  have conditional: "book_lambda_I_certificate \<Sigma> G ?T ?Q"
    by (rule book_lambda_I_certificate_weaken[OF negative_A cl])
  have inclusion: "S \<subseteq> ?T" by blast
  have negative_Q: "book_lambda_I_certificate \<Sigma> G ?T (book_not G ?Q)"
    by (rule book_lambda_I_certificate_mono[OF conjunction inclusion])
  have contradiction: "book_lambda_I_certificate \<Sigma> G ?T (book_bottom G)"
    by (rule book_lambda_I_certificate_not_elim[OF rich conditional negative_Q])
  show ?thesis by (rule book_lambda_I_certificate_RAA[OF rich al contradiction])
qed

end
