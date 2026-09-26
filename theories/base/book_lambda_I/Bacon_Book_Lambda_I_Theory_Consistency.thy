theory Bacon_Book_Lambda_I_Theory_Consistency
  imports Bacon_Book_Lambda_I_Finite_Support
begin

section \<open>Consistency as nonderivability of falsity\<close>

text \<open>
  S is consistent when S ⊬ ⊥ (Bacon, p.318). The definition
  book_lambda_I_consistent, in Bacon_Book_Lambda_I_Calculus, uses the λI
  derivability relation and the literal Table 4.1 formula ⊥. The premise set S need not be a closed theory,
  finite, or free of open formulas.

  Representation: book_lambda_I_consistent abbreviates the absence of a
  derivation, not the existence of a model. The subsequent refutation
  result is the CLOSED-formula repair of Corollary 15.1, pp.318–319.
  Unrestricted open discharge is not assumed.
\<close>

section \<open>An empty-premise refutation schema\<close>

text \<open>
  ∅ ⊢ (¬A→⊥)→A. Under the local certificate assumption ¬A→⊥,
  assume ¬A and obtain ⊥ by MP. Certificate RAA yields A, and
  certificate deduction discharges ¬A→⊥. This schema allows open A:
  only MP-only certificates are discharged here.
\<close>

lemma book_lambda_I_refutation_schema:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
  shows "book_lambda_I_derivable \<Sigma> G {}
    (book_imp (book_imp (book_not G A) (book_bottom G)) A)"
proof -
  let ?H = "book_imp (book_not G A) (book_bottom G)"
  have nal: "book_lambda_I_formula \<Sigma> G (book_not G A)"
    by (rule book_lambda_I_not_language[OF rich al])
  have bottom: "book_lambda_I_formula \<Sigma> G (book_bottom G)"
    by (rule book_lambda_I_bottom_language[OF rich])
  have hl: "book_lambda_I_formula \<Sigma> G ?H"
    by (rule book_lambda_I_imp_language[OF nal bottom])
  have implication_member: "?H \<in> insert (book_not G A) {?H}" by simp
  have conditional: "book_lambda_I_certificate \<Sigma> G (insert (book_not G A) {?H}) ?H"
    by (rule book_lambda_I_certificate.Assumption[OF implication_member hl])
  have negative: "book_lambda_I_certificate \<Sigma> G (insert (book_not G A) {?H}) (book_not G A)"
    by (rule book_lambda_I_certificate.Assumption[OF insertI1 nal])
  have contradiction: "book_lambda_I_certificate \<Sigma> G (insert (book_not G A) {?H}) (book_bottom G)"
    by (rule book_lambda_I_certificate.MP[OF negative conditional bottom])
  have positive: "book_lambda_I_certificate \<Sigma> G {?H} A"
    by (rule book_lambda_I_certificate_RAA[OF rich al contradiction])
  have discharged: "book_lambda_I_certificate \<Sigma> G {} (book_imp ?H A)"
    by (rule book_lambda_I_certificate_deduction[OF positive hl])
  show ?thesis by (rule book_lambda_I_certificate_embeds[OF discharged])
qed

section \<open>The closed-formula refutation principle\<close>

theorem book_lambda_I_closed_refutation:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
    and closed: "named_fv A = {}"
    and contradiction: "book_lambda_I_derivable \<Sigma> G (insert (book_not G A) S) (book_bottom G)"
  shows "book_lambda_I_derivable \<Sigma> G S A"
proof -
  have nal: "book_lambda_I_formula \<Sigma> G (book_not G A)"
    by (rule book_lambda_I_not_language[OF rich al])
  have negative_closed: "named_fv (book_not G A) = {}"
    by (simp only: book_not_fv closed)
  have discharged: "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_not G A) (book_bottom G))"
    by (rule book_lambda_I_closed_deduction[OF rich nal negative_closed contradiction])
  have schema: "book_lambda_I_derivable \<Sigma> G {}
    (book_imp (book_imp (book_not G A) (book_bottom G)) A)"
    by (rule book_lambda_I_refutation_schema[OF rich al])
  have lifted: "book_lambda_I_derivable \<Sigma> G S
    (book_imp (book_imp (book_not G A) (book_bottom G)) A)"
    by (rule book_lambda_I_derivable_mono[OF schema empty_subsetI])
  show ?thesis by (rule book_lambda_I_derivable.MP[OF discharged lifted al])
qed

corollary book_lambda_I_closed_inconsistency_refutation:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
    and closed: "named_fv A = {}"
    and inconsistent: "\<not> book_lambda_I_consistent \<Sigma> G (insert (book_not G A) S)"
  shows "book_lambda_I_derivable \<Sigma> G S A"
proof -
  have contradiction: "book_lambda_I_derivable \<Sigma> G (insert (book_not G A) S) (book_bottom G)"
    using inconsistent unfolding book_lambda_I_consistent_def by blast
  show ?thesis by (rule book_lambda_I_closed_refutation[OF rich al closed contradiction])
qed

corollary book_lambda_I_consistent_insert_not:
  assumes rich: "sg_rich G" and al: "book_lambda_I_formula \<Sigma> G A"
    and closed: "named_fv A = {}"
    and nonderivable: "\<not> book_lambda_I_derivable \<Sigma> G S A"
  shows "book_lambda_I_consistent \<Sigma> G (insert (book_not G A) S)"
  unfolding book_lambda_I_consistent_def
proof
  assume contradiction: "book_lambda_I_derivable \<Sigma> G (insert (book_not G A) S) (book_bottom G)"
  have positive: "book_lambda_I_derivable \<Sigma> G S A"
    by (rule book_lambda_I_closed_refutation[OF rich al closed contradiction])
  show False by (rule notE[OF nonderivable positive])
qed

section \<open>Finite character of proof-theoretic consistency\<close>

text \<open>
  S is consistent iff every finite subset of S is consistent. This
  follows from finite proof support and monotonicity, not semantic
  compactness. It will justify unions in the extension construction
  without enumerating the signature or its formulas.
\<close>

lemma book_lambda_I_consistent_subset:
  assumes consistent: "book_lambda_I_consistent \<Sigma> G S" and subset: "T \<subseteq> S"
  shows "book_lambda_I_consistent \<Sigma> G T"
  using consistent book_lambda_I_derivable_mono[where \<Sigma>=\<Sigma> and G=G and S=T and T=S
      and A="book_bottom G", OF _ subset]
  unfolding book_lambda_I_consistent_def by blast

theorem book_lambda_I_consistent_finite_iff:
  "book_lambda_I_consistent \<Sigma> G S \<longleftrightarrow>
    (\<forall>T. finite T \<longrightarrow> T \<subseteq> S \<longrightarrow> book_lambda_I_consistent \<Sigma> G T)"
proof
  assume consistent: "book_lambda_I_consistent \<Sigma> G S"
  show "\<forall>T. finite T \<longrightarrow> T \<subseteq> S \<longrightarrow> book_lambda_I_consistent \<Sigma> G T"
    using book_lambda_I_consistent_subset[OF consistent] by blast
next
  assume all_finite: "\<forall>T. finite T \<longrightarrow> T \<subseteq> S \<longrightarrow> book_lambda_I_consistent \<Sigma> G T"
  show "book_lambda_I_consistent \<Sigma> G S"
  proof (unfold book_lambda_I_consistent_def, rule notI)
    assume contradiction: "book_lambda_I_derivable \<Sigma> G S (book_bottom G)"
    obtain T where finite: "finite T" and subset: "T \<subseteq> S"
      and finite_contradiction: "book_lambda_I_derivable \<Sigma> G T (book_bottom G)"
      using book_lambda_I_derivable_finite_support[OF contradiction] by blast
    have consistent: "book_lambda_I_consistent \<Sigma> G T" using all_finite finite subset by blast
    show False using consistent finite_contradiction unfolding book_lambda_I_consistent_def by blast
  qed
qed

end
