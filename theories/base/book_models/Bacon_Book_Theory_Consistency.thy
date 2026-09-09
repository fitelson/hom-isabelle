theory Bacon_Book_Theory_Consistency
  imports Bacon_Book_Closed_Deduction Bacon_Book_Universal_Closure
begin

section \<open>Consistency as nonderivability of falsity\<close>

text \<open>
  S is consistent when S ⊬ ⊥ (Bacon, p.318). The definition below
  uses the existing theory derivability relation and the literal
  Table 4.1 formula ⊥. The premise set S need not be a closed theory,
  finite, or free of open formulas.

  Representation: book_theory_consistent abbreviates the absence of a
  derivation, not the existence of a model. The subsequent refutation
  result is the CLOSED-formula repair of Corollary 15.1, pp.318–319.
  Unrestricted open discharge is not assumed.
\<close>

definition book_theory_consistent ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_theory_consistent \<Sigma> G S \<longleftrightarrow>
    \<not> book_theory_derivable \<Sigma> G S (book_bottom G)"

section \<open>An empty-premise refutation schema\<close>

text \<open>
  ∅ ⊢ (¬A→⊥)→A. Under the local certificate assumption ¬A→⊥,
  assume ¬A and obtain ⊥ by MP. Certificate RAA yields A, and
  certificate deduction discharges ¬A→⊥. This schema allows open A:
  only MP-only certificates are discharged here.
\<close>

lemma book_theory_refutation_schema:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
  shows "book_theory_derivable \<Sigma> G {}
    (book_imp (book_imp (book_not G A) (book_bottom G)) A)"
proof -
  let ?H = "book_imp (book_not G A) (book_bottom G)"
  have nal: "book_theory_formula \<Sigma> G (book_not G A)"
    by (rule book_not_language[OF rich al])
  have bottom: "book_theory_formula \<Sigma> G (book_bottom G)"
    by (rule book_bottom_language[OF rich])
  have hl: "book_theory_formula \<Sigma> G ?H"
    by (rule book_imp_language[OF nal bottom])
  have implication_member: "?H \<in> insert (book_not G A) {?H}" by simp
  have conditional: "book_prop_certificate \<Sigma> G (insert (book_not G A) {?H}) ?H"
    by (rule book_prop_certificate.Assumption[OF implication_member hl])
  have negative: "book_prop_certificate \<Sigma> G (insert (book_not G A) {?H}) (book_not G A)"
    by (rule book_prop_certificate.Assumption[OF insertI1 nal])
  have contradiction: "book_prop_certificate \<Sigma> G (insert (book_not G A) {?H}) (book_bottom G)"
    by (rule book_prop_certificate.MP[OF negative conditional bottom])
  have positive: "book_prop_certificate \<Sigma> G {?H} A"
    by (rule book_prop_certificate_RAA[OF rich al contradiction])
  have discharged: "book_prop_certificate \<Sigma> G {} (book_imp ?H A)"
    by (rule book_prop_certificate_deduction[OF positive hl])
  show ?thesis by (rule book_prop_certificate_embeds[OF discharged])
qed

section \<open>The closed-formula refutation principle\<close>

theorem book_theory_closed_refutation:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and closed: "named_fv A = {}"
    and contradiction: "book_theory_derivable \<Sigma> G (insert (book_not G A) S) (book_bottom G)"
  shows "book_theory_derivable \<Sigma> G S A"
proof -
  have nal: "book_theory_formula \<Sigma> G (book_not G A)"
    by (rule book_not_language[OF rich al])
  have negative_closed: "named_fv (book_not G A) = {}"
    by (simp only: book_not_fv closed)
  have discharged: "book_theory_derivable \<Sigma> G S
    (book_imp (book_not G A) (book_bottom G))"
    by (rule book_theory_closed_deduction[OF rich nal negative_closed contradiction])
  have schema: "book_theory_derivable \<Sigma> G {}
    (book_imp (book_imp (book_not G A) (book_bottom G)) A)"
    by (rule book_theory_refutation_schema[OF rich al])
  have lifted: "book_theory_derivable \<Sigma> G S
    (book_imp (book_imp (book_not G A) (book_bottom G)) A)"
    by (rule book_theory_derivable_mono[OF schema empty_subsetI])
  show ?thesis by (rule book_theory_derivable.MP[OF discharged lifted al])
qed

corollary book_theory_closed_inconsistency_refutation:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and closed: "named_fv A = {}"
    and inconsistent: "\<not> book_theory_consistent \<Sigma> G (insert (book_not G A) S)"
  shows "book_theory_derivable \<Sigma> G S A"
proof -
  have contradiction: "book_theory_derivable \<Sigma> G (insert (book_not G A) S) (book_bottom G)"
    using inconsistent unfolding book_theory_consistent_def by blast
  show ?thesis by (rule book_theory_closed_refutation[OF rich al closed contradiction])
qed

corollary book_theory_consistent_insert_not:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and closed: "named_fv A = {}"
    and nonderivable: "\<not> book_theory_derivable \<Sigma> G S A"
  shows "book_theory_consistent \<Sigma> G (insert (book_not G A) S)"
  unfolding book_theory_consistent_def
proof
  assume contradiction: "book_theory_derivable \<Sigma> G (insert (book_not G A) S) (book_bottom G)"
  have positive: "book_theory_derivable \<Sigma> G S A"
    by (rule book_theory_closed_refutation[OF rich al closed contradiction])
  show False by (rule notE[OF nonderivable positive])
qed

section \<open>Open conclusions require negating their universal closure\<close>

text \<open>
  If S ⊬ A, then S∪{¬UC(A)} is consistent, where UC(A) universally
  closes all free variables of A. The added formula is NOT ¬A when A
  is open. Since S ⊢ UC(A) iff S ⊢ A, the closed-formula result applies
  without restricting S or the original conclusion A to closed formulas.
  This prepares a consistency construction; it proves no completeness
  or model-existence theorem.
\<close>

theorem book_theory_consistent_insert_not_universal_closure:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
    and nonderivable: "\<not> book_theory_derivable \<Sigma> G S A"
  shows "book_theory_consistent \<Sigma> G
    (insert (book_not G (book_universal_closure G A)) S)"
proof -
  have closure_language: "book_theory_formula \<Sigma> G (book_universal_closure G A)"
    by (rule book_universal_closure_language[OF al])
  have closure_nonderivable: "\<not> book_theory_derivable \<Sigma> G S (book_universal_closure G A)"
  proof
    assume derived: "book_theory_derivable \<Sigma> G S (book_universal_closure G A)"
    have original: "book_theory_derivable \<Sigma> G S A"
      by (rule iffD2[OF book_theory_universal_closure_iff[OF rich al] derived])
    show False by (rule notE[OF nonderivable original])
  qed
  show ?thesis by (rule book_theory_consistent_insert_not[
    OF rich closure_language book_universal_closure_closed closure_nonderivable])
qed

section \<open>Finite character of proof-theoretic consistency\<close>

text \<open>
  S is consistent iff every finite subset of S is consistent. This
  follows from finite proof support and monotonicity, not semantic
  compactness. It will justify unions in the extension construction
  without enumerating the signature or its formulas.
\<close>

lemma book_theory_consistent_subset:
  assumes consistent: "book_theory_consistent \<Sigma> G S" and subset: "T \<subseteq> S"
  shows "book_theory_consistent \<Sigma> G T"
  using consistent book_theory_derivable_mono[where \<Sigma>=\<Sigma> and G=G and S=T and T=S
      and A="book_bottom G", OF _ subset]
  unfolding book_theory_consistent_def by blast

theorem book_theory_consistent_finite_iff:
  "book_theory_consistent \<Sigma> G S \<longleftrightarrow>
    (\<forall>T. finite T \<longrightarrow> T \<subseteq> S \<longrightarrow> book_theory_consistent \<Sigma> G T)"
proof
  assume consistent: "book_theory_consistent \<Sigma> G S"
  show "\<forall>T. finite T \<longrightarrow> T \<subseteq> S \<longrightarrow> book_theory_consistent \<Sigma> G T"
    using book_theory_consistent_subset[OF consistent] by blast
next
  assume all_finite: "\<forall>T. finite T \<longrightarrow> T \<subseteq> S \<longrightarrow> book_theory_consistent \<Sigma> G T"
  show "book_theory_consistent \<Sigma> G S"
  proof (unfold book_theory_consistent_def, rule notI)
    assume contradiction: "book_theory_derivable \<Sigma> G S (book_bottom G)"
    obtain T where finite: "finite T" and subset: "T \<subseteq> S"
      and finite_contradiction: "book_theory_derivable \<Sigma> G T (book_bottom G)"
      using book_theory_derivable_finite_support[OF contradiction] by blast
    have consistent: "book_theory_consistent \<Sigma> G T" using all_finite finite subset by blast
    show False using consistent finite_contradiction unfolding book_theory_consistent_def by blast
  qed
qed

end
