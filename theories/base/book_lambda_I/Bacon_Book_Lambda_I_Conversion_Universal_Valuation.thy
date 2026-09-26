theory Bacon_Book_Lambda_I_Conversion_Universal_Valuation
  imports Bacon_Book_Lambda_I_Closed_Universal_Truth Bacon_Book_Lambda_I_Conversion_Logical_Values
begin

section \<open>The primitive universal symbol applied to a predicate class\<close>

text \<open>
  κ(∀σ)·[F]=[∀σF]. This is application in the internal λI-conversion
  quotient, with a closed λI predicate F.
  Source role: the universal clause in Bacon's term construction, p.321.
  No identity between alternative quantifier operators is used.
\<close>

lemma book_lambda_I_conversion_forall_app_class:
  assumes predicate: "F \<in> book_lambda_I_closed_terms \<Sigma> G (Arr \<sigma> Prop)"
  shows "book_lambda_I_conversion_app \<Sigma> G (Arr \<sigma> Prop) Prop
      (book_lambda_I_conversion_logical_value \<Sigma> G (SBAll \<sigma>))
      (book_lambda_I_conversion_class \<Sigma> G (Arr \<sigma> Prop) F) =
    book_lambda_I_conversion_class \<Sigma> G Prop (NApp (NLogical (SBAll \<sigma>)) F)"
proof -
  have operator: "NLogical (SBAll \<sigma>) \<in> book_lambda_I_closed_terms \<Sigma> G (Arr (Arr \<sigma> Prop) Prop)"
    using book_lambda_I_conversion_logical_closed_terms[where \<Sigma>=\<Sigma> and G=G and l="SBAll \<sigma>"]
    by (simp only: book_minimal_logical_type.simps)
  show ?thesis by (simp only: book_lambda_I_conversion_logical_value_def book_minimal_logical_type.simps;
      rule book_lambda_I_conversion_app_classes[OF operator predicate])
qed

lemma book_lambda_I_conversion_valuation_forall_class:
  assumes rich: "sg_rich G"
    and maximal: "book_lambda_I_closed_maximal_extension \<Sigma> G S M"
    and witnesses: "book_lambda_I_closed_constant_witness_complete \<Sigma> G M"
    and predicate: "F \<in> book_lambda_I_closed_terms \<Sigma> G (Arr \<sigma> Prop)"
  shows "book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop (NApp (NLogical (SBAll \<sigma>)) F))
    \<longleftrightarrow> (\<forall>A\<in>book_lambda_I_closed_terms \<Sigma> G \<sigma>.
      book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop (NApp F A)))"
proof -
  let ?U = "NApp (NLogical (SBAll \<sigma>)) F"
  have operator: "NLogical (SBAll \<sigma>) \<in> book_lambda_I_closed_terms \<Sigma> G (Arr (Arr \<sigma> Prop) Prop)"
    using book_lambda_I_conversion_logical_closed_terms[where \<Sigma>=\<Sigma> and G=G and l="SBAll \<sigma>"]
    by (simp only: book_minimal_logical_type.simps)
  have universal_closed: "?U \<in> book_lambda_I_closed_terms \<Sigma> G Prop"
    by (rule book_lambda_I_closed_terms_App[OF operator predicate])
  have projection: "book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop ?U) \<longleftrightarrow> ?U \<in> M"
    by (rule book_lambda_I_conversion_valuation_class[OF rich maximal universal_closed])
  have quantified: "?U \<in> M \<longleftrightarrow> (\<forall>A\<in>book_lambda_I_closed_terms \<Sigma> G \<sigma>. NApp F A \<in> M)"
    by (rule book_lambda_I_closed_maximal_forall_iff[OF rich maximal witnesses predicate])
  have instances: "(\<forall>A\<in>book_lambda_I_closed_terms \<Sigma> G \<sigma>. NApp F A \<in> M) \<longleftrightarrow>
    (\<forall>A\<in>book_lambda_I_closed_terms \<Sigma> G \<sigma>.
      book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop (NApp F A)))"
  proof (rule ball_cong[OF refl])
    fix A
    assume argument: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<sigma>"
    have application: "NApp F A \<in> book_lambda_I_closed_terms \<Sigma> G Prop"
      by (rule book_lambda_I_closed_terms_App[OF predicate argument])
    show "(NApp F A \<in> M) =
      book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop (NApp F A))"
      by (rule sym; rule book_lambda_I_conversion_valuation_class[OF rich maximal application])
  qed
  show ?thesis by (rule trans[OF projection trans[OF quantified instances]])
qed

section \<open>Quantifying over all class values, not just chosen terms\<close>

text \<open>
  Every a∈Dσ has a closed representative whose reconstructed class is a.
  Conversely, every closed λI term A:σ of Σ determines a member [A]σ of
  Dσ (a closed nonrelevant term need not determine a member).
  The next equivalence therefore transfers a bounded universal statement
  between closed terms and the entire domain, without any inhabitation,
  valuation, maximality or model premise.
\<close>

lemma book_lambda_I_conversion_closed_terms_ball_iff:
  "(\<forall>A\<in>book_lambda_I_closed_terms \<Sigma> G \<sigma>. P (book_lambda_I_conversion_class \<Sigma> G \<sigma> A))
    \<longleftrightarrow> (\<forall>a\<in>book_lambda_I_conversion_domain \<Sigma> G \<sigma>. P a)"
proof
  assume all_terms: "\<forall>A\<in>book_lambda_I_closed_terms \<Sigma> G \<sigma>. P (book_lambda_I_conversion_class \<Sigma> G \<sigma> A)"
  show "\<forall>a\<in>book_lambda_I_conversion_domain \<Sigma> G \<sigma>. P a"
  proof (rule ballI)
    fix a
    assume member: "a \<in> book_lambda_I_conversion_domain \<Sigma> G \<sigma>"
    have representative: "book_lambda_I_conversion_rep a \<in> book_lambda_I_closed_terms \<Sigma> G \<sigma>"
      by (rule book_lambda_I_conversion_rep_closed_terms[OF member])
    have holds: "P (book_lambda_I_conversion_class \<Sigma> G \<sigma> (book_lambda_I_conversion_rep a))"
      by (rule bspec[OF all_terms representative])
    show "P a" using holds by (simp only: book_lambda_I_conversion_rep_class[OF member])
  qed
next
  assume all_values: "\<forall>a\<in>book_lambda_I_conversion_domain \<Sigma> G \<sigma>. P a"
  show "\<forall>A\<in>book_lambda_I_closed_terms \<Sigma> G \<sigma>. P (book_lambda_I_conversion_class \<Sigma> G \<sigma> A)"
  proof (rule ballI)
    fix A
    assume member: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<sigma>"
    have domain: "book_lambda_I_conversion_class \<Sigma> G \<sigma> A \<in> book_lambda_I_conversion_domain \<Sigma> G \<sigma>"
      by (rule book_lambda_I_conversion_domainI[OF member])
    show "P (book_lambda_I_conversion_class \<Sigma> G \<sigma> A)" by (rule bspec[OF all_values domain])
  qed
qed

section \<open>The all-domain universal valuation clause\<close>

text \<open>
  v(κ(∀σ)·f)=1 iff every a∈Dσ satisfies v(f·a)=1.
  Source: Bacon, Definition 15.1, pp.314–315, and the term-model
  truth argument on p.321. The assumptions are closed maximal
  consistency, closed constant witnesses, richness, and typed membership
  of f. No full logical-model or environment premise is assumed.
\<close>

theorem book_lambda_I_conversion_forall_truth:
  assumes rich: "sg_rich G"
    and maximal: "book_lambda_I_closed_maximal_extension \<Sigma> G S M"
    and witnesses: "book_lambda_I_closed_constant_witness_complete \<Sigma> G M"
    and predicate: "f \<in> book_lambda_I_conversion_domain \<Sigma> G (Arr \<sigma> Prop)"
  shows "book_lambda_I_conversion_valuation M
      (book_lambda_I_conversion_app \<Sigma> G (Arr \<sigma> Prop) Prop
        (book_lambda_I_conversion_logical_value \<Sigma> G (SBAll \<sigma>)) f)
    \<longleftrightarrow> (\<forall>a\<in>book_lambda_I_conversion_domain \<Sigma> G \<sigma>.
      book_lambda_I_conversion_valuation M (book_lambda_I_conversion_app \<Sigma> G \<sigma> Prop f a))"
proof -
  let ?F = "book_lambda_I_conversion_rep f"
  have closed_F: "?F \<in> book_lambda_I_closed_terms \<Sigma> G (Arr \<sigma> Prop)"
    by (rule book_lambda_I_conversion_rep_closed_terms[OF predicate])
  have reconstructed: "book_lambda_I_conversion_class \<Sigma> G (Arr \<sigma> Prop) ?F = f"
    by (rule book_lambda_I_conversion_rep_class[OF predicate])
  have universal_application: "book_lambda_I_conversion_app \<Sigma> G (Arr \<sigma> Prop) Prop
      (book_lambda_I_conversion_logical_value \<Sigma> G (SBAll \<sigma>)) f =
    book_lambda_I_conversion_class \<Sigma> G Prop (NApp (NLogical (SBAll \<sigma>)) ?F)"
    using book_lambda_I_conversion_forall_app_class[OF closed_F] by (simp only: reconstructed)
  have universal_truth: "book_lambda_I_conversion_valuation M
      (book_lambda_I_conversion_class \<Sigma> G Prop (NApp (NLogical (SBAll \<sigma>)) ?F))
    \<longleftrightarrow> (\<forall>A\<in>book_lambda_I_closed_terms \<Sigma> G \<sigma>.
      book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop (NApp ?F A)))"
    by (rule book_lambda_I_conversion_valuation_forall_class[OF rich maximal witnesses closed_F])
  have instances: "(\<forall>A\<in>book_lambda_I_closed_terms \<Sigma> G \<sigma>.
      book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop (NApp ?F A)))
    \<longleftrightarrow> (\<forall>A\<in>book_lambda_I_closed_terms \<Sigma> G \<sigma>.
      book_lambda_I_conversion_valuation M (book_lambda_I_conversion_app \<Sigma> G \<sigma> Prop f (book_lambda_I_conversion_class \<Sigma> G \<sigma> A)))"
  proof (rule ball_cong[OF refl])
    fix A
    assume argument: "A \<in> book_lambda_I_closed_terms \<Sigma> G \<sigma>"
    have application: "book_lambda_I_conversion_app \<Sigma> G \<sigma> Prop f (book_lambda_I_conversion_class \<Sigma> G \<sigma> A) =
      book_lambda_I_conversion_class \<Sigma> G Prop (NApp ?F A)"
      using book_lambda_I_conversion_app_classes[OF closed_F argument] by (simp only: reconstructed)
    show "book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop (NApp ?F A)) =
      book_lambda_I_conversion_valuation M (book_lambda_I_conversion_app \<Sigma> G \<sigma> Prop f (book_lambda_I_conversion_class \<Sigma> G \<sigma> A))"
      by (simp only: application)
  qed
  have all_values: "(\<forall>A\<in>book_lambda_I_closed_terms \<Sigma> G \<sigma>.
      book_lambda_I_conversion_valuation M (book_lambda_I_conversion_app \<Sigma> G \<sigma> Prop f (book_lambda_I_conversion_class \<Sigma> G \<sigma> A)))
    \<longleftrightarrow> (\<forall>a\<in>book_lambda_I_conversion_domain \<Sigma> G \<sigma>.
      book_lambda_I_conversion_valuation M (book_lambda_I_conversion_app \<Sigma> G \<sigma> Prop f a))"
    by (rule book_lambda_I_conversion_closed_terms_ball_iff)
  show ?thesis by (simp only: universal_application;
      rule trans[OF universal_truth trans[OF instances all_values]])
qed

end
