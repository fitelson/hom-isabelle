theory Bacon_Book_Lambda_I_Conversion_Valuation
  imports Bacon_Book_Lambda_I_Conversion_Classes Bacon_Book_Lambda_I_Closed_Maximal_Truth
begin

section \<open>The characteristic valuation on conversion classes\<close>

text \<open>
  Define v(X)=1 when some member of X belongs to the completed set T⁺.
  For a legitimate propositional class [A], conversion-invariance proves
  v([A])=1 iff A∈T⁺. Thus this definition is independent of which
  closed representative is used. Source: the characteristic-function and
  term-quotient construction on pp.320–321, with closed representatives.

  The definition is a Boolean function on the ambient set-of-terms carrier.
  The proved projection and logical laws concern typed propositional
  classes. No interpretation, quantifier clause, or model is assumed.
\<close>

definition book_lambda_I_conversion_valuation ::
  "'c book_named_term set \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_lambda_I_conversion_valuation M X \<longleftrightarrow> (\<exists>A\<in>X. A \<in> M)"

theorem book_lambda_I_conversion_valuation_class:
  assumes rich: "sg_rich G" and maximal: "book_lambda_I_closed_maximal_extension \<Sigma> G S M"
    and closed_term: "A \<in> book_lambda_I_closed_terms \<Sigma> G Prop"
  shows "book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop A) \<longleftrightarrow> A \<in> M"
proof
  assume truth: "book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop A)"
  obtain B where in_class: "B \<in> book_lambda_I_conversion_class \<Sigma> G Prop A" and member: "B \<in> M"
    using truth unfolding book_lambda_I_conversion_valuation_def by blast
  have other: "B \<in> book_lambda_I_closed_terms \<Sigma> G Prop"
    by (rule book_lambda_I_conversion_class_member_closed_terms[OF in_class])
  have conversion: "book_lambda_I_conv \<Sigma> G Prop A B"
    by (rule book_lambda_I_conversion_class_member_conversion[OF in_class])
  have same_truth: "A \<in> M \<longleftrightarrow> B \<in> M"
    by (rule book_lambda_I_closed_maximal_conv_iff[OF rich maximal
      book_lambda_I_closed_terms_prop[OF closed_term] book_lambda_I_closed_terms_prop[OF other]
      book_lambda_I_closed_terms_closed[OF closed_term] book_lambda_I_closed_terms_closed[OF other] conversion])
  show "A \<in> M" by (rule iffD2[OF same_truth member])
next
  assume member: "A \<in> M"
  have in_class: "A \<in> book_lambda_I_conversion_class \<Sigma> G Prop A"
    by (rule book_lambda_I_conversion_class_self_member[OF closed_term])
  show "book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop A)"
    unfolding book_lambda_I_conversion_valuation_def by (rule bexI[where x=A]; fact)
qed

theorem book_lambda_I_conversion_valuation_bottom:
  assumes rich: "sg_rich G" and maximal: "book_lambda_I_closed_maximal_extension \<Sigma> G S M"
  shows "\<not> book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop (book_bottom G))"
proof -
  have closed_term: "book_bottom G \<in> book_lambda_I_closed_terms \<Sigma> G Prop"
    by (rule book_lambda_I_closed_terms_formula[OF book_lambda_I_bottom_language[OF rich] book_bottom_closed])
  show ?thesis by (simp only: book_lambda_I_conversion_valuation_class[OF rich maximal closed_term];
      rule book_lambda_I_closed_maximal_bottom_absent[OF maximal])
qed

theorem book_lambda_I_conversion_valuation_implication:
  assumes rich: "sg_rich G" and maximal: "book_lambda_I_closed_maximal_extension \<Sigma> G S M"
    and first: "A \<in> book_lambda_I_closed_terms \<Sigma> G Prop"
    and second: "B \<in> book_lambda_I_closed_terms \<Sigma> G Prop"
  shows "book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop (book_imp A B))
    \<longleftrightarrow> (book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop A)
      \<longrightarrow> book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop B))"
proof -
  have al: "book_lambda_I_formula \<Sigma> G A" by (rule book_lambda_I_closed_terms_prop[OF first])
  have bl: "book_lambda_I_formula \<Sigma> G B" by (rule book_lambda_I_closed_terms_prop[OF second])
  have ac: "named_fv A = {}" by (rule book_lambda_I_closed_terms_closed[OF first])
  have bc: "named_fv B = {}" by (rule book_lambda_I_closed_terms_closed[OF second])
  have closed_imp: "named_fv (book_imp A B) = {}" by (simp add: book_imp_fv ac bc)
  have closed_term: "book_imp A B \<in> book_lambda_I_closed_terms \<Sigma> G Prop"
    by (rule book_lambda_I_closed_terms_formula[OF book_lambda_I_imp_language[OF al bl] closed_imp])
  show ?thesis by (simp only: book_lambda_I_conversion_valuation_class[OF rich maximal closed_term]
      book_lambda_I_conversion_valuation_class[OF rich maximal first]
      book_lambda_I_conversion_valuation_class[OF rich maximal second]
      book_lambda_I_closed_maximal_implication_iff[OF rich maximal al bl ac bc]; blast)
qed

end
