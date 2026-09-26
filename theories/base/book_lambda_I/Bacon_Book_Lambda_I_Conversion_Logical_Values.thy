theory Bacon_Book_Lambda_I_Conversion_Logical_Values
  imports Bacon_Book_Lambda_I_Conversion_Application Bacon_Book_Lambda_I_Conversion_Valuation
begin

section \<open>Logical symbols have typed conversion-class values\<close>

text \<open>
  Set κ(l)=[l]type(l). Each logical symbol is a typed closed term, so
  κ(l) belongs to its indicated domain without a richness assumption.
  Source role: interpreting the minimal logical signature in the term
  quotient on Bacon pp.320–321.
\<close>

definition book_lambda_I_conversion_logical_value ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> book_minimal_logical \<Rightarrow> 'c book_named_term set" where
  "book_lambda_I_conversion_logical_value \<Sigma> G l =
    book_lambda_I_conversion_class \<Sigma> G (book_minimal_logical_type l) (NLogical l)"

lemma book_lambda_I_conversion_logical_closed_terms:
  "NLogical l \<in> book_lambda_I_closed_terms \<Sigma> G (book_minimal_logical_type l)"
proof -
  have language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NLogical l) (book_minimal_logical_type l)"
    by (rule book_language_Logical[OF UNIV_I])
  have closed: "named_fv (NLogical l) = {}" by simp
  show ?thesis by (rule book_lambda_I_closed_termsI[OF language closed]; simp)
qed

theorem book_lambda_I_conversion_logical_value_type:
  "book_lambda_I_conversion_logical_value \<Sigma> G l \<in> book_lambda_I_conversion_domain \<Sigma> G (book_minimal_logical_type l)"
  unfolding book_lambda_I_conversion_logical_value_def
  by (rule book_lambda_I_conversion_domainI[OF book_lambda_I_conversion_logical_closed_terms])

section \<open>Saturated implication represents the literal implication formula\<close>

lemma book_lambda_I_conversion_implication_app_classes:
  assumes first: "A \<in> book_lambda_I_closed_terms \<Sigma> G Prop"
    and second: "B \<in> book_lambda_I_closed_terms \<Sigma> G Prop"
  shows "book_lambda_I_conversion_app \<Sigma> G Prop Prop
      (book_lambda_I_conversion_app \<Sigma> G Prop (Arr Prop Prop)
        (book_lambda_I_conversion_logical_value \<Sigma> G SImp) (book_lambda_I_conversion_class \<Sigma> G Prop A))
      (book_lambda_I_conversion_class \<Sigma> G Prop B) =
    book_lambda_I_conversion_class \<Sigma> G Prop (book_imp A B)"
proof -
  have operator: "NLogical SImp \<in> book_lambda_I_closed_terms \<Sigma> G (Arr Prop (Arr Prop Prop))"
    using book_lambda_I_conversion_logical_closed_terms[where l=SImp and \<Sigma>=\<Sigma> and G=G]
    by (simp only: book_minimal_logical_type.simps)
  have partial_closed: "NApp (NLogical SImp) A \<in> book_lambda_I_closed_terms \<Sigma> G (Arr Prop Prop)"
    by (rule book_lambda_I_closed_terms_App[OF operator first])
  have first_application: "book_lambda_I_conversion_app \<Sigma> G Prop (Arr Prop Prop)
      (book_lambda_I_conversion_logical_value \<Sigma> G SImp) (book_lambda_I_conversion_class \<Sigma> G Prop A) =
    book_lambda_I_conversion_class \<Sigma> G (Arr Prop Prop) (NApp (NLogical SImp) A)"
    by (simp only: book_lambda_I_conversion_logical_value_def book_minimal_logical_type.simps;
      rule book_lambda_I_conversion_app_classes[OF operator first])
  have second_application: "book_lambda_I_conversion_app \<Sigma> G Prop Prop
      (book_lambda_I_conversion_class \<Sigma> G (Arr Prop Prop) (NApp (NLogical SImp) A))
      (book_lambda_I_conversion_class \<Sigma> G Prop B) =
    book_lambda_I_conversion_class \<Sigma> G Prop (NApp (NApp (NLogical SImp) A) B)"
    by (rule book_lambda_I_conversion_app_classes[OF partial_closed second])
  show ?thesis by (simp only: first_application second_application book_imp_def)
qed

section \<open>The material implication law for arbitrary domain elements\<close>

text \<open>
  For X,Y∈Dₜ, v((κ(→)·X)·Y) iff (v(X) implies v(Y)).
  Choose the guarded closed representatives of X and Y, reconstruct
  their classes, and apply the separately proved formula-membership
  implication law. This covers EVERY propositional domain element,
  not merely a specified pair of syntactic representatives.

  No identity between alternative implication operators is used:
  book_imp itself is the saturated primitive SImp application. This
  leaf establishes neither universal-quantifier truth nor a full model.
\<close>

theorem book_lambda_I_conversion_implication_truth:
  assumes rich: "sg_rich G" and maximal: "book_lambda_I_closed_maximal_extension \<Sigma> G S M"
    and first: "X \<in> book_lambda_I_conversion_domain \<Sigma> G Prop"
    and second: "Y \<in> book_lambda_I_conversion_domain \<Sigma> G Prop"
  shows "book_lambda_I_conversion_valuation M
      (book_lambda_I_conversion_app \<Sigma> G Prop Prop
        (book_lambda_I_conversion_app \<Sigma> G Prop (Arr Prop Prop)
          (book_lambda_I_conversion_logical_value \<Sigma> G SImp) X) Y)
    \<longleftrightarrow> (book_lambda_I_conversion_valuation M X \<longrightarrow> book_lambda_I_conversion_valuation M Y)"
proof -
  let ?A = "book_lambda_I_conversion_rep X"
  let ?B = "book_lambda_I_conversion_rep Y"
  have ac: "?A \<in> book_lambda_I_closed_terms \<Sigma> G Prop" by (rule book_lambda_I_conversion_rep_closed_terms[OF first])
  have bc: "?B \<in> book_lambda_I_closed_terms \<Sigma> G Prop" by (rule book_lambda_I_conversion_rep_closed_terms[OF second])
  have X_class: "book_lambda_I_conversion_class \<Sigma> G Prop ?A = X" by (rule book_lambda_I_conversion_rep_class[OF first])
  have Y_class: "book_lambda_I_conversion_class \<Sigma> G Prop ?B = Y" by (rule book_lambda_I_conversion_rep_class[OF second])
  have application: "book_lambda_I_conversion_app \<Sigma> G Prop Prop
      (book_lambda_I_conversion_app \<Sigma> G Prop (Arr Prop Prop) (book_lambda_I_conversion_logical_value \<Sigma> G SImp) X) Y =
    book_lambda_I_conversion_class \<Sigma> G Prop (book_imp ?A ?B)"
    using book_lambda_I_conversion_implication_app_classes[OF ac bc] by (simp only: X_class Y_class)
  have truth: "book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop (book_imp ?A ?B))
    \<longleftrightarrow> (book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop ?A) \<longrightarrow>
      book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop ?B))"
    by (rule book_lambda_I_conversion_valuation_implication[OF rich maximal ac bc])
  show ?thesis using truth by (simp only: application X_class Y_class)
qed

section \<open>A displayed false propositional class\<close>

lemma book_lambda_I_conversion_bottom_in_domain:
  assumes rich: "sg_rich G"
  shows "book_lambda_I_conversion_class \<Sigma> G Prop (book_bottom G) \<in> book_lambda_I_conversion_domain \<Sigma> G Prop"
  by (rule book_lambda_I_conversion_domainI[
    OF book_lambda_I_closed_terms_formula[OF book_lambda_I_bottom_language[OF rich] book_bottom_closed]])

corollary book_lambda_I_conversion_false_exists:
  assumes rich: "sg_rich G" and maximal: "book_lambda_I_closed_maximal_extension \<Sigma> G S M"
  shows "\<exists>X\<in>book_lambda_I_conversion_domain \<Sigma> G Prop. \<not> book_lambda_I_conversion_valuation M X"
proof -
  have domain: "book_lambda_I_conversion_class \<Sigma> G Prop (book_bottom G) \<in> book_lambda_I_conversion_domain \<Sigma> G Prop"
    by (rule book_lambda_I_conversion_bottom_in_domain[OF rich])
  have false_value: "\<not> book_lambda_I_conversion_valuation M (book_lambda_I_conversion_class \<Sigma> G Prop (book_bottom G))"
    by (rule book_lambda_I_conversion_valuation_bottom[OF rich maximal])
  show ?thesis by (rule bexI[where x="book_lambda_I_conversion_class \<Sigma> G Prop (book_bottom G)"],
    rule false_value, rule domain)
qed

end
