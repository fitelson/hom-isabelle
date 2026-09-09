theory Bacon_Book_Term_Valuation
  imports Bacon_Book_Term_Interpretation_Naturality
    Bacon_Book_Environment_Development.Bacon_Book_Closed_Universal_Truth
begin

section \<open>Characteristic truth on the actual identity classes\<close>

definition book_C_term_valuation where
  "book_C_term_valuation w X = (book_C_identity_rep X \<in> w)"

definition book_C_term_logical_value where
  "book_C_term_logical_value \<Sigma> G w l =
    book_C_identity_class \<Sigma> G w (book_minimal_logical_type l) (NLogical l)"

lemma book_C_logical_closed_terms:
  "NLogical l \<in> book_closed_terms \<Sigma> G (book_minimal_logical_type l)"
  by (rule book_closed_termsI; simp add: book_language_logical_iff)

context book_C_identity_world
begin

lemma term_H_maximal:
  "book_closed_maximal_extension \<Sigma> G (book_C_closed_theorems \<Sigma> G) w"
  using maximal by (simp only: book_C_closed_maximal_extension_def Un_empty_right)

theorem term_valuation_class:
  assumes member: "A \<in> book_closed_terms \<Sigma> G Prop"
  shows "book_C_term_valuation w (book_C_identity_class \<Sigma> G w Prop A) \<longleftrightarrow> A \<in> w"
proof -
  let ?X = "book_C_identity_class \<Sigma> G w Prop A"
  have xd: "?X \<in> book_C_identity_domain \<Sigma> G w Prop" by (rule book_C_identity_domainI[OF member])
  have rm: "book_C_identity_rep ?X \<in> book_closed_terms \<Sigma> G Prop" by (rule identity_rep_typed[OF xd])
  have rep: "book_C_identity_rep ?X \<in> ?X" by (rule identity_rep_member[OF xd])
  have identity: "book_leibniz G Prop A (book_C_identity_rep ?X) \<in> w"
    using rep by (simp only: book_C_identity_class_member; blast)
  show ?thesis unfolding book_C_term_valuation_def
    using proposition_identity_membership[OF member rm identity] by blast
qed

theorem term_logical_value_typed:
  "book_C_term_logical_value \<Sigma> G w l \<in> book_C_identity_domain \<Sigma> G w (book_minimal_logical_type l)"
  unfolding book_C_term_logical_value_def by (rule book_C_identity_domainI[OF book_C_logical_closed_terms])

theorem term_valuation_bottom:
  "\<not> book_C_term_valuation w (book_C_identity_class \<Sigma> G w Prop (book_bottom G))"
proof -
  have closed: "book_bottom G \<in> book_closed_terms \<Sigma> G Prop"
    by (rule book_closed_termsI[OF book_bottom_language[OF rich] book_bottom_closed])
  show ?thesis by (simp only: term_valuation_class[OF closed]; rule book_closed_maximal_bottom_absent[OF term_H_maximal])
qed

theorem term_valuation_implication_class:
  assumes pm: "P \<in> book_closed_terms \<Sigma> G Prop" and qm: "Q \<in> book_closed_terms \<Sigma> G Prop"
  shows "book_C_term_valuation w (book_C_identity_class \<Sigma> G w Prop (book_imp P Q)) \<longleftrightarrow>
    (\<not> book_C_term_valuation w (book_C_identity_class \<Sigma> G w Prop P) \<or>
      book_C_term_valuation w (book_C_identity_class \<Sigma> G w Prop Q))"
proof -
  have im: "book_imp P Q \<in> book_closed_terms \<Sigma> G Prop"
    by (rule book_closed_termsI[OF book_imp_language[OF book_closed_terms_language[OF pm] book_closed_terms_language[OF qm]]];
      simp only: book_imp_fv book_closed_terms_closed[OF pm] book_closed_terms_closed[OF qm] Un_empty)
  show ?thesis by (simp only: term_valuation_class[OF im] term_valuation_class[OF pm] term_valuation_class[OF qm];
    rule book_closed_maximal_implication_iff[OF rich term_H_maximal book_closed_terms_language[OF pm]
      book_closed_terms_language[OF qm] book_closed_terms_closed[OF pm] book_closed_terms_closed[OF qm]])
qed

end

text \<open>
  Truth of a typed proposition class is membership of its representative
  in w. The class theorem proves that this does not depend on the
  selected representative, using the already proved proposition-identity
  membership law. Bottom is false and closed implication has material
  truth conditions. These are derived membership facts, not model fields
  or a substitution of the earlier βη-class valuation.
\<close>

end
