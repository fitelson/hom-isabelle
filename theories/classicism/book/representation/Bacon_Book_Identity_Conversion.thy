theory Bacon_Book_Identity_Conversion
  imports Bacon_Book_Classicism_Development.Bacon_Book_Modal_Term_Application
    Bacon_Book_Environment_Development.Bacon_Book_Conversion_Environment
begin

section \<open>Typed conversion is contained in each world's identity relation\<close>

theorem book_H_conversion_identity:
  assumes rich: "sg_rich G"
    and al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    and bl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
    and conversion: "named_raw_beta_eta book_minimal_logical_type G \<sigma> A B"
  shows "book_H \<Sigma> G (book_leibniz G \<sigma> A B)"
proof (rule book_H_from_pointwise_models[OF rich book_leibniz_language[OF rich al bl]])
  fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k g
  assume model: "book_full_minimal_model D app \<Sigma> G J V k"
    and typed: "book_env_typed D G g"
  interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
  have same: "J g A = J g B"
    by (rule M.book_denote_conversion[OF UNIV_I UNIV_I al bl conversion typed])
  have member: "J g B \<in> D \<sigma>" by (rule M.denote_type[OF UNIV_I bl typed])
  show "V (J g (book_leibniz G \<sigma> A B))"
    by (simp only: M.book_leibniz_truth[OF rich typed al bl] same; rule book_leibniz_refl; rule member)
qed

context book_C_identity_world
begin

theorem identity_class_conversion:
  assumes am: "A \<in> book_closed_terms \<Sigma> G \<sigma>"
    and bm: "B \<in> book_closed_terms \<Sigma> G \<sigma>"
    and conversion: "named_raw_beta_eta book_minimal_logical_type G \<sigma> A B"
  shows "book_C_identity_class \<Sigma> G w \<sigma> A = book_C_identity_class \<Sigma> G w \<sigma> B"
proof -
  have original: "book_C_proves \<Sigma> G (book_leibniz G \<sigma> A B)"
    by (rule book_C_proves.H[OF book_H_conversion_identity[OF rich
      book_closed_terms_language[OF am] book_closed_terms_language[OF bm] conversion]])
  have closed: "named_fv (book_leibniz G \<sigma> A B) = {}"
    by (simp only: book_leibniz_fv book_closed_terms_closed[OF am] book_closed_terms_closed[OF bm] Un_empty)
  have member: "book_leibniz G \<sigma> A B \<in> w"
    by (rule book_C_closed_maximal_original_theorem[OF rich maximal original closed])
  show ?thesis by (simp only: identity_class_eq_iff[OF am bm]; rule member)
qed

end

text \<open>
  The class relation remains identity in w. We prove only the required
  inclusion: closed typed βη-convertible terms have the same identity
  class. We do not redefine these classes as βη classes or assert the
  converse. The H certificate is obtained from independently verified
  H completeness and the exact environment conversion law; no C
  completeness, Functionality or modal-model premise is used.
\<close>

end
