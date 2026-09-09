theory Bacon_Book_Typed_Name_Conversion
  imports Bacon_Book_Typed_Name_Map
begin

lemma book_typed_name_map_beta:
  assumes step: "named_beta_contract A B"
  shows "named_beta_contract (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B)"
  using step
proof (induction rule: named_beta_contract.induct)
  case (beta B n A)
  have permitted: "named_free_for (book_typed_name_map \<rho> B) n (book_typed_name_map \<rho> A)"
    by (simp only: book_typed_name_map_free_for; rule beta.hyps)
  show ?case by (simp only: book_typed_name_map.simps book_typed_name_map_subst; rule named_beta_contract.beta[OF permitted])
qed

lemma book_typed_name_map_eta:
  assumes step: "named_eta_contract A B"
  shows "named_eta_contract (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B)"
  using step by (induction rule: named_eta_contract.induct)
    (auto simp: book_typed_name_map_fv intro: named_eta_contract.eta)

lemma book_typed_name_map_compatible:
  assumes root: "\<And>A B. R A B \<Longrightarrow> T (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B)"
    and step: "named_compatible_step R A B"
  shows "named_compatible_step T (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B)"
  using step by (induction rule: named_compatible_step.induct)
    (auto intro: named_compatible_step.intros root)

lemma book_typed_name_map_beta_step:
  "named_compatible_step named_beta_contract A B \<Longrightarrow>
    named_compatible_step named_beta_contract (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B)"
  by (rule book_typed_name_map_compatible[where R=named_beta_contract and T=named_beta_contract and \<rho>=\<rho>];
    (rule book_typed_name_map_beta | assumption); assumption?)

lemma book_typed_name_map_eta_step:
  "named_compatible_step named_eta_contract A B \<Longrightarrow>
    named_compatible_step named_eta_contract (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B)"
  by (rule book_typed_name_map_compatible[where R=named_eta_contract and T=named_eta_contract and \<rho>=\<rho>];
    (rule book_typed_name_map_eta | assumption); assumption?)

lemma book_typed_name_map_imp:
  "book_typed_name_map \<rho> (book_imp A B) = book_imp (book_typed_name_map \<rho> A) (book_typed_name_map \<rho> B)"
  by (simp only: book_imp_def book_typed_name_map.simps)

lemma book_typed_name_map_all:
  "book_typed_name_map \<rho> (book_all G n A) = book_all G n (book_typed_name_map \<rho> A)"
  by (simp only: book_all_def book_typed_name_map.simps)

lemma book_typed_name_map_bottom:
  "book_typed_name_map \<rho> (book_bottom G) = book_bottom G"
  by (simp only: book_bottom_def book_typed_name_map.simps)

lemma book_typed_name_map_not_const:
  "book_typed_name_map \<rho> (book_not_const G) = book_not_const G"
  by (simp only: book_not_const_def book_typed_name_map.simps book_typed_name_map_imp book_typed_name_map_bottom)

lemma book_typed_name_map_not:
  "book_typed_name_map \<rho> (book_not G A) = book_not G (book_typed_name_map \<rho> A)"
  by (simp only: book_not_def book_typed_name_map.simps book_typed_name_map_not_const)

end
