theory Bacon_Book_ZF_Signature_Pullback
  imports Bacon_Book_ZF_Model_Truth
    Bacon_Book_Classicism_Development.Bacon_Book_Typed_Name_Map
begin

section \<open>Changing the nonlogical signature of a modal model\<close>

text \<open>
  Let ρσ map the declared constants of Σ into those of Ω.
  On a model for Ω, interpret c:σ by I(ρσ(c)):σ. The worlds,
  domains, counterparts and logical operators are unchanged.
  This semantic construction needs neither injectivity of ρσ nor
  countability. The imported name-map theory contains only syntax;
  no H or C derivability premise is used here.
\<close>

context book_ZF_modal_model
begin

theorem signature_pullback_model:
  assumes maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> c \<in> signature \<sigma>"
  shows "book_ZF_modal_model W R root D i \<Sigma> (\<lambda>c \<sigma>. I (\<rho> \<sigma> c) \<sigma>)"
proof (rule book_ZF_modal_model.intro[OF book_ZF_modal_structure_axioms])
  show "book_ZF_modal_model_axioms W R root D i \<Sigma> (\<lambda>c \<sigma>. I (\<rho> \<sigma> c) \<sigma>)"
    by (intro book_ZF_modal_model_axioms.intro;
      rule k_member s_member implication_member universal_member identity_member
        constants[OF maps]; assumption)
qed

end

context book_ZF_modal_interpretation
begin

theorem signature_pullback_interpretation:
  assumes maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> c \<in> signature \<sigma>"
  shows "book_ZF_modal_interpretation W R root D i \<Sigma>
    (\<lambda>c \<sigma>. I (\<rho> \<sigma> c) \<sigma>) G
    (\<lambda>w g A. J w g (book_typed_name_map \<rho> A))"
proof (rule book_ZF_modal_interpretation.intro[OF signature_pullback_model[OF maps]])
  have language: "book_in_language book_minimal_logical_type UNIV signature G
      (book_typed_name_map \<rho> A) \<tau>"
    if "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>" for A \<tau>
    by (rule book_typed_name_map_language[OF that maps])
  show "book_ZF_modal_interpretation_axioms W R root D i \<Sigma>
      (\<lambda>c \<sigma>. I (\<rho> \<sigma> c) \<sigma>) G
      (\<lambda>w g A. J w g (book_typed_name_map \<rho> A))"
    apply (rule book_ZF_modal_interpretation_axioms.intro)
    subgoal premises p for w g A \<tau>
      by (rule denote_type[OF p(1) language[OF p(2)] p(3)])
    subgoal by (simp only: book_typed_name_map.simps; rule denote_variable; assumption)
    subgoal premises p for w g c \<sigma>
      by (simp only: book_typed_name_map.simps; rule denote_constant[OF p(1) maps[OF p(2)] p(3)])
    subgoal by (simp only: book_typed_name_map.simps; rule denote_logical; assumption)
    subgoal premises p for w g F A \<sigma> \<tau>
      by (simp only: book_typed_name_map.simps;
        rule denote_application[OF p(1) language[OF p(2)] language[OF p(3)] p(4)])
    subgoal premises p for w g n A \<tau>
      by (simp only: book_typed_name_map.simps;
        rule denote_abstraction[OF p(1) language[OF p(2)] p(3)])
    done
qed

end

lemma book_ZF_signature_pullback_valid:
  "book_ZF_formula_valid D G (\<lambda>w g A. J w g (book_typed_name_map \<rho> A)) root A =
    book_ZF_formula_valid D G J root (book_typed_name_map \<rho> A)"
  by (simp only: book_ZF_formula_valid_def book_ZF_truth_at_def)

theorem book_ZF_signature_pullback_satisfies:
  "book_ZF_satisfies D G (\<lambda>w g A. J w g (book_typed_name_map \<rho> A)) root S =
    book_ZF_satisfies D G J root (book_typed_name_map \<rho> ` S)"
  by (simp only: book_ZF_satisfies_def book_ZF_signature_pullback_valid ball_simps(9))

text \<open>
  Both directions of truth preservation use the very same assignments.
  There is no closedness or finite-premise restriction. The model and
  interpretation theorems retain their language guards; the final two
  identities simply unfold the separately defined truth predicates.
\<close>

end
