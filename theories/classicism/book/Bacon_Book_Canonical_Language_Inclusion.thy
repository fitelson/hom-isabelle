theory Bacon_Book_Canonical_Language_Inclusion
  imports Bacon_Book_Ambient_Henkin_Successor
begin

section \<open>Necessitated identities witness the names in a world's language\<close>

lemma book_H_leibniz_reflexive:
  assumes rich: "sg_rich G" and al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
  shows "book_H \<Sigma> G (book_leibniz G \<sigma> A A)"
proof -
  have el: "book_theory_formula \<Sigma> G (book_leibniz G \<sigma> A A)"
    by (rule book_leibniz_language[OF rich al al])
  show ?thesis unfolding book_H_canonical_completeness[OF rich el]
  proof (unfold book_canonical_consequence_def, intro allI impI)
    fix D :: "otype \<Rightarrow> ('c book_henkin_name) book_named_term set set" and app J V k
    assume model: "book_full_minimal_model D app \<Sigma> G J V k" and "\<forall>B\<in>{}. book_formula_valid D G J V B"
    interpret M: book_full_minimal_model D app \<Sigma> G J V k by (rule model)
    show "book_formula_valid D G J V (book_leibniz G \<sigma> A A)"
    proof (rule book_formula_validI)
      fix g
      assume typed: "book_env_typed D G g"
      have member: "J g A \<in> D \<sigma>" by (rule M.denote_type[OF UNIV_I al typed])
      show "V (J g (book_leibniz G \<sigma> A A))"
        by (simp only: M.book_leibniz_truth[OF rich typed al al]; rule book_leibniz_refl; rule member)
    qed
  qed
qed

lemma book_C_closed_maximal_original_theorem:
  assumes rich: "sg_rich G" and world: "book_C_closed_maximal_extension \<Sigma> G T w"
    and theorem_C: "book_C_proves \<Sigma> G A" and closed: "named_fv A = {}"
  shows "A \<in> w"
  by (rule book_C_closed_maximal_consequence[OF rich world book_C_theory_from_C[OF rich theorem_C] closed])

lemma book_C_closed_world_constant_identity:
  assumes rich: "sg_rich G" and world: "book_C_closed_maximal_extension \<Sigma> G T w"
    and declared: "c \<in> \<Sigma> \<sigma>"
  shows "book_box G (book_leibniz G \<sigma> (NConst c \<sigma>) (NConst c \<sigma>)) \<in> w"
proof -
  let ?E = "book_leibniz G \<sigma> (NConst c \<sigma>) (NConst c \<sigma>)"
  have cl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NConst c \<sigma>) \<sigma>"
    by (simp only: book_language_const_iff; rule conjI[OF refl declared])
  have original: "book_C_proves \<Sigma> G ?E" by (rule book_C_proves.H[OF book_H_leibniz_reflexive[OF rich cl]])
  have necessary: "book_C_proves \<Sigma> G (book_box G ?E)" by (rule book_C_necessitation[OF rich original])
  have closed: "named_fv (book_box G ?E) = {}" by (simp only: book_box_fv book_leibniz_fv named_fv.simps Un_empty)
  show ?thesis by (rule book_C_closed_maximal_original_theorem[OF rich world necessary closed])
qed

theorem book_C_successor_language_inclusion:
  assumes rich: "sg_rich G" and world: "book_C_closed_maximal_extension \<Sigma> G T w"
    and target: "book_closed_formula_set \<Omega> G v"
    and accessible: "\<And>A. book_box G A \<in> w \<Longrightarrow> A \<in> v"
  shows "\<Sigma> \<sigma> \<subseteq> \<Omega> \<sigma>"
proof
  fix c
  assume declared: "c \<in> \<Sigma> \<sigma>"
  have necessary: "book_box G (book_leibniz G \<sigma> (NConst c \<sigma>) (NConst c \<sigma>)) \<in> w"
    by (rule book_C_closed_world_constant_identity[OF rich world declared])
  have at_target: "book_leibniz G \<sigma> (NConst c \<sigma>) (NConst c \<sigma>) \<in> v"
    by (rule accessible[OF necessary])
  have formula: "book_theory_formula \<Omega> G (book_leibniz G \<sigma> (NConst c \<sigma>) (NConst c \<sigma>))"
    by (rule conjunct1[OF book_closed_formula_set_member[OF target at_target]])
  have names: "named_in_signature \<Omega> (book_leibniz G \<sigma> (NConst c \<sigma>) (NConst c \<sigma>))"
    by (rule book_language_signature[OF formula])
  show "c \<in> \<Omega> \<sigma>" using names by (simp add: book_leibniz_def)
qed

text \<open>
  Definition 18.8 says that w ≤ v implies ℒ(Σw) ⊆ ℒ(Σv).
  We prove the constant-signature inclusion rather than build it into
  accessibility: for each declared c:σ, the closed theorem □(c =σ c)
  belongs to w. Its unboxed identity belongs to v, whose language must
  therefore declare c:σ. No modal completeness is used; the elementary
  reflexive identity is certified by the already verified H completeness.
\<close>

end
