theory Bacon_Book_ZF_Nontrivial_Interpretation
  imports Bacon_Book_ZF_Generic_Interpretation_Existence
    Bacon_Book_ZF_Signature_Pullback
    Bacon_Book_ZF_Modal_Semantics.Bacon_Book_ZF_Nontrivial_Model
begin

context book_ZF_nontrivial_modal_model
begin

theorem typed_assignment_exists:
  assumes ww: "w \<in> explode W"
  shows "\<exists>g. book_env_typed (\<lambda>\<sigma>. explode (D \<sigma> w)) G g"
  by (rule book_total_assignment_exists; rule domain_inhabited[OF ww])

theorem nontrivial_signature_pullback:
  assumes maps: "\<And>\<sigma> c. c \<in> \<Sigma> \<sigma> \<Longrightarrow> \<rho> \<sigma> c \<in> signature \<sigma>"
  shows "book_ZF_nontrivial_modal_model W R root D i \<Sigma> (\<lambda>c \<sigma>. I (\<rho> \<sigma> c) \<sigma>)"
proof -
  have pulled: "book_ZF_modal_model W R root D i \<Sigma> (\<lambda>c \<sigma>. I (\<rho> \<sigma> c) \<sigma>)"
  proof (rule book_ZF_modal_model.intro[OF book_ZF_modal_structure_axioms])
    show "book_ZF_modal_model_axioms W R root D i \<Sigma> (\<lambda>c \<sigma>. I (\<rho> \<sigma> c) \<sigma>)"
      by (intro book_ZF_modal_model_axioms.intro;
        rule k_member s_member implication_member universal_member identity_member
          constants[OF maps]; assumption)
  qed
  show ?thesis
  proof (rule book_ZF_nontrivial_modal_model.intro[OF pulled])
    show "book_ZF_nontrivial_modal_model_axioms W D"
      by (rule book_ZF_nontrivial_modal_model_axioms.intro;
        (rule domain_inhabited | rule false_at_world); assumption)
  qed
qed

text \<open>
  The existing generic interpretation construction is inherited from
  the structural model. The stronger class additionally supplies
  actual typed assignments at every world, for every stock G.
  Changing only the interpretation of nonlogical constants leaves
  both nontriviality conditions unchanged.
\<close>

end

end
