theory Bacon_HLE_Boolean_Identities
  imports Bacon_H_Equivalence_Syntax_Bridge
begin

section \<open>The Boolean identities follow from H-certified Logical Equivalence\<close>

text \<open>
  Every Boolean identity is an identity between abstractions whose bodies
  are propositionally equivalent. H proves each such biconditional by PC;
  Logical Equivalence therefore gives the operation identity.
  Sources: Bacon Table 6.4 and Theorem 6.1; Bacon–Dorr Figure 3.

  Isabelle representation: the binary and ternary helpers merely expose
  the literal λ syntax of these identities. The seventh represented list
  entry identifies primitive Imp with ¬p ∨ q; its bodies are also PC
  equivalents. It is a representation bridge, not a seventh independent
  Boolean thesis in the source language. No C theorem is invoked.
\<close>

lemma HLE_PC_two:
  assumes pc: "prop_tautology ([Prop, Prop] @ \<Gamma>) (A \<longleftrightarrow>\<^sub>o B)"
  shows "HLE_proves \<Gamma> (Eq prop_bin_ty
    (Lam Prop (Lam Prop A)) (Lam Prop (Lam Prop B)))"
  using HLE_PC_abstraction[OF pc]
  by (simp add: C_abstract_prefix_def prop_bin_ty_def)

lemma HLE_PC_three:
  assumes pc: "prop_tautology ([Prop, Prop, Prop] @ \<Gamma>) (A \<longleftrightarrow>\<^sub>o B)"
  shows "HLE_proves \<Gamma> (Eq (Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
    (Lam Prop (Lam Prop (Lam Prop A))) (Lam Prop (Lam Prop (Lam Prop B))))"
  using HLE_PC_abstraction[OF pc]
  by (simp add: C_abstract_prefix_def)

lemma HLE_bool_comm_conj:
  "HLE_proves \<Gamma> bool_comm_conj"
  unfolding bool_comm_conj_def
  by (rule HLE_PC_two) (auto simp: prop_tautology_def; rule infer_type_sound; simp add: lookup_def)

lemma HLE_bool_comm_disj:
  "HLE_proves \<Gamma> bool_comm_disj"
  unfolding bool_comm_disj_def
  by (rule HLE_PC_two) (auto simp: prop_tautology_def; rule infer_type_sound; simp add: lookup_def)

lemma HLE_bool_dist_conj_disj:
  "HLE_proves \<Gamma> bool_dist_conj_disj"
  unfolding bool_dist_conj_disj_def
  by (rule HLE_PC_three) (auto simp: prop_tautology_def; rule infer_type_sound; simp add: lookup_def)

lemma HLE_bool_dist_disj_conj:
  "HLE_proves \<Gamma> bool_dist_disj_conj"
  unfolding bool_dist_disj_conj_def
  by (rule HLE_PC_three) (auto simp: prop_tautology_def; rule infer_type_sound; simp add: lookup_def)

lemma HLE_bool_dissolve_conj_disj:
  "HLE_proves \<Gamma> bool_dissolve_conj_disj"
  unfolding bool_dissolve_conj_disj_def
  by (rule HLE_PC_two) (auto simp: prop_tautology_def; rule infer_type_sound; simp add: lookup_def)

lemma HLE_bool_dissolve_disj_conj:
  "HLE_proves \<Gamma> bool_dissolve_disj_conj"
  unfolding bool_dissolve_disj_conj_def
  by (rule HLE_PC_two) (auto simp: prop_tautology_def; rule infer_type_sound; simp add: lookup_def)

lemma HLE_bool_material_imp:
  "HLE_proves \<Gamma> bool_material_imp"
  unfolding bool_material_imp_def
  by (rule HLE_PC_two) (auto simp: prop_tautology_def; rule infer_type_sound; simp add: lookup_def)

theorem HLE_BooleanIdentity:
  assumes "A \<in> set all_boolean_identities"
  shows "HLE_proves \<Gamma> A"
  using assms HLE_bool_comm_conj HLE_bool_comm_disj HLE_bool_dist_conj_disj
    HLE_bool_dist_disj_conj HLE_bool_dissolve_conj_disj
    HLE_bool_dissolve_disj_conj HLE_bool_material_imp
  by (auto simp: all_boolean_identities_def)

end
