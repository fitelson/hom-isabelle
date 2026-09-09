theory Bacon_H_BBK_Countable_Arbitrary_Model
  imports Bacon_H_BBK_Countable_Completeness
    Bacon_H_BBK_Strong_Completeness_Development.Bacon_H_Arbitrary_Model
begin

section \<open>Bacon--Dorr Theorem 3.2: arbitrary consistent theories on the naturals\<close>

text \<open>
  Conₕ(S) ⇒ ∃𝔐 with Dσ ⊆ ℕ, ∀A ∈ S, 𝔐 ⊨ A. Bacon–Dorr, Theorem 3.2, pp. 44–45,
  countable-domain refinement.

  Isabelle representation: Rename S to reserve witness names, build and code its
  canonical Henkin model, then define ⟦A⟧original,g = ⟦ι(A)⟧nat,g.

  Status: Arbitrary sets of typed closed sentences, with no finiteness assumption,
  over F and universal string signatures. Source-syntax and arbitrary-cardinality
  completeness remain separate.
\<close>

context H_closed_Henkin
begin

definition H_BBK_nat_original_denote ::
    "(nat \<Rightarrow> nat) \<Rightarrow> oterm \<Rightarrow> nat" where
  "H_BBK_nat_original_denote =
    H_BBK_constant_pullback H_BBK_nat_denote H_original_name"

lemma H_BBK_nat_original_constant:
  "H_BBK_nat_original_denote g (Const c \<sigma>) =
    H_BBK_nat_denote g (Const (H_original_name c) \<sigma>)"
  by (simp only: H_BBK_nat_original_denote_def H_BBK_constant_pullback_Const)

lemma H_BBK_nat_original_model:
  "bbk_model (\<lambda>_. UNIV) H_BBK_nat_domain H_BBK_nat_original_denote H_BBK_nat_holds"
  unfolding H_BBK_nat_original_denote_def
  by (rule H_BBK_constant_pullback_model[OF H_BBK_nat_model])

lemma H_BBK_nat_original_truth:
  assumes typed: "[] \<turnstile> A : Prop"
  shows "H_BBK_nat_holds (H_BBK_nat_original_denote g A) \<longleftrightarrow>
    H_rename_constants H_original_name A \<in> T"
proof -
  have renamed_type: "[] \<turnstile> H_rename_constants H_original_name A : Prop"
    by (rule H_rename_constants_type[OF typed])
  show ?thesis
    by (simp only: H_BBK_nat_original_denote_def H_BBK_constant_pullback_def
      H_BBK_nat_closed_truth_lemma[OF renamed_type])
qed

end

subsection \<open>Model existence for every typed consistent set of closed sentences\<close>

text \<open>
  𝔐original ⊨ S, not merely 𝔐nat ⊨ ι(S). Bacon–Dorr, Theorem 3.2, pp. 44–45,
  countable-domain refinement.

  Isabelle representation: Only constant interpretation is pulled back. Quantifiers
  retain the full coded domains, including witness values unnamed by original
  constants.

  Status: No same-language Henkin extension of arbitrary S or inverse on invalid codes
  is assumed.
\<close>

theorem H_arbitrary_nat_BBK_model_exists:
  assumes typed: "typed_theory [] S" and consistent: "H_consistent [] S"
  shows "\<exists>D :: otype \<Rightarrow> nat set.
    \<exists>J :: (nat \<Rightarrow> nat) \<Rightarrow> oterm \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool.
      bbk_model (\<lambda>_. UNIV) D J V \<and>
      (\<forall>\<sigma>. D \<sigma> \<subseteq> (UNIV :: nat set)) \<and>
      (\<forall>A \<in> S. \<forall>g. V (J g A))"
proof -
  obtain U where henkin_U: "H_Henkin_theory [] U"
    and extends: "image (H_rename_constants H_original_name) S \<subseteq> U"
  proof (rule H_arbitrary_Henkin_extension_exists[OF typed consistent])
    fix U
    assume henkin_U: "H_Henkin_theory [] U"
      and extends: "image (H_rename_constants H_original_name) S \<subseteq> U"
    show thesis by (rule that[where U=U, OF henkin_U extends])
  qed
  interpret C: H_closed_Henkin U by (unfold_locales) (rule henkin_U)
  let ?D = "H_closed_Henkin.H_BBK_nat_domain U"
  let ?J = "H_closed_Henkin.H_BBK_nat_original_denote U"
  let ?V = "H_closed_Henkin.H_BBK_nat_holds U"
  have model: "bbk_model (\<lambda>_. UNIV) ?D ?J ?V"
    by (rule C.H_BBK_nat_original_model)
  have domains: "\<forall>\<sigma>. ?D \<sigma> \<subseteq> (UNIV :: nat set)"
    by (rule allI) (rule C.H_BBK_nat_domain_subset_nat)
  have satisfies: "\<forall>A \<in> S. \<forall>g. ?V (?J g A)"
  proof (intro ballI allI)
    fix A g
    assume member: "A \<in> S"
    have A_type: "[] \<turnstile> A : Prop" by (rule typed_theoryD[OF typed member])
    have renamed_member: "H_rename_constants H_original_name A \<in>
      image (H_rename_constants H_original_name) S"
      by (rule imageI[OF member])
    have in_U: "H_rename_constants H_original_name A \<in> U"
      by (rule subsetD[OF extends renamed_member])
    show "?V (?J g A)"
      by (rule iffD2[OF C.H_BBK_nat_original_truth[OF A_type] in_U])
  qed
  show ?thesis
  proof (rule exI[where x="?D"], rule exI[where x="?J"], rule exI[where x="?V"])
    show "bbk_model (\<lambda>_. UNIV) ?D ?J ?V \<and>
      (\<forall>\<sigma>. ?D \<sigma> \<subseteq> (UNIV :: nat set)) \<and> (\<forall>A \<in> S. \<forall>g. ?V (?J g A))"
      by (rule conjI[OF model conjI[OF domains satisfies]])
  qed
qed

text \<open>
  All quantified variables still range over the full coded domains, including
  witness values not named by the original constants.  The only pullback is
  on the interpretations of names.  Neither a same-language Henkin extension
  of an arbitrary S nor an inverse on invalid codes is assumed.
\<close>

end
