theory Goodman_Expansion_Conversion
  imports Goodman_Logical_Expansion
begin

section \<open>Root and contextual βη steps survive logical expansion\<close>

lemma gi_expand_beta:
  "beta_contract A B \<Longrightarrow> sbeta_contract (gi_expand G k A) (gi_expand G k B)"
  by (induction rule: beta_contract.induct)
    (simp only: gi_expand.simps gi_expand_subst0; rule sbeta_contract.beta)

lemma gi_expand_eta:
  "eta_contract A B \<Longrightarrow> seta_contract (gi_expand G k A) (gi_expand G k B)"
  by (induction rule: eta_contract.induct)
    (simp only: gi_expand.simps gi_expand_shift; rule seta_contract.eta)

lemma gi_expand_compatible:
  assumes step: "compatible_step R A B"
    and root: "\<And>X Y. R X Y \<Longrightarrow> scompatible_step Q (gi_expand G k X) (gi_expand G k Y)"
  shows "scompatible_step Q (gi_expand G k A) (gi_expand G k B)"
  using step
  by (induction rule: compatible_step.induct)
    (auto intro: root scompatible_step.intros)

theorem gi_expand_beta_context:
  assumes step: "compatible_step beta_contract A B"
  shows "scompatible_step sbeta_contract (gi_expand G k A) (gi_expand G k B)"
  by (rule gi_expand_compatible[OF step], rule scompatible_step.root, rule gi_expand_beta; assumption)

theorem gi_expand_eta_context:
  assumes step: "compatible_step eta_contract A B"
  shows "scompatible_step seta_contract (gi_expand G k A) (gi_expand G k B)"
  by (rule gi_expand_compatible[OF step], rule scompatible_step.root, rule gi_expand_eta; assumption)

text \<open>
  These theorems preserve raw root contractions and replacement in every
  old constructor context, including equality, connectives and quantifiers.
  They do not assert unrestricted named conversion or object-language
  theoremhood. Typed, signature-guarded endpoints and the named-encoding
  bridge are still required when applying the source conversion rules.
\<close>

end
