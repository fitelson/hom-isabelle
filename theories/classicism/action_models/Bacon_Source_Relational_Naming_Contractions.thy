theory Bacon_Source_Relational_Naming_Contractions
  imports Bacon_Source_Relational_Naming_Substitution
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Conversion_Steps
begin

section \<open>Root β and η contractions survive a fresh naming chart\<close>

lemma paper_R_naming_replace_beta_contract:
  assumes step: "named_beta_contract A B"
    and fresh: "x ` paper_R_naming_support A \<inter> named_vars A = {}"
  shows "named_beta_contract (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
  using step fresh
proof (induction rule: named_beta_contract.induct)
  case (beta C n E)
  have marker: "n \<notin> x ` paper_R_naming_support E"
    and capture: "x ` paper_R_naming_support C \<inter> named_vars E = {}"
    using beta.prems by auto
  have free_for: "named_free_for (paper_R_naming_replace x C) n (paper_R_naming_replace x E)"
    by (rule paper_R_naming_replace_free_for[OF beta.hyps marker capture])
  have replaced: "paper_R_naming_replace x (named_subst n C E) =
    named_subst n (paper_R_naming_replace x C) (paper_R_naming_replace x E)"
    by (rule paper_R_naming_replace_subst[OF marker])
  show ?case by (simp only: paper_R_naming_replace.simps replaced;
    rule named_beta_contract.beta[OF free_for])
qed

lemma paper_R_naming_replace_eta_contract:
  assumes step: "named_eta_contract A B"
    and fresh: "x ` paper_R_naming_support A \<inter> named_vars A = {}"
  shows "named_eta_contract (paper_R_naming_replace x A) (paper_R_naming_replace x B)"
  using step fresh
proof (induction rule: named_eta_contract.induct)
  case (eta n F)
  have markers: "n \<notin> x ` paper_R_naming_support F" using eta.prems by auto
  have remains: "n \<notin> named_fv (paper_R_naming_replace x F)"
    by (rule paper_R_naming_replace_preserves_fresh[OF eta.hyps markers])
  show ?case by (simp only: paper_R_naming_replace.simps;
    rule named_eta_contract.eta[OF remains])
qed

text \<open>
  Only the redex's support and variable names need be covered. In a β
  redex this already includes the body and payload, and the contracted
  binder itself. The replacement is the same cross-carrier operation on
  both endpoints. These are raw source contractions, not F conversion or
  semantic equality. Source: §1.1 and Figure 2, pp.5–8.
\<close>

end
