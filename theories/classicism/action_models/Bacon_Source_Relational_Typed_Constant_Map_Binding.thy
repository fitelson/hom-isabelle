theory Bacon_Source_Relational_Typed_Constant_Map_Binding
  imports Bacon_Source_Relational_Typed_Constant_Map
begin

section \<open>Literal substitution and its capture condition are unchanged\<close>

lemma paper_R_typed_constant_map_subst:
  "paper_R_typed_constant_map \<rho> (named_subst x B A) =
    named_subst x (paper_R_typed_constant_map \<rho> B) (paper_R_typed_constant_map \<rho> A)"
  by (induction A) (simp_all split: if_splits)

lemma paper_R_typed_constant_map_free_for:
  "named_free_for (paper_R_typed_constant_map \<rho> B) x (paper_R_typed_constant_map \<rho> A) =
    named_free_for B x A"
  by (induction A) (simp_all only: paper_R_typed_constant_map.simps
    named_free_for.simps paper_R_typed_constant_map_fv)

lemma paper_R_typed_constant_map_beta:
  assumes step: "named_beta_contract A B"
  shows "named_beta_contract (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)"
  using step
proof (induction rule: named_beta_contract.induct)
  case (beta B x A)
  have permitted: "named_free_for (paper_R_typed_constant_map \<rho> B) x (paper_R_typed_constant_map \<rho> A)"
    by (simp only: paper_R_typed_constant_map_free_for; rule beta.hyps)
  show ?case by (simp only: paper_R_typed_constant_map.simps paper_R_typed_constant_map_subst;
    rule named_beta_contract.beta[OF permitted])
qed

lemma paper_R_typed_constant_map_eta:
  assumes step: "named_eta_contract A B"
  shows "named_eta_contract (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)"
  using step
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  have fresh: "x \<notin> named_fv (paper_R_typed_constant_map \<rho> F)"
    by (simp only: paper_R_typed_constant_map_fv; rule eta.hyps)
  show ?case by (simp only: paper_R_typed_constant_map.simps; rule named_eta_contract.eta[OF fresh])
qed

lemma paper_R_typed_constant_map_compatible:
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>M N. R M N \<Longrightarrow>
      Q (paper_R_typed_constant_map \<rho> M) (paper_R_typed_constant_map \<rho> N)"
  shows "named_compatible_step Q (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)"
  using step
proof (induction rule: named_compatible_step.induct)
  case (root M N)
  show ?case by (rule named_compatible_step.root[where R=Q, OF roots[OF root.hyps]])
next
  case App_left
  show ?case by (simp only: paper_R_typed_constant_map.simps; rule named_compatible_step.App_left[OF App_left.IH])
next
  case App_right
  show ?case by (simp only: paper_R_typed_constant_map.simps; rule named_compatible_step.App_right[OF App_right.IH])
next
  case Lam_body
  show ?case by (simp only: paper_R_typed_constant_map.simps; rule named_compatible_step.Lam_body[OF Lam_body.IH])
qed

lemma paper_R_typed_constant_map_beta_step:
  assumes step: "named_compatible_step named_beta_contract A B"
  shows "named_compatible_step named_beta_contract (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)"
  by (rule paper_R_typed_constant_map_compatible[OF step]; rule paper_R_typed_constant_map_beta; assumption)

lemma paper_R_typed_constant_map_eta_step:
  assumes step: "named_compatible_step named_eta_contract A B"
  shows "named_compatible_step named_eta_contract (paper_R_typed_constant_map \<rho> A) (paper_R_typed_constant_map \<rho> B)"
  by (rule paper_R_typed_constant_map_compatible[OF step]; rule paper_R_typed_constant_map_eta; assumption)

text \<open>
  These are forward literal root and contextual-step transports.
  Type indexing of names creates no variables and alters no binder,
  so the original free-for and η freshness conditions are preserved
  exactly. No α step, proof judgment, model, or term payload
  substitution for constants has been introduced.
\<close>

end
