theory Bacon_Source_Relational_Constant_Map_Binding
  imports Bacon_Source_Relational_Constant_Map
begin

section \<open>Literal substitution and contextual contractions commute\<close>

lemma paper_R_constant_map_subst:
  "paper_R_constant_map f (named_subst x B A) =
    named_subst x (paper_R_constant_map f B) (paper_R_constant_map f A)"
  by (induction A) (simp_all split: if_splits)

lemma paper_R_constant_map_free_for:
  "named_free_for (paper_R_constant_map f B) x (paper_R_constant_map f A) = named_free_for B x A"
  by (induction A) (simp_all only: paper_R_constant_map_simps named_free_for.simps paper_R_constant_map_fv)

lemma paper_R_constant_map_beta:
  assumes step: "named_beta_contract A B"
  shows "named_beta_contract (paper_R_constant_map f A) (paper_R_constant_map f B)"
  using step
proof (induction rule: named_beta_contract.induct)
  case (beta B x A)
  have permitted: "named_free_for (paper_R_constant_map f B) x (paper_R_constant_map f A)"
    by (simp only: paper_R_constant_map_free_for; rule beta.hyps)
  show ?case by (simp only: paper_R_constant_map_simps paper_R_constant_map_subst;
    rule named_beta_contract.beta[OF permitted])
qed

lemma paper_R_constant_map_eta:
  assumes step: "named_eta_contract A B"
  shows "named_eta_contract (paper_R_constant_map f A) (paper_R_constant_map f B)"
  using step
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  have fresh: "x \<notin> named_fv (paper_R_constant_map f F)"
    by (simp only: paper_R_constant_map_fv; rule eta.hyps)
  show ?case by (simp only: paper_R_constant_map_simps; rule named_eta_contract.eta[OF fresh])
qed

lemma paper_R_constant_map_compatible:
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>M N. R M N \<Longrightarrow> Q (paper_R_constant_map f M) (paper_R_constant_map f N)"
  shows "named_compatible_step Q (paper_R_constant_map f A) (paper_R_constant_map f B)"
  using step
proof (induction rule: named_compatible_step.induct)
  case (root M N)
  show ?case by (rule named_compatible_step.root[where R=Q, OF roots[OF root.hyps]])
next
  case (App_left M M' N)
  show ?case by (simp only: paper_R_constant_map_simps; rule named_compatible_step.App_left[OF App_left.IH])
next
  case (App_right N N' M)
  show ?case by (simp only: paper_R_constant_map_simps; rule named_compatible_step.App_right[OF App_right.IH])
next
  case (Lam_body M M' n)
  show ?case by (simp only: paper_R_constant_map_simps; rule named_compatible_step.Lam_body[OF Lam_body.IH])
qed

lemma paper_R_constant_map_beta_step:
  assumes step: "named_compatible_step named_beta_contract A B"
  shows "named_compatible_step named_beta_contract (paper_R_constant_map f A) (paper_R_constant_map f B)"
  by (rule paper_R_constant_map_compatible[OF step]; rule paper_R_constant_map_beta; assumption)

lemma paper_R_constant_map_eta_step:
  assumes step: "named_compatible_step named_eta_contract A B"
  shows "named_compatible_step named_eta_contract (paper_R_constant_map f A) (paper_R_constant_map f B)"
  by (rule paper_R_constant_map_compatible[OF step]; rule paper_R_constant_map_eta; assumption)

lemma paper_R_constant_map_raw_conversion:
  assumes conversion: "paper_R_raw_beta_eta G \<tau> A B"
  shows "paper_R_raw_beta_eta G \<tau> (paper_R_constant_map f A) (paper_R_constant_map f B)"
  using conversion
proof (induction rule: paper_R_raw_beta_eta.induct)
  case Refl
  show ?case by (rule paper_R_raw_beta_eta.Refl[OF paper_R_constant_map_type[OF Refl.hyps]])
next
  case Beta
  show ?case by (rule paper_R_raw_beta_eta.Beta[OF paper_R_constant_map_type[OF Beta.hyps(1)]
    paper_R_constant_map_type[OF Beta.hyps(2)] paper_R_constant_map_beta_step[OF Beta.hyps(3)]])
next
  case Eta
  show ?case by (rule paper_R_raw_beta_eta.Eta[OF paper_R_constant_map_type[OF Eta.hyps(1)]
    paper_R_constant_map_type[OF Eta.hyps(2)] paper_R_constant_map_eta_step[OF Eta.hyps(3)]])
next
  case Sym
  show ?case by (rule paper_R_raw_beta_eta.Sym[OF Sym.IH])
next
  case Trans
  show ?case by (rule paper_R_raw_beta_eta.Trans[OF Trans.IH])
qed

end
