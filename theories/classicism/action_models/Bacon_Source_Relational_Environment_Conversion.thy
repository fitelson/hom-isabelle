theory Bacon_Source_Relational_Environment_Conversion
  imports Bacon_Source_Relational_Environment_Contractions Bacon_Source_Relational_Environment_Substitution_Typing
    Bacon_Source_Relational_Conversion
begin

section \<open>Contextual contraction preserves closed-payload partial substitution\<close>

lemma paper_R_environment_subst_compatible:
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>r U V. R U V \<Longrightarrow>
      (\<And>n C. r n = Some C \<Longrightarrow> named_fv C = {}) \<Longrightarrow>
      Q (paper_R_environment_subst r U) (paper_R_environment_subst r V)"
    and closed: "\<And>n C. r n = Some C \<Longrightarrow> named_fv C = {}"
  shows "named_compatible_step Q (paper_R_environment_subst r A) (paper_R_environment_subst r B)"
  using step closed
proof (induction arbitrary: r rule: named_compatible_step.induct)
  case (root U V)
  show ?case by (rule named_compatible_step.root[where R=Q, OF roots[OF root.hyps root.prems]])
next
  case (App_left U V C)
  show ?case by (simp only: paper_R_environment_subst.simps;
    rule named_compatible_step.App_left[OF App_left.IH[OF App_left.prems]])
next
  case (App_right U V C)
  show ?case by (simp only: paper_R_environment_subst.simps;
    rule named_compatible_step.App_right[OF App_right.IH[OF App_right.prems]])
next
  case (Lam_body U V n)
  have body_closed: "\<And>m C. (r(n := None)) m = Some C \<Longrightarrow> named_fv C = {}"
    by (rule paper_R_environment_closed_delete[where r=r and n=n, OF Lam_body.prems]; assumption)
  show ?case by (simp only: paper_R_environment_subst.simps;
    rule named_compatible_step.Lam_body[OF Lam_body.IH[OF body_closed]])
qed

theorem paper_R_environment_subst_beta_step:
  fixes r :: "('c,'l) named_term named_assignment"
  assumes closed: "\<And>n C. r n = Some C \<Longrightarrow> named_fv C = {}"
    and step: "named_compatible_step named_beta_contract A B"
  shows "named_compatible_step named_beta_contract (paper_R_environment_subst r A) (paper_R_environment_subst r B)"
proof (rule paper_R_environment_subst_compatible[OF step _ closed])
  fix s :: "('c,'l) named_term named_assignment" and U V :: "('c,'l) named_term"
  assume contraction: "named_beta_contract U V" and payloads: "\<And>n C. s n = Some C \<Longrightarrow> named_fv C = {}"
  show "named_beta_contract (paper_R_environment_subst s U) (paper_R_environment_subst s V)"
    by (rule paper_R_environment_subst_beta_contract[OF payloads contraction])
qed

theorem paper_R_environment_subst_eta_step:
  fixes r :: "('c,'l) named_term named_assignment"
  assumes closed: "\<And>n C. r n = Some C \<Longrightarrow> named_fv C = {}"
    and step: "named_compatible_step named_eta_contract A B"
  shows "named_compatible_step named_eta_contract (paper_R_environment_subst r A) (paper_R_environment_subst r B)"
proof (rule paper_R_environment_subst_compatible[OF step _ closed])
  fix s :: "('c,'l) named_term named_assignment" and U V :: "('c,'l) named_term"
  assume contraction: "named_eta_contract U V" and payloads: "\<And>n C. s n = Some C \<Longrightarrow> named_fv C = {}"
  show "named_eta_contract (paper_R_environment_subst s U) (paper_R_environment_subst s V)"
    by (rule paper_R_environment_subst_eta_contract[OF payloads contraction])
qed

section \<open>Typed raw conversion in the independent R grammar\<close>

text \<open>
  Every intermediate R typing is preserved using the assigned payload
  types; every contextual β/η step uses the preceding raw lemmas.
  The premise is a partial assignment of typed closed terms, not a total
  assignment or a stock of closed terms at every type. Undefined names
  remain variables, so no adequacy or completion premise is needed.
  Source role: the βη property of the canonical interpretation in
  Theorem 3.2, p.45 n.64. No J, model, consistency or Henkin property
  is assumed; converting this syntax fact into class equality is separate.
\<close>

theorem paper_R_environment_subst_raw_conversion:
  assumes assigned: "paper_R_closed_term_assignment \<Sigma> G r" and conversion: "paper_R_raw_beta_eta G \<tau> A B"
  shows "paper_R_raw_beta_eta G \<tau> (paper_R_environment_subst r A) (paper_R_environment_subst r B)"
proof -
  have payloads: "paper_R_has_type G C (G n)" if "r n = Some C" for n C
    by (rule paper_R_closed_terms_type[OF paper_R_closed_term_assignmentD[OF assigned that]])
  have closed: "named_fv C = {}" if "r n = Some C" for n C
    by (rule paper_R_closed_terms_closed[OF paper_R_closed_term_assignmentD[OF assigned that]])
  show ?thesis using conversion
  proof (induction rule: paper_R_raw_beta_eta.induct)
    case Refl
    show ?case by (rule paper_R_raw_beta_eta.Refl[OF paper_R_environment_subst_type[OF Refl.hyps payloads]])
  next
    case Beta
    show ?case by (rule paper_R_raw_beta_eta.Beta[
      OF paper_R_environment_subst_type[OF Beta.hyps(1) payloads]
        paper_R_environment_subst_type[OF Beta.hyps(2) payloads] paper_R_environment_subst_beta_step[OF closed Beta.hyps(3)]])
  next
    case Eta
    show ?case by (rule paper_R_raw_beta_eta.Eta[
      OF paper_R_environment_subst_type[OF Eta.hyps(1) payloads]
        paper_R_environment_subst_type[OF Eta.hyps(2) payloads] paper_R_environment_subst_eta_step[OF closed Eta.hyps(3)]])
  next
    case Sym
    show ?case by (rule paper_R_raw_beta_eta.Sym[OF Sym.IH])
  next
    case Trans
    show ?case by (rule paper_R_raw_beta_eta.Trans[OF Trans.IH])
  qed
qed

end
