theory Bacon_Source_Relational_Environment_Substitution_Typing
  imports Bacon_Source_Relational_Environment_Substitution Bacon_Source_Relational_Representative_Assignments
begin

section \<open>Native R typing needs only the assigned replacement entries\<close>

theorem paper_R_environment_subst_type:
  assumes typed: "paper_R_has_type G A \<tau>"
    and replacements: "\<And>n B. r n = Some B \<Longrightarrow> paper_R_has_type G B (G n)"
  shows "paper_R_has_type G (paper_R_environment_subst r A) \<tau>"
  using typed replacements
proof (induction arbitrary: r rule: paper_R_has_type.induct)
  case (Var n)
  show ?case
  proof (cases "r n")
    case None
    show ?thesis by (simp only: paper_R_environment_subst.simps None option.case;
      rule paper_R_has_type.Var[where G=G and n=n, OF Var.hyps])
  next
    case (Some B)
    have bt: "paper_R_has_type G B (G n)" by (rule Var.prems[OF Some])
    show ?thesis by (simp only: paper_R_environment_subst.simps Some option.case; rule bt)
  qed
next
  case (Const \<sigma> c)
  show ?case by (simp only: paper_R_environment_subst.simps; rule paper_R_has_type.Const[OF Const.hyps])
next
  case (Logical l)
  show ?case by (simp only: paper_R_environment_subst.simps; rule paper_R_has_type.Logical[OF Logical.hyps])
next
  case (App F \<sigma> \<tau> B)
  show ?case by (simp only: paper_R_environment_subst.simps;
    rule paper_R_has_type.App[OF App.IH(1)[OF App.prems] App.IH(2)[OF App.prems]])
next
  case (Lam B \<tau> n)
  have body_replacements: "paper_R_has_type G C (G m)" if assigned: "(r(n := None)) m = Some C" for m C
  proof -
    have old: "r m = Some C" using assigned by (auto split: if_splits)
    show ?thesis by (rule Lam.prems[OF old])
  qed
  show ?case by (simp only: paper_R_environment_subst.simps;
    rule paper_R_has_type.Lam[OF Lam.IH[OF body_replacements] Lam.hyps(2,3)])
qed

lemma paper_R_environment_subst_signature:
  assumes names: "named_in_signature \<Sigma> A"
    and replacements: "\<And>n B. r n = Some B \<Longrightarrow> named_in_signature \<Sigma> B"
  shows "named_in_signature \<Sigma> (paper_R_environment_subst r A)"
  using names replacements
proof (induction A arbitrary: r)
  case (NVar n)
  show ?case by (cases "r n") (auto intro: NVar.prems(2))
next
  case (NConst c \<sigma>)
  show ?case using NConst.prems by simp
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fn: "named_in_signature \<Sigma> F" and an: "named_in_signature \<Sigma> A" using NApp.prems(1) by simp_all
  show ?case by (simp only: paper_R_environment_subst.simps named_in_signature.simps;
    rule conjI[OF NApp.IH(1)[OF fn NApp.prems(2)] NApp.IH(2)[OF an NApp.prems(2)]])
next
  case (NLam n A)
  have an: "named_in_signature \<Sigma> A" using NLam.prems(1) by simp
  have body_replacements: "named_in_signature \<Sigma> B" if assigned: "(r(n := None)) m = Some B" for m B
  proof -
    have old: "r m = Some B" using assigned by (auto split: if_splits)
    show ?thesis by (rule NLam.prems(2)[OF old])
  qed
  show ?case by (simp only: paper_R_environment_subst.simps named_in_signature.simps;
    rule NLam.IH[OF an body_replacements])
qed

theorem paper_R_environment_subst_language:
  assumes language: "paper_R_in_language \<Sigma> G A \<tau>" and assigned: "paper_R_closed_term_assignment \<Sigma> G r"
  shows "paper_R_in_language \<Sigma> G (paper_R_environment_subst r A) \<tau>"
proof -
  have typed: "paper_R_has_type G A \<tau>" and names: "named_in_signature \<Sigma> A"
    using language unfolding paper_R_in_language_def by blast+
  have payload_types: "paper_R_has_type G B (G n)" if "r n = Some B" for n B
    by (rule paper_R_closed_terms_type[OF paper_R_closed_term_assignmentD[OF assigned that]])
  have payload_names: "named_in_signature \<Sigma> B" if "r n = Some B" for n B
  proof -
    have bl: "paper_R_in_language \<Sigma> G B (G n)"
      by (rule paper_R_closed_terms_language[OF paper_R_closed_term_assignmentD[OF assigned that]])
    show ?thesis using bl unfolding paper_R_in_language_def by blast
  qed
  show ?thesis unfolding paper_R_in_language_def
    by (rule conjI[OF paper_R_environment_subst_type[OF typed payload_types]
      paper_R_environment_subst_signature[OF names payload_names]])
qed

section \<open>Adequate class assignments produce actual typed closed terms\<close>

theorem paper_R_representative_substitution_closed_terms:
  assumes language: "paper_R_in_language \<Sigma> G A \<tau>"
    and typed: "named_env_typed (paper_R_identity_domain \<Sigma> G S) G g" and adequate: "named_adequate g A"
  shows "paper_R_environment_subst (paper_R_representative_assignment g) A \<in> paper_R_closed_terms \<Sigma> G \<tau>"
proof -
  let ?r = "paper_R_representative_assignment g"
  have assigned: "paper_R_closed_term_assignment \<Sigma> G ?r" by (rule paper_R_representative_assignment_typed[OF typed])
  have result_language: "paper_R_in_language \<Sigma> G (paper_R_environment_subst ?r A) \<tau>"
    by (rule paper_R_environment_subst_language[OF language assigned])
  have closed_payloads: "named_fv B = {}" if "?r n = Some B" for n B
    by (rule paper_R_closed_terms_closed[OF paper_R_closed_term_assignmentD[OF assigned that]])
  have covering: "named_adequate ?r A" by (simp only: paper_R_representative_assignment_adequate_iff; rule adequate)
  have result_closed: "named_fv (paper_R_environment_subst ?r A) = {}"
    by (rule paper_R_environment_subst_adequate_closed[OF closed_payloads covering])
  show ?thesis by (rule paper_R_closed_termsI[OF result_language result_closed])
qed

lemma paper_R_representative_substitution_Lam:
  "paper_R_environment_subst (paper_R_representative_assignment g) (NLam n A) =
    NLam n (paper_R_environment_subst (paper_R_representative_assignment (g(n := None))) A)"
  by (simp only: paper_R_environment_subst.simps paper_R_representative_assignment_delete)

text \<open>
  No full-F variable stock is needed: typing obligations arise only from
  assigned entries and from variables occurring in the R typing derivation.
  Adequacy, rather than a forced totalization, closes the final term.
  These are syntax prerequisites only. Representative independence,
  a denotation J, valuation and the canonical-model laws remain separate.
\<close>

end
