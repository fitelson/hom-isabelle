theory Bacon_Source_Relational_Conversion_Identity_Steps
  imports Bacon_Source_Relational_Identity_Derivations
begin

section \<open>A typed term step becomes a formula step in one identity operand\<close>

lemma paper_R_named_identity_operand_step:
  assumes step: "named_compatible_step R A B"
  shows "named_compatible_step R (named_paper_eq \<sigma> A A) (named_paper_eq \<sigma> A B)"
  unfolding named_paper_eq_def
  by (rule named_compatible_step.App_right[OF step])

lemma paper_R_named_H_identity_from_reflexive_iff:
  assumes rich: "paper_R_rich G" and left: "paper_R_in_language \<Sigma> G A \<sigma>"
    and right: "paper_R_in_language \<Sigma> G B \<sigma>"
    and biconditional: "paper_R_named_H \<Sigma> G
      (named_paper_iff G (named_paper_eq \<sigma> A A) (named_paper_eq \<sigma> A B))"
  shows "paper_R_named_H \<Sigma> G (named_paper_eq \<sigma> A B)"
proof -
  have aa: "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> A A) Prop"
    by (rule paper_R_named_identity_language[OF left left])
  have ab: "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> A B) Prop"
    by (rule paper_R_named_identity_language[OF left right])
  have conditional: "paper_R_named_H \<Sigma> G
    (named_paper_imp G (named_paper_eq \<sigma> A A) (named_paper_eq \<sigma> A B))"
    by (rule paper_R_named_H.MP[OF biconditional paper_R_named_H_iff_forward[OF rich aa ab]
      paper_R_named_paper_imp_language[OF rich aa ab]])
  have reflexive: "paper_R_named_H \<Sigma> G (named_paper_eq \<sigma> A A)"
    by (rule paper_R_named_H.Ref[OF aa])
  show ?thesis by (rule paper_R_named_H.MP[OF reflexive conditional ab])
qed

text \<open>
  Even when A and B have nonpropositional R type σ, a step A→B
  yields the formula step (A=σA)→(A=σB). The ACTUAL formula-level
  H β/η axiom supplies its biconditional. Ref and native PC then
  derive A=σB. Source: Figure 2, p.8, and the βη condition in the
  theorem-identity class construction, Theorem 3.2, footnote 64.
  This adds no conversion axiom at term types and uses no model law.
\<close>

theorem paper_R_named_H_beta_identity:
  assumes rich: "paper_R_rich G" and left: "paper_R_in_language \<Sigma> G A \<sigma>"
    and right: "paper_R_in_language \<Sigma> G B \<sigma>"
    and step: "named_compatible_step named_beta_contract A B"
  shows "paper_R_named_H \<Sigma> G (named_paper_eq \<sigma> A B)"
proof -
  have aa: "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> A A) Prop"
    by (rule paper_R_named_identity_language[OF left left])
  have ab: "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> A B) Prop"
    by (rule paper_R_named_identity_language[OF left right])
  have lifted: "named_compatible_step named_beta_contract
    (named_paper_eq \<sigma> A A) (named_paper_eq \<sigma> A B)"
    by (rule paper_R_named_identity_operand_step[OF step])
  have il: "paper_R_in_language \<Sigma> G
    (named_paper_iff G (named_paper_eq \<sigma> A A) (named_paper_eq \<sigma> A B)) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich aa ab])
  have biconditional: "paper_R_named_H \<Sigma> G
    (named_paper_iff G (named_paper_eq \<sigma> A A) (named_paper_eq \<sigma> A B))"
    by (rule paper_R_named_H.Beta[OF aa ab lifted il])
  show ?thesis by (rule paper_R_named_H_identity_from_reflexive_iff[OF rich left right biconditional])
qed

theorem paper_R_named_H_eta_identity:
  assumes rich: "paper_R_rich G" and left: "paper_R_in_language \<Sigma> G A \<sigma>"
    and right: "paper_R_in_language \<Sigma> G B \<sigma>"
    and step: "named_compatible_step named_eta_contract A B"
  shows "paper_R_named_H \<Sigma> G (named_paper_eq \<sigma> A B)"
proof -
  have aa: "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> A A) Prop"
    by (rule paper_R_named_identity_language[OF left left])
  have ab: "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> A B) Prop"
    by (rule paper_R_named_identity_language[OF left right])
  have lifted: "named_compatible_step named_eta_contract
    (named_paper_eq \<sigma> A A) (named_paper_eq \<sigma> A B)"
    by (rule paper_R_named_identity_operand_step[OF step])
  have il: "paper_R_in_language \<Sigma> G
    (named_paper_iff G (named_paper_eq \<sigma> A A) (named_paper_eq \<sigma> A B)) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich aa ab])
  have biconditional: "paper_R_named_H \<Sigma> G
    (named_paper_iff G (named_paper_eq \<sigma> A A) (named_paper_eq \<sigma> A B))"
    by (rule paper_R_named_H.Eta[OF aa ab lifted il])
  show ?thesis by (rule paper_R_named_H_identity_from_reflexive_iff[OF rich left right biconditional])
qed

end
