theory Bacon_Source_Relational_H_Signature_Conservativity
  imports Bacon_Source_Relational_H_Retraction
begin

section \<open>Fresh R variables eliminate foreign constants from an H proof\<close>

text \<open>
  An Hᴿ theorem whose constants belong to Ω has a proof in Ω even
  if the original proof used a larger or different signature Σ.
  The finite whole-proof avoidance certificate chooses replacement
  variables only at R types. At unused non-R indices a fresh Prop
  name supplies the generic freshness condition, not a fictitious
  variable of that non-R type.

  The result is syntactic signature conservativity. No model, closed
  Ω inhabitant, full-F richness, signature inclusion or name-countability
  premise is used. A fresh-witness consistency extension remains a
  separate argument; it is not concluded from this theorem alone.
\<close>

theorem paper_R_named_H_foreign_constants_eliminate:
  assumes rich: "paper_R_rich G" and derivation: "paper_R_named_H \<Sigma> G A"
    and names: "named_in_signature \<Omega> A"
  shows "paper_R_named_H \<Omega> G A"
proof -
  obtain N where support: "paper_R_H_retraction_support \<Omega> G A N"
    using paper_R_named_H_retraction_support[where \<Omega>=\<Omega>, OF derivation] by blast
  have finite: "finite N" by (rule paper_R_H_retraction_support_finite[OF support])
  let ?v = "\<lambda>\<rho>. SOME n. G n = (if paper_R_type \<rho> then \<rho> else Prop) \<and> n \<notin> N"
  have chosen: "G (?v \<rho>) = (if paper_R_type \<rho> then \<rho> else Prop) \<and> ?v \<rho> \<notin> N" for \<rho>
  proof (rule someI_ex)
    have rt: "paper_R_type (if paper_R_type \<rho> then \<rho> else Prop)" by simp
    show "\<exists>n. G n = (if paper_R_type \<rho> then \<rho> else Prop) \<and> n \<notin> N"
      by (rule paper_R_rich_avoiding_variable[OF rich rt finite])
  qed
  have stock: "G (?v \<rho>) = \<rho>" if rt: "paper_R_type \<rho>" for \<rho>
    using conjunct1[OF chosen[of \<rho>]] by (simp only: if_P[OF rt])
  have fresh: "\<And>\<rho>. ?v \<rho> \<notin> N" by (rule conjunct2[OF chosen])
  have retracted: "paper_R_named_H \<Omega> G (named_retract \<Omega> ?v A)"
    by (rule paper_R_H_retraction_support_apply[OF support stock fresh])
  show ?thesis using retracted by (simp only: named_retract_fixed[OF names])
qed

corollary paper_R_named_H_signature_iff:
  assumes rich: "paper_R_rich G" and left_names: "named_in_signature \<Sigma> A"
    and right_names: "named_in_signature \<Omega> A"
  shows "paper_R_named_H \<Sigma> G A \<longleftrightarrow> paper_R_named_H \<Omega> G A"
proof
  assume proof_left: "paper_R_named_H \<Sigma> G A"
  show "paper_R_named_H \<Omega> G A" by (rule paper_R_named_H_foreign_constants_eliminate[OF rich proof_left right_names])
next
  assume proof_right: "paper_R_named_H \<Omega> G A"
  show "paper_R_named_H \<Sigma> G A" by (rule paper_R_named_H_foreign_constants_eliminate[OF rich proof_right left_names])
qed

end
