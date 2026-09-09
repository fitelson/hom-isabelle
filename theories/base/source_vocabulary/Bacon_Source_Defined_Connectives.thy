theory Bacon_Source_Defined_Connectives
  imports Bacon_Source_Conversion_Congruence
begin

section \<open>Literal Figure 1 definitions reduce to their material bodies\<close>

text \<open>
  → is λpq.¬p ∨ q; ↔ is λpq.(¬p ∨ q) ∧ (¬q ∨ p)
  (Bacon–Dorr Figure 1, p. 6).  We first normalize the primitive connective
  applications inside those λ-bodies, then apply the resulting functions.

  Isabelle representation: every equality below is signature-indexed βη
  conversion.  The target bodies use PNeg, PConj, and PDisj, not PImp.
  Status: computations for the literal paper abbreviations.  No identity
  between primitive implication and the paper definition is asserted.
\<close>

lemma paper_not_expansion:
  assumes arg: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (paper_to_pterm A) A'"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_not A)) (PNeg A')"
proof -
  have al: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    using source_conversion_left_language[OF arg] by (simp only: paper_to_pterm_language_iff)
  have head: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_not A)) (PNeg (paper_to_pterm A))"
    unfolding paper_not_def by (rule paper_not_application[OF al])
  show ?thesis by (rule pbeta_eta_equiv_in_signature.Trans[OF head source_conversion_Neg[OF arg]])
qed

lemma paper_and_expansion:
  assumes left: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (paper_to_pterm A) A'"
    and right: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (paper_to_pterm B) B'"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_and A B)) (PConj A' B')"
proof -
  have al: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    using source_conversion_left_language[OF left] by (simp only: paper_to_pterm_language_iff)
  have bl: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    using source_conversion_left_language[OF right] by (simp only: paper_to_pterm_language_iff)
  have head: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_and A B)) (PConj (paper_to_pterm A) (paper_to_pterm B))"
    unfolding paper_and_def by (rule paper_and_application[OF al bl])
  show ?thesis by (rule pbeta_eta_equiv_in_signature.Trans[OF head source_conversion_Conj[OF left right]])
qed

lemma paper_or_expansion:
  assumes left: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (paper_to_pterm A) A'"
    and right: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (paper_to_pterm B) B'"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_or A B)) (PDisj A' B')"
proof -
  have al: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    using source_conversion_left_language[OF left] by (simp only: paper_to_pterm_language_iff)
  have bl: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    using source_conversion_left_language[OF right] by (simp only: paper_to_pterm_language_iff)
  have head: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_or A B)) (PDisj (paper_to_pterm A) (paper_to_pterm B))"
    unfolding paper_or_def by (rule paper_or_application[OF al bl])
  show ?thesis by (rule pbeta_eta_equiv_in_signature.Trans[OF head source_conversion_Disj[OF left right]])
qed

lemma paper_slot_conversion:
  assumes "lookup \<Gamma> n = Some Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (paper_to_pterm (SVar n)) (PVar n)"
  unfolding sterm_translation.simps
  by (rule pbeta_eta_equiv_in_signature.Refl[OF has_ptype.PVar[OF assms]]) simp

lemma paper_imp_const_conversion:
  "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> (Arr Prop (Arr Prop Prop))
    (paper_to_pterm paper_imp_const)
    (PLam Prop (PLam Prop (PDisj (PNeg (PVar 1)) (PVar 0))))"
proof -
  have v1: "pbeta_eta_equiv_in_signature \<Sigma> (Prop # Prop # \<Gamma>) Prop
    (paper_to_pterm (SVar 1)) (PVar 1)"
    by (rule paper_slot_conversion) (simp add: lookup_def)
  have v0: "pbeta_eta_equiv_in_signature \<Sigma> (Prop # Prop # \<Gamma>) Prop
    (paper_to_pterm (SVar 0)) (PVar 0)"
    by (rule paper_slot_conversion) simp
  note body = paper_or_expansion[OF paper_not_expansion[OF v1] v0]
  note lifted = source_conversion_Lam[OF source_conversion_Lam[OF body]]
  show ?thesis using lifted by (simp only: paper_imp_const_def sterm_translation.simps)
qed

lemma paper_iff_const_conversion:
  "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> (Arr Prop (Arr Prop Prop))
    (paper_to_pterm paper_iff_const)
    (PLam Prop (PLam Prop
      (PConj (PDisj (PNeg (PVar 1)) (PVar 0)) (PDisj (PNeg (PVar 0)) (PVar 1)))))"
proof -
  have v1: "pbeta_eta_equiv_in_signature \<Sigma> (Prop # Prop # \<Gamma>) Prop
    (paper_to_pterm (SVar 1)) (PVar 1)"
    by (rule paper_slot_conversion) (simp add: lookup_def)
  have v0: "pbeta_eta_equiv_in_signature \<Sigma> (Prop # Prop # \<Gamma>) Prop
    (paper_to_pterm (SVar 0)) (PVar 0)"
    by (rule paper_slot_conversion) simp
  note forward = paper_or_expansion[OF paper_not_expansion[OF v1] v0]
  note backward = paper_or_expansion[OF paper_not_expansion[OF v0] v1]
  note body = paper_and_expansion[OF forward backward]
  note lifted = source_conversion_Lam[OF source_conversion_Lam[OF body]]
  show ?thesis using lifted by (simp only: paper_iff_const_def sterm_translation.simps)
qed

lemma paper_imp_application:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_imp A B)) (PDisj (PNeg (paper_to_pterm A)) (paper_to_pterm B))"
proof -
  note al = iffD2[OF paper_to_pterm_language_iff A]
  note bl = iffD2[OF paper_to_pterm_language_iff B]
  note head = paper_imp_const_conversion[where \<Sigma>=\<Sigma> and \<Gamma>=\<Gamma>]
  note applied = source_conversion_App_left[OF source_conversion_App_left[OF head al] bl]
  note reduced = source_target_binary_beta[OF source_conversion_right_language[OF head] al bl]
  have tail: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (PApp (PApp (PLam Prop (PLam Prop (PDisj (PNeg (PVar 1)) (PVar 0))))
      (paper_to_pterm A)) (paper_to_pterm B))
    (PDisj (PNeg (paper_to_pterm A)) (paper_to_pterm B))"
    using reduced by (simp add: psubst0_def source_target_subst_shift)
  show ?thesis using pbeta_eta_equiv_in_signature.Trans[OF applied tail]
    by (simp only: paper_imp_def sterm_translation.simps)
qed

lemma paper_iff_application:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_iff A B))
    (PConj (PDisj (PNeg (paper_to_pterm A)) (paper_to_pterm B))
      (PDisj (PNeg (paper_to_pterm B)) (paper_to_pterm A)))"
proof -
  note al = iffD2[OF paper_to_pterm_language_iff A]
  note bl = iffD2[OF paper_to_pterm_language_iff B]
  note head = paper_iff_const_conversion[where \<Sigma>=\<Sigma> and \<Gamma>=\<Gamma>]
  note applied = source_conversion_App_left[OF source_conversion_App_left[OF head al] bl]
  note reduced = source_target_binary_beta[OF source_conversion_right_language[OF head] al bl]
  have tail: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (PApp (PApp (PLam Prop (PLam Prop
      (PConj (PDisj (PNeg (PVar 1)) (PVar 0)) (PDisj (PNeg (PVar 0)) (PVar 1)))))
      (paper_to_pterm A)) (paper_to_pterm B))
    (PConj (PDisj (PNeg (paper_to_pterm A)) (paper_to_pterm B))
      (PDisj (PNeg (paper_to_pterm B)) (paper_to_pterm A)))"
    using reduced by (simp add: psubst0_def source_target_subst_shift)
  show ?thesis using pbeta_eta_equiv_in_signature.Trans[OF applied tail]
    by (simp only: paper_iff_def sterm_translation.simps)
qed

lemma paper_imp_expansion:
  assumes left: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (paper_to_pterm A) A'"
    and right: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (paper_to_pterm B) B'"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_imp A B)) (PDisj (PNeg A') B')"
proof -
  have al: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    using source_conversion_left_language[OF left] by (simp only: paper_to_pterm_language_iff)
  have bl: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    using source_conversion_left_language[OF right] by (simp only: paper_to_pterm_language_iff)
  show ?thesis by (rule pbeta_eta_equiv_in_signature.Trans[
    OF paper_imp_application[OF al bl] source_conversion_Disj[OF source_conversion_Neg[OF left] right]])
qed

lemma paper_iff_expansion:
  assumes left: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (paper_to_pterm A) A'"
    and right: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (paper_to_pterm B) B'"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (paper_iff A B))
    (PConj (PDisj (PNeg A') B') (PDisj (PNeg B') A'))"
proof -
  have al: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    using source_conversion_left_language[OF left] by (simp only: paper_to_pterm_language_iff)
  have bl: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    using source_conversion_left_language[OF right] by (simp only: paper_to_pterm_language_iff)
  note forward = source_conversion_Disj[OF source_conversion_Neg[OF left] right]
  note backward = source_conversion_Disj[OF source_conversion_Neg[OF right] left]
  show ?thesis by (rule pbeta_eta_equiv_in_signature.Trans[
    OF paper_iff_application[OF al bl] source_conversion_Conj[OF forward backward]])
qed

end
