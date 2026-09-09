theory Bacon_Source_Relational_Intensionality_Proof
  imports Bacon_Source_Relational_Intensionality_Certificates
    Bacon_Source_Relational_Intensionality_Guarded_Replacement
    Bacon_Source_Relational_Classicism_H_Theory Bacon_Source_Relational_Box_Unfolding
begin

section \<open>Native C proves abstraction-form Intensionality\<close>

theorem paper_R_classicism_abstraction_intensionality:
  assumes rich: "paper_R_rich G"
    and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_classicism_proves \<Sigma> G
    (named_paper_imp G
      (paper_R_named_box G (paper_R_all_vec G ns (named_paper_iff G P Q)))
      (named_paper_eq (paper_type_vector (map G ns) Prop)
        (named_lam_vec ns P) (named_lam_vec ns Q)))"
proof -
  let ?R = "paper_R_all_vec G ns (named_paper_iff G P Q)"
  let ?E = "named_paper_or ?R (named_paper_not ?R)"
  let ?Box = "paper_R_named_box G ?R"
  let ?\<theta> = "paper_type_vector (map G ns) Prop"
  let ?LP = "named_lam_vec ns P"
  let ?LQ = "named_lam_vec ns Q"
  let ?PR = "named_lam_vec ns (named_paper_and P ?R)"
  let ?QR = "named_lam_vec ns (named_paper_and Q ?R)"
  let ?PE = "named_lam_vec ns (named_paper_and P ?E)"
  let ?QE = "named_lam_vec ns (named_paper_and Q ?E)"
  have il: "paper_R_in_language \<Sigma> G (named_paper_iff G P Q) Prop"
    by (rule paper_R_named_paper_iff_language[OF rich pl ql])
  have rl: "paper_R_in_language \<Sigma> G ?R Prop"
    by (rule paper_R_all_vec_language[OF il binders])
  have el: "paper_R_in_language \<Sigma> G ?E Prop"
    by (rule paper_R_named_or_language[OF rl paper_R_named_not_language[OF rl]])
  have box_language: "paper_R_in_language \<Sigma> G ?Box Prop"
    by (rule paper_R_named_box_language[OF rich rl])
  have pr: "paper_R_in_language \<Sigma> G (named_paper_and P ?R) Prop"
    by (rule paper_R_named_and_language[OF pl rl])
  have qr: "paper_R_in_language \<Sigma> G (named_paper_and Q ?R) Prop"
    by (rule paper_R_named_and_language[OF ql rl])
  have pe: "paper_R_in_language \<Sigma> G (named_paper_and P ?E) Prop"
    by (rule paper_R_named_and_language[OF pl el])
  have qe: "paper_R_in_language \<Sigma> G (named_paper_and Q ?E) Prop"
    by (rule paper_R_named_and_language[OF ql el])
  have lp: "paper_R_in_language \<Sigma> G ?LP ?\<theta>"
    by (rule paper_R_named_lam_vec_prop_language[OF pl binders])
  have lq: "paper_R_in_language \<Sigma> G ?LQ ?\<theta>"
    by (rule paper_R_named_lam_vec_prop_language[OF ql binders])
  have lpr: "paper_R_in_language \<Sigma> G ?PR ?\<theta>"
    by (rule paper_R_named_lam_vec_prop_language[OF pr binders])
  have lqr: "paper_R_in_language \<Sigma> G ?QR ?\<theta>"
    by (rule paper_R_named_lam_vec_prop_language[OF qr binders])
  have lpe: "paper_R_in_language \<Sigma> G ?PE ?\<theta>"
    by (rule paper_R_named_lam_vec_prop_language[OF pe binders])
  have lqe: "paper_R_in_language \<Sigma> G ?QE ?\<theta>"
    by (rule paper_R_named_lam_vec_prop_language[OF qe binders])

  text \<open>All three C identities are obtained before introducing the Box assumption.\<close>
  have guards_H: "paper_R_named_H \<Sigma> G
      (named_paper_iff G (named_paper_and P ?R) (named_paper_and Q ?R))"
    by (rule paper_R_named_H_intensionality_guards[OF rich pl ql binders])
  have guards_C: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<theta> ?PR ?QR)"
    by (rule paper_R_classicism_proves.Logical_Equivalence[OF guards_H pr qr binders])
  have left_H: "paper_R_named_H \<Sigma> G (named_paper_iff G (named_paper_and P ?E) P)"
    by (rule paper_R_named_H_intensionality_true_guard[OF rich pl rl])
  have left_C: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<theta> ?PE ?LP)"
    by (rule paper_R_classicism_proves.Logical_Equivalence[OF left_H pe pl binders])
  have right_H: "paper_R_named_H \<Sigma> G (named_paper_iff G (named_paper_and Q ?E) Q)"
    by (rule paper_R_named_H_intensionality_true_guard[OF rich ql rl])
  have right_C: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<theta> ?QE ?LQ)"
    by (rule paper_R_classicism_proves.Logical_Equivalence[OF right_H qe ql binders])

  have avoid_R: "set ns \<inter> named_fv ?R = {}"
    by (simp only: paper_R_all_vec_fv; blast)
  have avoid_E: "set ns \<inter> named_fv ?E = {}"
    using avoid_R by (simp only: named_paper_primitive_fv; blast)
  let ?T = "{A. paper_R_classicism_proves \<Sigma> G A}"
  let ?S = "insert ?Box ?T"
  have original_H_theory: "paper_R_H_theory \<Sigma> G ?T"
    by (rule paper_R_classicism_is_H_theory)
  have include_C: "paper_R_named_derivable \<Sigma> G ?S A"
    if derivation: "paper_R_classicism_proves \<Sigma> G A" for A
  proof -
    have member: "A \<in> ?S" using derivation by simp
    have language: "paper_R_in_language \<Sigma> G A Prop"
      by (rule paper_R_classicism_proves_language[OF derivation])
    show ?thesis by (rule paper_R_named_derivable.Assumption[OF member language])
  qed
  have assumed: "paper_R_named_derivable \<Sigma> G ?S ?Box"
    by (rule paper_R_named_derivable.Assumption[OF insertI1 box_language])
  have guard_identity: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop ?R ?E)"
    by (rule paper_R_named_derivable_box_unfold[OF rich rl assumed])
  have left_replacement: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<theta> ?PR ?PE)"
    by (rule paper_R_intensionality_guarded_replacement[
      OF rich pl rl el binders avoid_R avoid_E guard_identity])
  have right_replacement: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<theta> ?QR ?QE)"
    by (rule paper_R_intensionality_guarded_replacement[
      OF rich ql rl el binders avoid_R avoid_E guard_identity])
  have left_reduced: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<theta> ?PR ?LP)"
    by (rule paper_R_named_identity_trans[OF rich lpr lpe lp left_replacement include_C[OF left_C]])
  have right_reduced: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<theta> ?QR ?LQ)"
    by (rule paper_R_named_identity_trans[OF rich lqr lqe lq right_replacement include_C[OF right_C]])
  have left_reverse: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<theta> ?LP ?PR)"
    by (rule paper_R_named_identity_sym[OF rich lpr lp left_reduced])
  have middle: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<theta> ?LP ?QR)"
    by (rule paper_R_named_identity_trans[OF rich lp lpr lqr left_reverse include_C[OF guards_C]])
  have result: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<theta> ?LP ?LQ)"
    by (rule paper_R_named_identity_trans[OF rich lp lqr lq middle right_reduced])
  have discharged: "paper_R_named_derivable \<Sigma> G ?T
      (named_paper_imp G ?Box (named_paper_eq ?\<theta> ?LP ?LQ))"
    by (rule paper_R_named_derivable_deduction[OF rich box_language result])
  have member: "named_paper_imp G ?Box (named_paper_eq ?\<theta> ?LP ?LQ) \<in> ?T"
    by (rule paper_R_H_theory_local_consequences[OF original_H_theory discharged subset_refl])
  show ?thesis using member by simp
qed

text \<open>
  R is literally ∀n⃗.(P↔Q), and E is literally R∨¬R.
  Their free variables avoid the displayed prefix by the proved
  finite-universal FV equation; they need not be closed. The middle
  replacements use LL with explicit fresh markers and β certificates.
  Local deduction discharges the sole Box assumption, and the original
  C H-theory absorbs the resulting implication.

  This is the abstraction form of p.17 Intensionality. The prefix may
  be empty or contain repeated names, and residual free variables are
  allowed. No ζ is used under an assumption, no general λ-congruence
  or semantic model is invoked, and n.22's Modalized Functionality
  reduction is not claimed here.
\<close>

end
