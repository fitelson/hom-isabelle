theory Bacon_Source_Relational_Classicism_A2_Closed_Identity
  imports Bacon_Source_Relational_Classicism_A2_H Bacon_Source_Relational_Closed_Identity_Vector
begin

section \<open>The closed-identity base case of native Appendix A.2\<close>

text \<open>
  From ⊢C A=ρB with A,B closed, derive
  ⊢C (λn⃗.A=ρB)=(λn⃗.⊤), using the literal Figure 1 truth term.
  The controlled environment lemma first gives
  (λn⃗.A=ρA)=(λn⃗.A=ρB). Ref is an H theorem, so the
  already proved H-base gives (λn⃗.A=ρA)=(λn⃗.⊤).
  Native symmetry and transitivity combine the two identities.

  Source: Appendix A.2's closed identity case, p.66. Native local H
  consequences are lifted through the p.12 C constructors; no new
  C rule is introduced. Closedness of both identity payloads is
  essential to the proved transport step. This does not assert
  general abstraction congruence, full A.2, Equivalence closure or
  the separate Figures 3–4 presentation theorem.
\<close>

theorem paper_R_classicism_A2_closed_identity:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A \<rho>"
    and bl: "paper_R_in_language \<Sigma> G B \<rho>"
    and ac: "named_fv A = {}" and bc: "named_fv B = {}"
    and binders: "list_all paper_R_type (map G ns)"
    and equality: "paper_R_classicism_proves \<Sigma> G (named_paper_eq \<rho> A B)"
  shows "paper_R_classicism_proves \<Sigma> G
    (named_paper_eq (paper_type_vector (map G ns) Prop)
      (named_lam_vec ns (named_paper_eq \<rho> A B)) (named_lam_vec ns (paper_R_named_top G)))"
proof -
  let ?S = "{P. paper_R_classicism_proves \<Sigma> G P}"
  let ?AA = "named_lam_vec ns (named_paper_eq \<rho> A A)"
  let ?AB = "named_lam_vec ns (named_paper_eq \<rho> A B)"
  let ?TT = "named_lam_vec ns (paper_R_named_top G)"
  let ?\<tau> = "paper_type_vector (map G ns) Prop"
  have aa: "paper_R_in_language \<Sigma> G (named_paper_eq \<rho> A A) Prop"
    by (rule paper_R_named_identity_language[OF al al])
  have ab: "paper_R_in_language \<Sigma> G (named_paper_eq \<rho> A B) Prop"
    by (rule paper_R_named_identity_language[OF al bl])
  have laa: "paper_R_in_language \<Sigma> G ?AA ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF aa binders])
  have lab: "paper_R_in_language \<Sigma> G ?AB ?\<tau>" by (rule paper_R_named_lam_vec_prop_language[OF ab binders])
  have ltt: "paper_R_in_language \<Sigma> G ?TT ?\<tau>"
    by (rule paper_R_named_lam_vec_prop_language[OF paper_R_named_top_language[OF rich] binders])
  have premise_member: "named_paper_eq \<rho> A B \<in> ?S" using equality by simp
  have premise: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq \<rho> A B)"
    by (rule paper_R_named_derivable.Assumption[OF premise_member ab])
  have transported: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?AA ?AB)"
    by (rule paper_R_closed_identity_vector_transport[OF rich al bl ac bc binders premise])
  have reverse: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?AB ?AA)"
    by (rule paper_R_named_identity_sym[OF rich laa lab transported])
  have ref_H: "paper_R_named_H \<Sigma> G (named_paper_eq \<rho> A A)" by (rule paper_R_named_H.Ref[OF aa])
  have ref_C: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<tau> ?AA ?TT)"
    by (rule paper_R_classicism_A2_H[OF rich ref_H binders])
  have truth_member: "named_paper_eq ?\<tau> ?AA ?TT \<in> ?S" using ref_C by simp
  have truth: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?AA ?TT)"
    by (rule paper_R_named_derivable.Assumption[OF truth_member paper_R_named_identity_language[OF laa ltt]])
  have result: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<tau> ?AB ?TT)"
    by (rule paper_R_named_identity_trans[OF rich lab laa ltt reverse truth])
  show ?thesis
  proof (rule paper_R_local_H_in_classicism[OF result])
    fix P
    assume member: "P \<in> ?S" and "paper_R_in_language \<Sigma> G P Prop"
    show "paper_R_classicism_proves \<Sigma> G P" using member by simp
  qed
qed

end
