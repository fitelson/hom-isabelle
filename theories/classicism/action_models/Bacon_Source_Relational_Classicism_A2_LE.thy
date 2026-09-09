theory Bacon_Source_Relational_Classicism_A2_LE
  imports Bacon_Source_Relational_Classicism_A2_Local Bacon_Source_Relational_Classicism_A2_Closed_Identity
begin

section \<open>The open Logical Equivalence base case follows from a closed identity\<close>

text \<open>
  An H-certified LE instance may leave free variables. Recover it as
  a local H consequence of one closed LE identity. The closed-identity
  base case gives the abstraction-to-truth property for that premise
  at every prefix, and the local H lifting theorem transfers it to
  the original open instance.

  Source role: the native p.12 presentation and Appendix A.2. No open
  identity is silently treated as closed. H, LE and MP cases are now
  available separately; the subsequent Gen/Inst leaves and Classicism_A2
  complete the native p.12 induction.
\<close>

theorem paper_R_classicism_A2_LE:
  assumes rich: "paper_R_rich G"
    and certificate: "paper_R_named_H \<Sigma> G (named_paper_iff G P Q)"
    and pl: "paper_R_in_language \<Sigma> G P Prop" and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and inner: "list_all paper_R_type (map G vs)"
    and outer: "list_all paper_R_type (map G ns)"
  shows "paper_R_classicism_proves \<Sigma> G
    (named_paper_eq (paper_type_vector (map G ns) Prop)
      (named_lam_vec ns (named_paper_eq (paper_type_vector (map G vs) Prop)
        (named_lam_vec vs P) (named_lam_vec vs Q)))
      (named_lam_vec ns (paper_R_named_top G)))"
proof -
  obtain \<rho> U V where ul: "paper_R_in_language \<Sigma> G U \<rho>"
    and vl: "paper_R_in_language \<Sigma> G V \<rho>"
    and uc: "named_fv U = {}" and vc: "named_fv V = {}"
    and closed_identity: "paper_R_classicism_proves \<Sigma> G (named_paper_eq \<rho> U V)"
    and recovery: "paper_R_named_derivable \<Sigma> G {named_paper_eq \<rho> U V}
      (named_paper_eq (paper_type_vector (map G vs) Prop) (named_lam_vec vs P) (named_lam_vec vs Q))"
    by (rule paper_R_classicism_LE_closed_generator[OF rich certificate pl ql inner])
  show ?thesis
  proof (rule paper_R_classicism_A2_local_H[OF rich recovery outer])
    fix B ms
    assume member: "B \<in> {named_paper_eq \<rho> U V}"
      and language: "paper_R_in_language \<Sigma> G B Prop"
      and binders: "list_all paper_R_type (map G ms)"
    have shape: "B = named_paper_eq \<rho> U V" using member by simp
    show "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ms) Prop)
        (named_lam_vec ms B) (named_lam_vec ms (paper_R_named_top G)))"
      by (simp only: shape; rule paper_R_classicism_A2_closed_identity[OF rich ul vl uc vc binders closed_identity])
  qed
qed

end
