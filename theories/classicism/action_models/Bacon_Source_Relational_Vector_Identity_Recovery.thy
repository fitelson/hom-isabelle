theory Bacon_Source_Relational_Vector_Identity_Recovery
  imports Bacon_Source_Relational_Vector_Proof_Syntax Bacon_Source_Relational_Application_Congruence
begin

section \<open>Iterate native application congruence over a fixed argument vector\<close>

theorem paper_R_named_identity_app_vec:
  assumes rich: "paper_R_rich G"
    and arguments: "list_all2 (\<lambda>A \<sigma>. paper_R_in_language \<Sigma> G A \<sigma>) As \<sigma>s"
    and left: "paper_R_in_language \<Sigma> G F (paper_type_vector \<sigma>s \<tau>)"
    and right: "paper_R_in_language \<Sigma> G H (paper_type_vector \<sigma>s \<tau>)"
    and equality: "paper_R_named_derivable \<Sigma> G S (named_paper_eq (paper_type_vector \<sigma>s \<tau>) F H)"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> (named_app_vec F As) (named_app_vec H As))"
  using arguments left right equality
proof (induction As arbitrary: \<sigma>s F H)
  case Nil
  have types: "\<sigma>s = []" using Nil.prems(1) by simp
  show ?case using Nil.prems(4) by (simp only: types paper_type_vector.simps named_app_vec.simps)
next
  case (Cons A As)
  obtain \<sigma> \<rho>s where types: "\<sigma>s = \<sigma>#\<rho>s" using Cons.prems(1) by (cases \<sigma>s) auto
  have argument: "paper_R_in_language \<Sigma> G A \<sigma>"
    and rest: "list_all2 (\<lambda>A \<sigma>. paper_R_in_language \<Sigma> G A \<sigma>) As \<rho>s"
    using Cons.prems(1) by (simp_all add: types)
  have fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> (paper_type_vector \<rho>s \<tau>))"
    and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> (paper_type_vector \<rho>s \<tau>))"
    and fh: "paper_R_named_derivable \<Sigma> G S (named_paper_eq (Arr \<sigma> (paper_type_vector \<rho>s \<tau>)) F H)"
    using Cons.prems(2,3,4) by (simp_all only: types paper_type_vector.simps)
  have applied: "paper_R_named_derivable \<Sigma> G S
    (named_paper_eq (paper_type_vector \<rho>s \<tau>) (NApp F A) (NApp H A))"
    by (rule paper_R_named_identity_App_head[OF rich fl hl argument fh])
  show ?case by (simp only: named_app_vec.simps; rule Cons.IH[
    OF rest paper_R_language_App[OF fl argument] paper_R_language_App[OF hl argument] applied])
qed

section \<open>Recover body identity from a longer abstraction identity\<close>

text \<open>
  From (λz⃗.K)=(λz⃗.L), derive K=L by applying both sides
  to z⃗, then using the native R self-β identities.
  The proof requires neither Equivalence nor a general abstraction rule.
  It works for repeated z⃗ too; a later closed-generator construction
  deliberately uses a distinct covering vector.
  Source: the λ/β manipulations in Appendix A.2–A.3, pp.65–67.
\<close>

theorem paper_R_named_identity_from_lam_vec:
  assumes rich: "paper_R_rich G" and left: "paper_R_in_language \<Sigma> G K \<tau>"
    and right: "paper_R_in_language \<Sigma> G L \<tau>"
    and binders: "list_all paper_R_type (map G zs)" and result: "\<tau> \<noteq> Ind"
    and equality: "paper_R_named_derivable \<Sigma> G S
      (named_paper_eq (paper_type_vector (map G zs) \<tau>) (named_lam_vec zs K) (named_lam_vec zs L))"
  shows "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> K L)"
proof -
  let ?K = "named_app_vec (named_lam_vec zs K) (map NVar zs)"
  let ?L = "named_app_vec (named_lam_vec zs L) (map NVar zs)"
  have arguments: "list_all2 (\<lambda>A \<sigma>. paper_R_in_language \<Sigma> G A \<sigma>) (map NVar zs) (map G zs)"
    by (rule paper_R_named_vector_variables_language[OF binders])
  have kl: "paper_R_in_language \<Sigma> G (named_lam_vec zs K) (paper_type_vector (map G zs) \<tau>)"
    by (rule paper_R_named_lam_vec_language[OF left binders result])
  have ll: "paper_R_in_language \<Sigma> G (named_lam_vec zs L) (paper_type_vector (map G zs) \<tau>)"
    by (rule paper_R_named_lam_vec_language[OF right binders result])
  have ka: "paper_R_in_language \<Sigma> G ?K \<tau>" by (rule paper_R_named_app_vec_language[OF arguments kl])
  have la: "paper_R_in_language \<Sigma> G ?L \<tau>" by (rule paper_R_named_app_vec_language[OF arguments ll])
  have applied: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> ?K ?L)"
    by (rule paper_R_named_identity_app_vec[OF rich arguments kl ll equality])
  have k_beta: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> ?K K)"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_lam_vec_self_identity[OF rich left binders result]])
  have l_beta: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> ?L L)"
    by (rule paper_R_named_derivable.Theorem[OF paper_R_named_H_lam_vec_self_identity[OF rich right binders result]])
  have k_reverse: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> K ?K)"
    by (rule paper_R_named_identity_sym[OF rich ka left k_beta])
  have first: "paper_R_named_derivable \<Sigma> G S (named_paper_eq \<tau> K ?L)"
    by (rule paper_R_named_identity_trans[OF rich left ka la k_reverse applied])
  show ?thesis by (rule paper_R_named_identity_trans[OF rich left la right first l_beta])
qed

end
