theory Bacon_Source_Relational_Classicism_Identity_Consequences
  imports Bacon_Source_Relational_Classicism_A2_H
begin

section \<open>Native H identity consequences in the p.12 C presentation\<close>

lemma paper_R_classicism_identity_sym:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A \<tau>"
    and bl: "paper_R_in_language \<Sigma> G B \<tau>"
    and equality: "paper_R_classicism_proves \<Sigma> G (named_paper_eq \<tau> A B)"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_eq \<tau> B A)"
proof -
  let ?S = "{P. paper_R_classicism_proves \<Sigma> G P}"
  have member: "named_paper_eq \<tau> A B \<in> ?S" using equality by simp
  have premise: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq \<tau> A B)"
    by (rule paper_R_named_derivable.Assumption[OF member paper_R_named_identity_language[OF al bl]])
  have result: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq \<tau> B A)"
    by (rule paper_R_named_identity_sym[OF rich al bl premise])
  show ?thesis by (rule paper_R_local_H_in_classicism[OF result]; simp)
qed

lemma paper_R_classicism_identity_trans:
  assumes rich: "paper_R_rich G" and al: "paper_R_in_language \<Sigma> G A \<tau>"
    and bl: "paper_R_in_language \<Sigma> G B \<tau>" and cl: "paper_R_in_language \<Sigma> G C \<tau>"
    and first: "paper_R_classicism_proves \<Sigma> G (named_paper_eq \<tau> A B)"
    and second: "paper_R_classicism_proves \<Sigma> G (named_paper_eq \<tau> B C)"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_eq \<tau> A C)"
proof -
  let ?S = "{P. paper_R_classicism_proves \<Sigma> G P}"
  have ab: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq \<tau> A B)"
    by (rule paper_R_named_derivable.Assumption; (use first in simp | rule paper_R_named_identity_language[OF al bl]))
  have bc: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq \<tau> B C)"
    by (rule paper_R_named_derivable.Assumption; (use second in simp | rule paper_R_named_identity_language[OF bl cl]))
  have result: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq \<tau> A C)"
    by (rule paper_R_named_identity_trans[OF rich al bl cl ab bc])
  show ?thesis by (rule paper_R_local_H_in_classicism[OF result]; simp)
qed

text \<open>
  An H-certified biconditional P↔Q yields (λv⃗.P)=(λv⃗.Q)
  by Logical Equivalence. Thus the abstraction-to-truth property transfers
  from P to Q by native identity symmetry and transitivity. This uses
  only the H-certified schema, not the general recursive Equivalence rule.
  Source: p.12 and the transformations in Appendix A.2, pp.65–67.
\<close>

theorem paper_R_classicism_A2_H_equivalent:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and certificate: "paper_R_named_H \<Sigma> G (named_paper_iff G P Q)"
    and binders: "list_all paper_R_type (map G ns)"
    and truth: "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
      (named_lam_vec ns P) (named_lam_vec ns (paper_R_named_top G)))"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns Q) (named_lam_vec ns (paper_R_named_top G)))"
proof -
  have lp: "paper_R_in_language \<Sigma> G (named_lam_vec ns P) (paper_type_vector (map G ns) Prop)"
    by (rule paper_R_named_lam_vec_prop_language[OF pl binders])
  have lq: "paper_R_in_language \<Sigma> G (named_lam_vec ns Q) (paper_type_vector (map G ns) Prop)"
    by (rule paper_R_named_lam_vec_prop_language[OF ql binders])
  have lt: "paper_R_in_language \<Sigma> G (named_lam_vec ns (paper_R_named_top G)) (paper_type_vector (map G ns) Prop)"
    by (rule paper_R_named_lam_vec_prop_language[OF paper_R_named_top_language[OF rich] binders])
  have same: "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
      (named_lam_vec ns P) (named_lam_vec ns Q))"
    by (rule paper_R_classicism_proves.Logical_Equivalence[OF certificate pl ql binders])
  have reverse: "paper_R_classicism_proves \<Sigma> G (named_paper_eq (paper_type_vector (map G ns) Prop)
      (named_lam_vec ns Q) (named_lam_vec ns P))"
    by (rule paper_R_classicism_identity_sym[OF rich lp lq same])
  show ?thesis by (rule paper_R_classicism_identity_trans[OF rich lq lp lt reverse truth])
qed

end
