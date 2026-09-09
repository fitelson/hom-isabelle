theory Bacon_Source_Relational_Vector_Eta_Recovery
  imports Bacon_Source_Relational_Vector_Proof_Syntax Bacon_Source_Relational_Conversion_Congruence
begin

section \<open>Fresh distinct argument vectors permit actual native R η recovery\<close>

text \<open>
  λu⃗.Fu⃗ ≡η F when u⃗ is distinct, has the displayed
  argument types, and is disjoint from FV(F). At the first binder,
  recover the tail by induction; its freshness for F u follows
  from freshness for F and the distinctness of the whole vector.
  Then contract the outer η redex.
  Source: p.14–15, with the relational-type decomposition in n.17.
  All intermediate terms remain R-typed. This is not an F-conversion
  shortcut or a general object-identity abstraction rule.
\<close>

theorem paper_R_named_eta_vector:
  assumes head: "paper_R_has_type G F (paper_type_vector (map G us) Prop)"
    and binders: "list_all paper_R_type (map G us)"
    and distinct: "distinct us" and fresh: "set us \<inter> named_fv F = {}"
  shows "paper_R_raw_beta_eta G (paper_type_vector (map G us) Prop)
    (named_lam_vec us (named_app_vec F (map NVar us))) F"
  using head binders distinct fresh
proof (induction us arbitrary: F)
  case Nil
  have typed: "paper_R_has_type G F Prop" using Nil.prems(1) by simp
  show ?case by (simp only: named_lam_vec.simps named_app_vec.simps list.map paper_type_vector.simps;
    rule paper_R_raw_beta_eta.Refl[OF typed])
next
  case (Cons u us)
  let ?\<tau> = "paper_type_vector (map G us) Prop"
  have ft: "paper_R_has_type G F (Arr (G u) ?\<tau>)"
    using Cons.prems(1) by (simp only: list.map paper_type_vector.simps)
  have ur: "paper_R_type (G u)" and tail: "list_all paper_R_type (map G us)" using Cons.prems(2) by simp_all
  have ut: "paper_R_has_type G (NVar u) (G u)" by (rule paper_R_has_type.Var[where G=G and n=u, OF ur])
  have applied: "paper_R_has_type G (NApp F (NVar u)) ?\<tau>" by (rule paper_R_has_type.App[OF ft ut])
  have tail_distinct: "distinct us" using Cons.prems(3) by simp
  have tail_fresh: "set us \<inter> named_fv (NApp F (NVar u)) = {}"
    using Cons.prems(3,4) by auto
  have outer_fresh: "u \<notin> named_fv F" using Cons.prems(4) by auto
  have inner: "paper_R_raw_beta_eta G ?\<tau>
    (named_lam_vec us (named_app_vec (NApp F (NVar u)) (map NVar us))) (NApp F (NVar u))"
    by (rule Cons.IH[OF applied tail tail_distinct tail_fresh])
  have result: "?\<tau> \<noteq> Ind" by simp
  have lifted: "paper_R_raw_beta_eta G (Arr (G u) ?\<tau>)
    (NLam u (named_lam_vec us (named_app_vec (NApp F (NVar u)) (map NVar us))))
    (NLam u (NApp F (NVar u)))"
    by (rule paper_R_raw_beta_eta_Lam[OF inner ur result])
  have middle_type: "paper_R_has_type G (NLam u (NApp F (NVar u))) (Arr (G u) ?\<tau>)"
    by (rule paper_R_has_type.Lam[OF applied ur result])
  have contraction: "named_eta_contract (NLam u (NApp F (NVar u))) F"
    by (rule named_eta_contract.eta[OF outer_fresh])
  have step: "named_compatible_step named_eta_contract (NLam u (NApp F (NVar u))) F"
    by (rule named_compatible_step.root[where R=named_eta_contract and M="NLam u (NApp F (NVar u))" and N=F, OF contraction])
  have eta: "paper_R_raw_beta_eta G (Arr (G u) ?\<tau>) (NLam u (NApp F (NVar u))) F"
    by (rule paper_R_raw_beta_eta.Eta[OF middle_type ft step])
  show ?case by (simp only: named_lam_vec.simps named_app_vec.simps list.map paper_type_vector.simps;
    rule paper_R_raw_beta_eta.Trans[OF lifted eta])
qed

theorem paper_R_named_H_eta_vector_identity:
  assumes rich: "paper_R_rich G"
    and language: "paper_R_in_language \<Sigma> G F (paper_type_vector (map G us) Prop)"
    and binders: "list_all paper_R_type (map G us)"
    and distinct: "distinct us" and fresh: "set us \<inter> named_fv F = {}"
  shows "paper_R_named_H \<Sigma> G (named_paper_eq (paper_type_vector (map G us) Prop)
    (named_lam_vec us (named_app_vec F (map NVar us))) F)"
proof -
  have typed: "paper_R_has_type G F (paper_type_vector (map G us) Prop)"
    using language unfolding paper_R_in_language_def by (rule conjunct1)
  have conversion: "paper_R_raw_beta_eta G (paper_type_vector (map G us) Prop)
    (named_lam_vec us (named_app_vec F (map NVar us))) F"
    by (rule paper_R_named_eta_vector[OF typed binders distinct fresh])
  have body: "paper_R_in_language \<Sigma> G (named_app_vec F (map NVar us)) Prop"
    by (rule paper_R_named_app_vec_language[OF paper_R_named_vector_variables_language[OF binders] language])
  have left: "paper_R_in_language \<Sigma> G (named_lam_vec us (named_app_vec F (map NVar us)))
    (paper_type_vector (map G us) Prop)"
    by (rule paper_R_named_lam_vec_prop_language[OF body binders])
  show ?thesis by (rule paper_R_named_H_raw_conversion_identity[OF rich conversion left language])
qed

end
