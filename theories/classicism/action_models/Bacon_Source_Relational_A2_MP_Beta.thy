theory Bacon_Source_Relational_A2_MP_Beta
  imports Bacon_Source_Relational_Conversion_Congruence Bacon_Source_Relational_Vector_Proof_Syntax
begin

section \<open>Native R conversion inside the explicit Boolean MP context\<close>

lemma paper_R_raw_MP_context:
  fixes P :: "'c paper_named_term"
  assumes pt: "paper_R_has_type G P Prop"
    and first: "paper_R_raw_beta_eta G Prop A A'"
    and second: "paper_R_raw_beta_eta G Prop B B'"
  shows "paper_R_raw_beta_eta G Prop (named_paper_or P (named_paper_and A B))
    (named_paper_or P (named_paper_and A' B'))"
proof -
  have and_type: "paper_R_has_type G (NLogical SAnd :: 'c paper_named_term) (Arr Prop (Arr Prop Prop))"
    using paper_R_has_type.Logical[where G=G and l=SAnd] by simp
  have or_type: "paper_R_has_type G (NLogical SOr :: 'c paper_named_term) (Arr Prop (Arr Prop Prop))"
    using paper_R_has_type.Logical[where G=G and l=SOr] by simp
  have and_head: "paper_R_raw_beta_eta G (Arr Prop Prop)
    (NApp (NLogical SAnd) A) (NApp (NLogical SAnd) A')"
    by (rule paper_R_raw_beta_eta_App_right[OF first and_type])
  have conjunction: "paper_R_raw_beta_eta G Prop
    (NApp (NApp (NLogical SAnd) A) B) (NApp (NApp (NLogical SAnd) A') B')"
    by (rule paper_R_raw_beta_eta_App[OF and_head second])
  have disjunction_head: "paper_R_has_type G (NApp (NLogical SOr) P) (Arr Prop Prop)"
    by (rule paper_R_has_type.App[OF or_type pt])
  show ?thesis unfolding named_paper_or_def named_paper_and_def
    by (rule paper_R_raw_beta_eta_App_right[OF conjunction disjunction_head])
qed

lemma paper_R_MP_vector_body_language:
  assumes pl: "paper_R_in_language \<Sigma> G P Prop"
    and kl: "paper_R_in_language \<Sigma> G K (paper_type_vector (map G ns) Prop)"
    and ll: "paper_R_in_language \<Sigma> G L (paper_type_vector (map G ns) Prop)"
    and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_in_language \<Sigma> G
    (named_lam_vec ns (named_paper_or P (named_paper_and
      (named_app_vec K (map NVar ns)) (named_app_vec L (map NVar ns)))))
    (paper_type_vector (map G ns) Prop)"
proof -
  have arguments: "list_all2 (\<lambda>A \<sigma>. paper_R_in_language \<Sigma> G A \<sigma>) (map NVar ns) (map G ns)"
    by (rule paper_R_named_vector_variables_language[OF binders])
  have ka: "paper_R_in_language \<Sigma> G (named_app_vec K (map NVar ns)) Prop"
    by (rule paper_R_named_app_vec_language[OF arguments kl])
  have la: "paper_R_in_language \<Sigma> G (named_app_vec L (map NVar ns)) Prop"
    by (rule paper_R_named_app_vec_language[OF arguments ll])
  show ?thesis by (rule paper_R_named_lam_vec_prop_language[
    OF paper_R_named_or_language[OF pl paper_R_named_and_language[OF ka la]] binders])
qed

text \<open>
  Expand the two premises Q and Q→P by their self-applying
  abstractions, inside P∨(−∧−), and then under the full prefix.
  These are actual R β chains with every intermediate type checked.
  Source: Appendix A.2's MP calculation, p.66.
  No semantic equation or C abstraction-congruence rule is used.
\<close>

theorem paper_R_named_H_MP_vector_self_identity:
  assumes rich: "paper_R_rich G" and pl: "paper_R_in_language \<Sigma> G P Prop"
    and al: "paper_R_in_language \<Sigma> G A Prop" and bl: "paper_R_in_language \<Sigma> G B Prop"
    and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_eq (paper_type_vector (map G ns) Prop)
      (named_lam_vec ns (named_paper_or P (named_paper_and
        (named_app_vec (named_lam_vec ns A) (map NVar ns))
        (named_app_vec (named_lam_vec ns B) (map NVar ns)))))
      (named_lam_vec ns (named_paper_or P (named_paper_and A B))))"
proof -
  have pt: "paper_R_has_type G P Prop" using pl unfolding paper_R_in_language_def by (rule conjunct1)
  have first: "paper_R_raw_beta_eta G Prop (named_app_vec (named_lam_vec ns A) (map NVar ns)) A"
    by (rule paper_R_named_lam_vec_self_beta[OF al binders]; simp)
  have second: "paper_R_raw_beta_eta G Prop (named_app_vec (named_lam_vec ns B) (map NVar ns)) B"
    by (rule paper_R_named_lam_vec_self_beta[OF bl binders]; simp)
  have body: "paper_R_raw_beta_eta G Prop
    (named_paper_or P (named_paper_and (named_app_vec (named_lam_vec ns A) (map NVar ns))
      (named_app_vec (named_lam_vec ns B) (map NVar ns))))
    (named_paper_or P (named_paper_and A B))"
    by (rule paper_R_raw_MP_context[OF pt first second])
  have conversion: "paper_R_raw_beta_eta G (paper_type_vector (map G ns) Prop)
    (named_lam_vec ns (named_paper_or P (named_paper_and (named_app_vec (named_lam_vec ns A) (map NVar ns))
      (named_app_vec (named_lam_vec ns B) (map NVar ns)))))
    (named_lam_vec ns (named_paper_or P (named_paper_and A B)))"
    by (rule paper_R_raw_beta_eta_lam_vec[OF body binders]; simp)
  have left_language: "paper_R_in_language \<Sigma> G
    (named_lam_vec ns (named_paper_or P (named_paper_and (named_app_vec (named_lam_vec ns A) (map NVar ns))
      (named_app_vec (named_lam_vec ns B) (map NVar ns))))) (paper_type_vector (map G ns) Prop)"
    by (rule paper_R_MP_vector_body_language[OF pl paper_R_named_lam_vec_prop_language[OF al binders]
      paper_R_named_lam_vec_prop_language[OF bl binders] binders])
  have right_language: "paper_R_in_language \<Sigma> G (named_lam_vec ns (named_paper_or P (named_paper_and A B)))
    (paper_type_vector (map G ns) Prop)"
    by (rule paper_R_named_lam_vec_prop_language[OF paper_R_named_or_language[
      OF pl paper_R_named_and_language[OF al bl]] binders])
  show ?thesis by (rule paper_R_named_H_raw_conversion_identity[OF rich conversion left_language right_language])
qed

end
