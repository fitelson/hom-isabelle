theory Bacon_Source_Relational_Functionality_Saturation
  imports Bacon_Source_Relational_Universal_Consequent
    Bacon_Source_Relational_Vector_Identity_Recovery
    Bacon_Source_Relational_Identity_To_Biconditional
begin

section \<open>Native H turns pointwise identity into a saturated universal biconditional\<close>

theorem paper_R_named_H_functionality_saturation:
  assumes rich: "paper_R_rich G"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and variable: "G z = \<sigma>"
    and tail_shape: "\<tau> = paper_type_vector (map G us) Prop"
    and tail_types: "list_all paper_R_type (map G us)"
    and avoid: "set us \<inter> (named_fv F \<union> named_fv H) = {}"
  shows "paper_R_named_H \<Sigma> G
    (named_paper_imp G
      (named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp F (NVar z)) (NApp H (NVar z)))))
      (paper_R_all_vec G (z#us)
        (named_paper_iff G
          (named_app_vec (NApp F (NVar z)) (map NVar us))
          (named_app_vec (NApp H (NVar z)) (map NVar us)))))"
proof -
  let ?Fz = "NApp F (NVar z)"
  let ?Hz = "NApp H (NVar z)"
  let ?E = "named_paper_eq \<tau> ?Fz ?Hz"
  let ?A = "named_paper_all \<sigma> (NLam z ?E)"
  let ?P = "named_app_vec ?Fz (map NVar us)"
  let ?Q = "named_app_vec ?Hz (map NVar us)"
  let ?I = "named_paper_iff G ?P ?Q"
  have arrow_R: "paper_R_type (Arr \<sigma> \<tau>)" by (rule paper_R_language_result_type[OF fl])
  have sr: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF arrow_R])
  have zr: "paper_R_type (G z)" by (simp only: variable; rule sr)
  have zv: "paper_R_in_language \<Sigma> G (NVar z) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=z, OF variable sr])
  have fz: "paper_R_in_language \<Sigma> G ?Fz \<tau>" by (rule paper_R_language_App[OF fl zv])
  have hz: "paper_R_in_language \<Sigma> G ?Hz \<tau>" by (rule paper_R_language_App[OF hl zv])
  have f_tail: "paper_R_in_language \<Sigma> G ?Fz (paper_type_vector (map G us) Prop)"
    by (simp only: tail_shape[symmetric]; rule fz)
  have h_tail: "paper_R_in_language \<Sigma> G ?Hz (paper_type_vector (map G us) Prop)"
    by (simp only: tail_shape[symmetric]; rule hz)
  have arguments: "list_all2 (\<lambda>B \<rho>. paper_R_in_language \<Sigma> G B \<rho>) (map NVar us) (map G us)"
    by (rule paper_R_named_vector_variables_language[OF tail_types])
  have pl: "paper_R_in_language \<Sigma> G ?P Prop" by (rule paper_R_named_app_vec_language[OF arguments f_tail])
  have ql: "paper_R_in_language \<Sigma> G ?Q Prop" by (rule paper_R_named_app_vec_language[OF arguments h_tail])
  have il: "paper_R_in_language \<Sigma> G ?I Prop" by (rule paper_R_named_paper_iff_language[OF rich pl ql])
  have el: "paper_R_in_language \<Sigma> G ?E Prop" by (rule paper_R_named_identity_language[OF fz hz])
  have al: "paper_R_in_language \<Sigma> G ?A Prop" by (rule paper_R_named_all_binder_language[OF el variable sr])
  have ui: "paper_R_named_H \<Sigma> G (named_paper_imp G ?A ?E)"
    by (rule paper_R_named_H_all_binder_instance[OF rich el variable sr])
  have assumed: "paper_R_named_derivable \<Sigma> G {?A} ?A"
    by (rule paper_R_named_derivable.Assumption[OF insertI1 al])
  have equality: "paper_R_named_derivable \<Sigma> G {?A} ?E"
    by (rule paper_R_named_derivable.MP[OF assumed paper_R_named_derivable.Theorem[OF ui] el])
  have tail_equality: "paper_R_named_derivable \<Sigma> G {?A}
      (named_paper_eq (paper_type_vector (map G us) Prop) ?Fz ?Hz)"
    by (simp only: tail_shape[symmetric]; rule equality)
  have saturated: "paper_R_named_derivable \<Sigma> G {?A} (named_paper_eq Prop ?P ?Q)"
    by (rule paper_R_named_identity_app_vec[OF rich arguments f_tail h_tail tail_equality])
  have equivalence: "paper_R_named_derivable \<Sigma> G {?A} ?I"
    by (rule paper_R_named_derivable_identity_iff[OF rich pl ql saturated])
  have discharged: "paper_R_named_derivable \<Sigma> G {} (named_paper_imp G ?A ?I)"
    by (rule paper_R_named_derivable_deduction[OF rich al equivalence])
  have certificate: "paper_R_named_H \<Sigma> G (named_paper_imp G ?A ?I)"
    by (rule iffD1[OF paper_R_named_derivable_empty_iff discharged])
  have binders: "list_all paper_R_type (map G (z#us))" using zr tail_types by simp
  have fresh: "set (z#us) \<inter> named_fv ?A = {}"
    using avoid by (simp only: named_paper_primitive_fv named_fv.simps list.set; blast)
  show ?thesis by (rule paper_R_named_H_imp_all_vec[OF rich al il binders fresh certificate])
qed

text \<open>
  The tail may be empty. The local identity assumption is used only
  for native application congruence and propositional identity
  elimination, then discharged. Gen is applied afterwards to an
  actual H implication with a fresh antecedent. Neither ζ nor
  Functionality nor a semantic model occurs. Source: p.18 n.22.
\<close>

end
