theory Bacon_Source_Relational_Classicism_Zeta
  imports Bacon_Source_Relational_Fresh_Typed_Vectors Bacon_Source_Relational_Identity_To_Biconditional
    Bacon_Source_Relational_Vector_Eta_Recovery
begin

section \<open>Source-defined C is closed under the fresh-variable ζ rule\<close>

text \<open>
  From ⊢C Fx=τHx infer ⊢C F=σ→τH when x:σ is free
  in neither head. In R, τ is relational, so write τ=τ⃗→t.
  Choose distinct fresh variables u⃗ of types τ⃗, avoiding x.
  Native application congruence gives Fx u⃗=Hx u⃗ at t;
  native identity-to-biconditional reasoning and A.3 give equality
  of their x,u⃗ abstractions. The proved raw R η recovery returns
  F and H. Source: pp.14–16, especially the type decomposition
  and fresh-vector argument in p.15 n.17.

  The relational tail may be empty. Distinctness prevents a diagonal
  test, and all intermediate types remain in R. Neither general
  λ-congruence, Functionality, H identity reflection, F conversion,
  a semantic model nor a completeness theorem is assumed.
\<close>

theorem paper_R_classicism_zeta:
  assumes rich: "paper_R_rich G"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and variable: "G x = \<sigma>" and fresh_F: "x \<notin> named_fv F" and fresh_H: "x \<notin> named_fv H"
    and premise: "paper_R_classicism_proves \<Sigma> G (named_paper_eq \<tau> (NApp F (NVar x)) (NApp H (NVar x)))"
  shows "paper_R_classicism_proves \<Sigma> G (named_paper_eq (Arr \<sigma> \<tau>) F H)"
proof -
  have arrow_type: "paper_R_type (Arr \<sigma> \<tau>)" by (rule paper_R_language_result_type[OF fl])
  have sr: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF arrow_type])
  have relational: "paper_R_relational \<tau>" by (rule paper_R_arrow_codomain[OF arrow_type])
  obtain \<tau>s where types: "list_all paper_R_type \<tau>s" and decomposition: "\<tau> = paper_type_vector \<tau>s Prop"
    using paper_R_relational_decomposition[OF relational] by blast
  have finite: "finite (named_fv F \<union> named_fv H \<union> {x})" by (simp add: named_fv_finite)
  obtain us where distinct: "distinct us" and typed_names: "map G us = \<tau>s"
    and avoids: "set us \<inter> (named_fv F \<union> named_fv H \<union> {x}) = {}"
    by (rule paper_R_fresh_typed_vector[OF rich types finite])
  have tail_types: "list_all paper_R_type (map G us)" by (simp only: typed_names; rule types)
  have tail_shape: "paper_type_vector (map G us) Prop = \<tau>"
    by (simp only: typed_names; rule decomposition[symmetric])
  have xr: "paper_R_type (G x)" by (simp only: variable; rule sr)
  have whole_types: "list_all paper_R_type (map G (x#us))" using xr tail_types by simp
  have whole_distinct: "distinct (x#us)" using distinct avoids by auto
  have whole_fresh_F: "set (x#us) \<inter> named_fv F = {}" using fresh_F avoids by auto
  have whole_fresh_H: "set (x#us) \<inter> named_fv H = {}" using fresh_H avoids by auto
  let ?\<theta> = "paper_type_vector (map G (x#us)) Prop"
  have whole_shape: "?\<theta> = Arr \<sigma> \<tau>" by (simp only: list.map paper_type_vector.simps variable tail_shape)
  have fwhole: "paper_R_in_language \<Sigma> G F ?\<theta>" by (simp only: whole_shape; rule fl)
  have hwhole: "paper_R_in_language \<Sigma> G H ?\<theta>" by (simp only: whole_shape; rule hl)
  have vx: "paper_R_in_language \<Sigma> G (NVar x) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=x, OF variable sr])
  have fa: "paper_R_in_language \<Sigma> G (NApp F (NVar x)) \<tau>" by (rule paper_R_language_App[OF fl vx])
  have ha: "paper_R_in_language \<Sigma> G (NApp H (NVar x)) \<tau>" by (rule paper_R_language_App[OF hl vx])
  have f_tail: "paper_R_in_language \<Sigma> G (NApp F (NVar x)) (paper_type_vector (map G us) Prop)"
    by (simp only: tail_shape; rule fa)
  have h_tail: "paper_R_in_language \<Sigma> G (NApp H (NVar x)) (paper_type_vector (map G us) Prop)"
    by (simp only: tail_shape; rule ha)
  have arguments: "list_all2 (\<lambda>A \<rho>. paper_R_in_language \<Sigma> G A \<rho>) (map NVar us) (map G us)"
    by (rule paper_R_named_vector_variables_language[OF tail_types])
  let ?P = "named_app_vec (NApp F (NVar x)) (map NVar us)"
  let ?Q = "named_app_vec (NApp H (NVar x)) (map NVar us)"
  have pl: "paper_R_in_language \<Sigma> G ?P Prop" by (rule paper_R_named_app_vec_language[OF arguments f_tail])
  have ql: "paper_R_in_language \<Sigma> G ?Q Prop" by (rule paper_R_named_app_vec_language[OF arguments h_tail])
  let ?S = "{A. paper_R_classicism_proves \<Sigma> G A}"
  have member: "named_paper_eq \<tau> (NApp F (NVar x)) (NApp H (NVar x)) \<in> ?S" using premise by simp
  have local: "paper_R_named_derivable \<Sigma> G ?S
    (named_paper_eq \<tau> (NApp F (NVar x)) (NApp H (NVar x)))"
    by (rule paper_R_named_derivable.Assumption[OF member paper_R_named_identity_language[OF fa ha]])
  have tail_identity: "paper_R_named_derivable \<Sigma> G ?S
    (named_paper_eq (paper_type_vector (map G us) Prop) (NApp F (NVar x)) (NApp H (NVar x)))"
    by (simp only: tail_shape; rule local)
  have saturated_local: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq Prop ?P ?Q)"
    by (rule paper_R_named_identity_app_vec[OF rich arguments f_tail h_tail tail_identity])
  have saturated: "paper_R_classicism_proves \<Sigma> G (named_paper_eq Prop ?P ?Q)"
    by (rule paper_R_local_H_in_classicism[OF saturated_local]; simp)
  have biconditional: "paper_R_classicism_proves \<Sigma> G (named_paper_iff G ?P ?Q)"
    by (rule paper_R_classicism_identity_iff[OF rich pl ql saturated])
  let ?LF = "named_lam_vec (x#us) ?P"
  let ?LH = "named_lam_vec (x#us) ?Q"
  have abstractions: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<theta> ?LF ?LH)"
    by (rule paper_R_classicism_A3[OF rich biconditional pl ql whole_types])
  have flambda: "paper_R_in_language \<Sigma> G ?LF ?\<theta>"
    by (rule paper_R_named_lam_vec_prop_language[OF pl whole_types])
  have hlambda: "paper_R_in_language \<Sigma> G ?LH ?\<theta>"
    by (rule paper_R_named_lam_vec_prop_language[OF ql whole_types])
  have f_eta_H: "paper_R_named_H \<Sigma> G (named_paper_eq ?\<theta> ?LF F)"
    using paper_R_named_H_eta_vector_identity[OF rich fwhole whole_types whole_distinct whole_fresh_F]
    by (simp only: list.map named_app_vec.simps)
  have h_eta_H: "paper_R_named_H \<Sigma> G (named_paper_eq ?\<theta> ?LH H)"
    using paper_R_named_H_eta_vector_identity[OF rich hwhole whole_types whole_distinct whole_fresh_H]
    by (simp only: list.map named_app_vec.simps)
  have f_eta: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<theta> ?LF F)"
    by (rule paper_R_classicism_proves.H[OF f_eta_H])
  have h_eta: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<theta> ?LH H)"
    by (rule paper_R_classicism_proves.H[OF h_eta_H])
  have f_reverse: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<theta> F ?LF)"
    by (rule paper_R_classicism_identity_sym[OF rich flambda fwhole f_eta])
  have intermediate: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<theta> F ?LH)"
    by (rule paper_R_classicism_identity_trans[OF rich fwhole flambda hlambda f_reverse abstractions])
  have final_identity: "paper_R_classicism_proves \<Sigma> G (named_paper_eq ?\<theta> F H)"
    by (rule paper_R_classicism_identity_trans[OF rich fwhole hlambda hwhole intermediate h_eta])
  show ?thesis using final_identity by (simp only: whole_shape)
qed

end
