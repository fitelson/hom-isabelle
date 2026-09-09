theory Bacon_Source_Relational_Modalized_Functionality
  imports Bacon_Source_Relational_Functionality_Saturation
    Bacon_Source_Relational_Classicism_Box_Monotonicity
    Bacon_Source_Relational_Intensionality_Proof
    Bacon_Source_Relational_Fresh_Typed_Vectors Bacon_Source_Relational_Vector_Eta_Recovery
begin

section \<open>Native C proves the R instances of Modalized Functionality\<close>

theorem paper_R_classicism_modalized_functionality:
  assumes rich: "paper_R_rich G"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and variable: "G z = \<sigma>"
    and fresh_F: "z \<notin> named_fv F" and fresh_H: "z \<notin> named_fv H"
  shows "paper_R_classicism_proves \<Sigma> G
    (named_paper_imp G
      (paper_R_named_box G
        (named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp F (NVar z)) (NApp H (NVar z))))))
      (named_paper_eq (Arr \<sigma> \<tau>) F H))"
proof -
  have arrow_R: "paper_R_type (Arr \<sigma> \<tau>)" by (rule paper_R_language_result_type[OF fl])
  have sr: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF arrow_R])
  have relational: "paper_R_relational \<tau>" by (rule paper_R_arrow_codomain[OF arrow_R])
  obtain \<tau>s where types: "list_all paper_R_type \<tau>s"
    and decomposition: "\<tau> = paper_type_vector \<tau>s Prop"
    using paper_R_relational_decomposition[OF relational] by blast
  have finite: "finite (named_fv F \<union> named_fv H \<union> {z})" by (simp add: named_fv_finite)
  obtain us where distinct: "distinct us" and typed_names: "map G us = \<tau>s"
    and avoids: "set us \<inter> (named_fv F \<union> named_fv H \<union> {z}) = {}"
    by (rule paper_R_fresh_typed_vector[OF rich types finite])
  have tail_types: "list_all paper_R_type (map G us)" by (simp only: typed_names; rule types)
  have tail_shape: "\<tau> = paper_type_vector (map G us) Prop"
    by (simp only: typed_names; rule decomposition)
  have tail_avoid: "set us \<inter> (named_fv F \<union> named_fv H) = {}" using avoids by blast
  have zr: "paper_R_type (G z)" by (simp only: variable; rule sr)
  have binders: "list_all paper_R_type (map G (z#us))" using zr tail_types by simp
  have whole_distinct: "distinct (z#us)" using distinct avoids by auto
  have whole_fresh_F: "set (z#us) \<inter> named_fv F = {}" using fresh_F avoids by auto
  have whole_fresh_H: "set (z#us) \<inter> named_fv H = {}" using fresh_H avoids by auto
  let ?\<theta> = "paper_type_vector (map G (z#us)) Prop"
  have whole_shape: "?\<theta> = Arr \<sigma> \<tau>"
    by (simp only: list.map paper_type_vector.simps variable tail_shape[symmetric])
  have fwhole: "paper_R_in_language \<Sigma> G F ?\<theta>" by (simp only: whole_shape; rule fl)
  have hwhole: "paper_R_in_language \<Sigma> G H ?\<theta>" by (simp only: whole_shape; rule hl)
  have zv: "paper_R_in_language \<Sigma> G (NVar z) \<sigma>"
    by (rule paper_R_language_Var[where \<Sigma>=\<Sigma> and G=G and n=z, OF variable sr])
  have fz: "paper_R_in_language \<Sigma> G (NApp F (NVar z)) \<tau>" by (rule paper_R_language_App[OF fl zv])
  have hz: "paper_R_in_language \<Sigma> G (NApp H (NVar z)) \<tau>" by (rule paper_R_language_App[OF hl zv])
  have ftail: "paper_R_in_language \<Sigma> G (NApp F (NVar z)) (paper_type_vector (map G us) Prop)"
    by (simp only: tail_shape[symmetric]; rule fz)
  have htail: "paper_R_in_language \<Sigma> G (NApp H (NVar z)) (paper_type_vector (map G us) Prop)"
    by (simp only: tail_shape[symmetric]; rule hz)
  have arguments: "list_all2 (\<lambda>A \<rho>. paper_R_in_language \<Sigma> G A \<rho>) (map NVar us) (map G us)"
    by (rule paper_R_named_vector_variables_language[OF tail_types])
  let ?P = "named_app_vec (NApp F (NVar z)) (map NVar us)"
  let ?Q = "named_app_vec (NApp H (NVar z)) (map NVar us)"
  let ?A = "named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp F (NVar z)) (NApp H (NVar z))))"
  let ?B = "paper_R_all_vec G (z#us) (named_paper_iff G ?P ?Q)"
  let ?LF = "named_lam_vec (z#us) ?P"
  let ?LH = "named_lam_vec (z#us) ?Q"
  have pl: "paper_R_in_language \<Sigma> G ?P Prop" by (rule paper_R_named_app_vec_language[OF arguments ftail])
  have ql: "paper_R_in_language \<Sigma> G ?Q Prop" by (rule paper_R_named_app_vec_language[OF arguments htail])
  have al: "paper_R_in_language \<Sigma> G ?A Prop"
    by (rule paper_R_named_all_binder_language[OF paper_R_named_identity_language[OF fz hz] variable sr])
  have bl: "paper_R_in_language \<Sigma> G ?B Prop"
    by (rule paper_R_all_vec_language[OF paper_R_named_paper_iff_language[OF rich pl ql] binders])
  have lf: "paper_R_in_language \<Sigma> G ?LF ?\<theta>" by (rule paper_R_named_lam_vec_prop_language[OF pl binders])
  have lh: "paper_R_in_language \<Sigma> G ?LH ?\<theta>" by (rule paper_R_named_lam_vec_prop_language[OF ql binders])
  have box_al: "paper_R_in_language \<Sigma> G (paper_R_named_box G ?A) Prop"
    by (rule paper_R_named_box_language[OF rich al])
  have box_bl: "paper_R_in_language \<Sigma> G (paper_R_named_box G ?B) Prop"
    by (rule paper_R_named_box_language[OF rich bl])
  have identity_language: "paper_R_in_language \<Sigma> G (named_paper_eq ?\<theta> ?LF ?LH) Prop"
    by (rule paper_R_named_identity_language[OF lf lh])

  text \<open>The certificate is necessitated in original C before any local assumption.\<close>
  have certificate: "paper_R_named_H \<Sigma> G (named_paper_imp G ?A ?B)"
    by (rule paper_R_named_H_functionality_saturation[
      OF rich fl hl variable tail_shape tail_types tail_avoid])
  have boxed: "paper_R_classicism_proves \<Sigma> G
      (named_paper_imp G (paper_R_named_box G ?A) (paper_R_named_box G ?B))"
    by (rule paper_R_classicism_box_monotone[OF rich al bl paper_R_classicism_proves.H[OF certificate]])
  have intensionality: "paper_R_classicism_proves \<Sigma> G
      (named_paper_imp G (paper_R_named_box G ?B) (named_paper_eq ?\<theta> ?LF ?LH))"
    by (rule paper_R_classicism_abstraction_intensionality[OF rich pl ql binders])
  have f_eta: "paper_R_named_H \<Sigma> G (named_paper_eq ?\<theta> ?LF F)"
    using paper_R_named_H_eta_vector_identity[OF rich fwhole binders whole_distinct whole_fresh_F]
    by (simp only: list.map named_app_vec.simps)
  have h_eta: "paper_R_named_H \<Sigma> G (named_paper_eq ?\<theta> ?LH H)"
    using paper_R_named_H_eta_vector_identity[OF rich hwhole binders whole_distinct whole_fresh_H]
    by (simp only: list.map named_app_vec.simps)

  let ?T = "{C. paper_R_classicism_proves \<Sigma> G C}"
  let ?S = "insert (paper_R_named_box G ?A) ?T"
  have include_C: "paper_R_named_derivable \<Sigma> G ?S C"
    if derivation: "paper_R_classicism_proves \<Sigma> G C" for C
  proof -
    have member: "C \<in> ?S" using derivation by simp
    show ?thesis by (rule paper_R_named_derivable.Assumption[
      OF member paper_R_classicism_proves_language[OF derivation]])
  qed
  have assumed: "paper_R_named_derivable \<Sigma> G ?S (paper_R_named_box G ?A)"
    by (rule paper_R_named_derivable.Assumption[OF insertI1 box_al])
  have next_box: "paper_R_named_derivable \<Sigma> G ?S (paper_R_named_box G ?B)"
    by (rule paper_R_named_derivable.MP[OF assumed include_C[OF boxed] box_bl])
  have abstracts: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<theta> ?LF ?LH)"
    by (rule paper_R_named_derivable.MP[OF next_box include_C[OF intensionality] identity_language])
  have f_to_lf: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<theta> F ?LF)"
    by (rule paper_R_named_identity_sym[OF rich lf fwhole paper_R_named_derivable.Theorem[OF f_eta]])
  have middle: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<theta> F ?LH)"
    by (rule paper_R_named_identity_trans[OF rich fwhole lf lh f_to_lf abstracts])
  have result: "paper_R_named_derivable \<Sigma> G ?S (named_paper_eq ?\<theta> F H)"
    by (rule paper_R_named_identity_trans[OF rich fwhole lh hwhole middle
      paper_R_named_derivable.Theorem[OF h_eta]])
  have discharged: "paper_R_named_derivable \<Sigma> G ?T
      (named_paper_imp G (paper_R_named_box G ?A) (named_paper_eq ?\<theta> F H))"
    by (rule paper_R_named_derivable_deduction[OF rich box_al result])
  have member: "named_paper_imp G (paper_R_named_box G ?A) (named_paper_eq ?\<theta> F H) \<in> ?T"
    by (rule paper_R_H_theory_local_consequences[
      OF paper_R_classicism_is_H_theory discharged subset_refl])
  show ?thesis using member by (simp only: mem_Collect_eq whole_shape)
qed

text \<open>
  This is □∀z(Fz=τHz)→F=σ→τH, with the displayed z fresh
  in both heads. R typing makes τ a finite relational tail ending in t;
  no F-type ending in e is included. The tail may be empty. Distinct
  fresh test variables are constructed for η recovery, not assumed
  as an enumeration of a domain.

  The proof follows p.18 n.22: native H saturation, original-theory
  Necessitation and K, the proved p.17 Intensionality theorem, and
  typed η recovery. No local ζ, Functionality axiom, semantic model
  or completeness theorem is used.
\<close>

end
