theory Bacon_Finite_Calibration_BBK_Inhabitation
  imports Bacon_Classicism.Bacon_Finite_CEV_Model
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Local_Quantifiers
    Bacon_Source_Model_Development.Bacon_Source_BBK_Model_Existence
    Bacon_Source_Model_Development.Bacon_Source_Named_Tagged_Model
begin

section \<open>Nonvacuity from the independently constructed finite calibration\<close>

text \<open>
  The concrete finite-table interpretation falsifies ⊥. Its H soundness
  component therefore proves that H does not derive ⊥.
  Transfer this metatheoretic certificate to the parametric H calculus;
  its canonical existence theorem then supplies a current BBK model.

  Source role: nonvacuity calibration for the represented H and the model
  classes associated with Bacon–Dorr Definition 3.1 and Theorem 3.2,
  pp.43–45. The older finite-table model is an extensional calibration,
  not a named-model isomorphism or a non-extensional C construction.

  Status. This downstream bridge leaves the standalone H development
  unchanged. It does not derive an H object-language theorem using stronger
  object-language principles or invoke a C/CE/CEV judgment, and it does not relabel
  Finite as a pbbk_model. Instead it proves
  consistency from a previously checked counterinterpretation, then uses
  the separately checked canonical model and source/name transports.
  Constant names and signatures remain arbitrary. Full F is represented.
\<close>

lemma H_not_false_from_finite_calibration:
  "\<not> H_proves [] ObjFalse"
proof
  assume bad: "H_proves [] ObjFalse"
  have valid: "Finite.valid_in_context [] ObjFalse"
    by (rule Finite.H_soundness[OF bad])
  have env: "Finite.env_typed [] (\<lambda>_. FDInd)"
    unfolding Finite.env_typed_def by (simp add: lookup_def)
  have impossible: "finite_holds (Finite.eval (\<lambda>_. FDInd) ObjFalse)"
    by (rule Finite.valid_holds[OF valid env])
  show False using impossible by (simp add: ObjFalse_def ObjTrue_def)
qed

lemma pH_string_not_false_from_finite_calibration:
  fixes \<Sigma> :: "string psignature"
  shows "\<not> pH_proves \<Sigma> [] PObjFalse"
proof
  assume bad: "pH_proves \<Sigma> [] PObjFalse"
  have translated: "H_proves [] (pterm_to_oterm PObjFalse)"
    by (rule pH_string_proves_to_H[OF bad])
  have old_false: "H_proves [] ObjFalse"
    using translated by (simp add: PObjFalse_def PObjTrue_def ObjFalse_def ObjTrue_def)
  show False by (rule notE[OF H_not_false_from_finite_calibration old_false])
qed

lemma pH_string_empty_consistent_from_finite_calibration:
  fixes \<Sigma> :: "string psignature"
  shows "pH_consistent \<Sigma> [] {}"
proof (unfold pH_consistent_def, rule notI)
  assume bad: "pH_set_derivable \<Sigma> [] {} PObjFalse"
  obtain \<Delta> where subset: "set \<Delta> \<subseteq> {}" and local_false: "pH_derivable \<Sigma> [] \<Delta> PObjFalse"
    using bad unfolding pH_set_derivable_def by (elim exE conjE)
  have empty: "\<Delta> = []" using subset by simp
  have local_empty: "pH_derivable \<Sigma> [] [] PObjFalse"
    using local_false by (simp only: empty)
  have theorem_false: "pH_proves \<Sigma> [] PObjFalse"
    by (rule pH_local_empty_to_theorem[OF local_empty])
  show False by (rule notE[OF pH_string_not_false_from_finite_calibration theorem_false])
qed

theorem pH_empty_consistent_from_finite_calibration:
  fixes \<Sigma> :: "'c psignature"
  shows "pH_consistent \<Sigma> [] {}"
proof -
  let ?k = "\<lambda>_ :: 'c. (''calibration'' :: string)"
  let ?\<Omega> = "\<lambda>_ :: otype. (UNIV :: string set)"
  have maps: "\<And>c \<sigma>. c \<in> \<Sigma> \<sigma> \<Longrightarrow> ?k c \<in> ?\<Omega> \<sigma>" by simp
  have target: "pH_consistent ?\<Omega> [] (phenkin_map ?k ` {})"
    by (simp only: image_empty; rule pH_string_empty_consistent_from_finite_calibration)
  show ?thesis by (rule pH_map_consistency_reflection[where k="?k" and \<Omega>="?\<Omega>", OF maps target])
qed

subsection \<open>Unconditional inhabitation of the current model predicates\<close>

text \<open>
  The empty theory is typed and consistent for every declared signature.
  The following witnesses use the explicitly displayed canonical carrier.
  A model's domains, denotation, and valuation are existentially quantified;
  HOL carrier types are not quantified over inside these statements.
\<close>

theorem pbbk_model_exists_from_finite_calibration:
  fixes \<Sigma> :: "'c psignature"
  shows "\<exists>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
    \<exists>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
      'c pterm \<Rightarrow> ('c phenkin_full_name) pHc_value.
    \<exists>V. pbbk_model \<Sigma> D J V"
proof -
  have typed: "pH_typed_theory \<Sigma> [] {}" by (simp add: pH_typed_theory_def)
  have existence: "\<exists>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
    \<exists>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
      'c pterm \<Rightarrow> ('c phenkin_full_name) pHc_value.
    \<exists>V. pbbk_model \<Sigma> D J V \<and> (\<forall>A \<in> {}. \<forall>g. V (J g A))"
    by (rule pH_BBK_model_existence[OF typed pH_empty_consistent_from_finite_calibration])
  show ?thesis using existence by simp
qed

theorem paper_db_structure_exists_from_finite_calibration:
  fixes \<Sigma> :: "'c ssignature"
  shows "\<exists>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
    \<exists>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
      'c paper_term \<Rightarrow> ('c phenkin_full_name) pHc_value.
    \<exists>V. paper_db_bbk_structure \<Sigma> D J V"
proof -
  obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set"
    and J V where model: "pbbk_model \<Sigma> D J V"
    using pbbk_model_exists_from_finite_calibration[where \<Sigma>=\<Sigma>] by (elim exE)
  have source: "paper_db_bbk_model \<Sigma> D (\<lambda>g A. J g (paper_to_pterm A)) V"
    by (rule pbbk_to_paper_db_model[OF model])
  have weak: "paper_db_bbk_structure \<Sigma> D (\<lambda>g A. J g (paper_to_pterm A)) V"
    by (rule paper_db_bbk_model.axioms(1)[OF source])
  show ?thesis by (rule exI[where x=D], rule exI[where x="\<lambda>g A. J g (paper_to_pterm A)"],
    rule exI[where x=V], rule weak)
qed

theorem paper_named_model_exists_from_finite_calibration:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "sg_rich G"
  shows "\<exists>D :: otype \<Rightarrow> (otype \<times> ('c phenkin_full_name) pHc_value) set.
    \<exists>J :: (otype \<times> ('c phenkin_full_name) pHc_value) named_assignment \<Rightarrow>
      'c paper_named_term \<Rightarrow> (otype \<times> ('c phenkin_full_name) pHc_value).
    \<exists>V. paper_named_bbk_model \<Sigma> G D J V"
proof -
  obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set"
    and J V where source: "paper_db_bbk_structure \<Sigma> D J V"
    using paper_db_structure_exists_from_finite_calibration[where \<Sigma>=\<Sigma>] by (elim exE)
  obtain J' where named: "paper_named_bbk_model \<Sigma> G (named_tag_domain D) J' (\<lambda>v. V (snd v))"
    using paper_db_named_model_exists[OF source rich] by (elim exE)
  show ?thesis by (rule exI[where x="named_tag_domain D"], rule exI[where x=J'],
    rule exI[where x="\<lambda>v. V (snd v)"], rule named)
qed

corollary paper_standard_named_model_exists_from_finite_calibration:
  fixes \<Sigma> :: "'c ssignature"
  shows "\<exists>D :: otype \<Rightarrow> (otype \<times> ('c phenkin_full_name) pHc_value) set.
    \<exists>J :: (otype \<times> ('c phenkin_full_name) pHc_value) named_assignment \<Rightarrow>
      'c paper_named_term \<Rightarrow> (otype \<times> ('c phenkin_full_name) pHc_value).
    \<exists>V. paper_named_bbk_model \<Sigma> sg_standard_stock D J V"
  by (rule paper_named_model_exists_from_finite_calibration[OF sg_standard_stock_rich])

end
