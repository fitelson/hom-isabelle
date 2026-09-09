theory Bacon_Source_Relational_Intensional_Restriction
  imports Bacon_Source_Relational_Profile_Restriction
begin

section \<open>Inheritance of profile injectivity on retained objects\<close>

text \<open>
  Restricting the objects while preserving their outgoing arrows leaves
  their profiles unchanged, hence preserves quasi-Fregeanness,
  quasi-functionality and intensionality (Definition 3.11, pp.50–51).
  This supplies the injectivity part of Proposition 3.22's reachable
  restriction, p.57; category and reachability facts are separate.

  The hypotheses are raw object inclusion, outgoing-arrow equality,
  and the indicated original injectivity property. No model predicate,
  category existence, valuation preservation, or common-theory equality
  is assumed or proved. In particular, removing objects can enlarge
  the common theory even though each retained object's profiles agree.
\<close>

theorem paper_R_quasi_fregean_outgoing_restrict:
  assumes subset: "NewObj \<subseteq> Obj"
    and outgoing: "\<And>M h. M \<in> NewObj \<Longrightarrow>
      (h \<in> NewArrows \<and> paper_arrow_source h = M) \<longleftrightarrow>
      (h \<in> Arrows \<and> paper_arrow_source h = M)"
    and quasi: "paper_bbk_quasi_fregean_on Obj Arrows"
  shows "paper_bbk_quasi_fregean_on NewObj NewArrows"
proof (unfold paper_bbk_quasi_fregean_on_def, intro ballI)
  fix M
  assume object: "M \<in> NewObj"
  have original_object: "M \<in> Obj" by (rule subsetD[OF subset object])
  have original: "inj_on (paper_bbk_truth_profile_on Arrows M) (paper_bbk_domain M Prop)"
    using quasi original_object unfolding paper_bbk_quasi_fregean_on_def by blast
  have profiles: "paper_bbk_truth_profile_on NewArrows M = paper_bbk_truth_profile_on Arrows M"
    by (rule ext, rule paper_R_truth_profile_outgoing_cong, rule outgoing[OF object])
  show "inj_on (paper_bbk_truth_profile_on NewArrows M) (paper_bbk_domain M Prop)"
    by (simp only: profiles; rule original)
qed

theorem paper_R_quasi_functional_outgoing_restrict:
  assumes subset: "NewObj \<subseteq> Obj"
    and outgoing: "\<And>M h. M \<in> NewObj \<Longrightarrow>
      (h \<in> NewArrows \<and> paper_arrow_source h = M) \<longleftrightarrow>
      (h \<in> Arrows \<and> paper_arrow_source h = M)"
    and quasi: "paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
  shows "paper_R_quasi_functional_on \<Sigma> G NewObj NewArrows"
proof (unfold paper_R_quasi_functional_on_def, intro ballI allI impI)
  fix M \<sigma> \<tau>
  assume object: "M \<in> NewObj" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
  have original_object: "M \<in> Obj" by (rule subsetD[OF subset object])
  have original: "inj_on (paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau>)
      (paper_bbk_domain M (Arr \<sigma> \<tau>))"
    using quasi original_object rt unfolding paper_R_quasi_functional_on_def by blast
  have profiles: "paper_R_app_profile_on \<Sigma> G NewArrows M \<sigma> \<tau> =
      paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau>"
    by (rule ext, rule paper_R_app_profile_outgoing_cong, rule outgoing[OF object])
  show "inj_on (paper_R_app_profile_on \<Sigma> G NewArrows M \<sigma> \<tau>)
      (paper_bbk_domain M (Arr \<sigma> \<tau>))"
    by (simp only: profiles; rule original)
qed

theorem paper_R_intensional_outgoing_restrict:
  assumes subset: "NewObj \<subseteq> Obj"
    and outgoing: "\<And>M h. M \<in> NewObj \<Longrightarrow>
      (h \<in> NewArrows \<and> paper_arrow_source h = M) \<longleftrightarrow>
      (h \<in> Arrows \<and> paper_arrow_source h = M)"
    and intensional: "paper_R_intensional_on \<Sigma> G Obj Arrows"
  shows "paper_R_intensional_on \<Sigma> G NewObj NewArrows"
proof (unfold paper_R_intensional_on_def, intro ballI allI impI)
  fix M \<sigma>s
  assume object: "M \<in> NewObj" and types: "list_all paper_R_type \<sigma>s"
  have original_object: "M \<in> Obj" by (rule subsetD[OF subset object])
  have original: "inj_on (paper_R_intension_on \<Sigma> G Arrows M \<sigma>s)
      (paper_bbk_domain M (paper_type_vector \<sigma>s Prop))"
    using intensional original_object types unfolding paper_R_intensional_on_def by blast
  have profiles: "paper_R_intension_on \<Sigma> G NewArrows M \<sigma>s =
      paper_R_intension_on \<Sigma> G Arrows M \<sigma>s"
    by (rule ext, rule paper_R_intension_outgoing_cong, rule outgoing[OF object])
  show "inj_on (paper_R_intension_on \<Sigma> G NewArrows M \<sigma>s)
      (paper_bbk_domain M (paper_type_vector \<sigma>s Prop))"
    by (simp only: profiles; rule original)
qed

end
