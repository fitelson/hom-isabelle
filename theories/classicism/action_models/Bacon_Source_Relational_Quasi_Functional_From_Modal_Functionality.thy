theory Bacon_Source_Relational_Quasi_Functional_From_Modal_Functionality
  imports Bacon_Source_Relational_Quasi_Functional_Modal_Antecedent Bacon_Source_Relational_Validity_Basics
begin

section \<open>Quasi-Fregeanness and valid Modalized Functionality imply quasi-functionality\<close>

text \<open>
  Modalized Functionality is retained as the explicit validity premise
  □∀z(Fz=H z)→F=H, with its R language and eigenvariable guards.
  For two equal application profiles choose fresh variable heads and
  assign the two source values. Their common behaviour at all outgoing
  target arguments makes the boxed premise true; the supplied schema
  and actual identity truth then force equality of the source values.

  Source: p.18 n.22–23 and the final paragraph of p.52 n.73.
  No C theorem, Functionality field, arrow injectivity, fullness, or
  all-homomorphism assumption is used. The selected category may be
  empty, and no model inhabitation or consistency premise is required.
\<close>

theorem paper_R_quasi_functional_from_modal_functionality:
  fixes \<Sigma> :: "'c ssignature" and Obj :: "('c,'v) paper_bbk_model_data set"
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and quasi: "paper_bbk_quasi_fregean_on Obj Arrows"
    and modal: "\<And>M \<sigma> \<tau> F H z. M \<in> Obj \<Longrightarrow>
      paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>) \<Longrightarrow>
      paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>) \<Longrightarrow>
      G z = \<sigma> \<Longrightarrow> z \<notin> named_fv F \<Longrightarrow> z \<notin> named_fv H \<Longrightarrow>
      paper_R_bbk_model.paper_R_valid \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
        (named_paper_imp G
          (paper_R_named_box G (named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp F (NVar z)) (NApp H (NVar z))))))
          (named_paper_eq (Arr \<sigma> \<tau>) F H))"
  shows "paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
proof (unfold paper_R_quasi_functional_on_def, intro ballI allI impI)
  fix M \<sigma> \<tau>
  assume object: "M \<in> Obj" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
  have valid: "paper_R_bbk_data_valid \<Sigma> G M" by (rule paper_R_bbk_subcategory_models[OF category object])
  interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF valid])
  show "inj_on (paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau>) (paper_bbk_domain M (Arr \<sigma> \<tau>))"
  proof (rule inj_onI)
    fix d e
    assume dm: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)" and em: "e \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
      and profiles: "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> d = paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> e"
    obtain x where xt: "G x = Arr \<sigma> \<tau>" and xf: "x \<notin> {}"
      by (rule paper_R_rich_fresh[OF Model.stock_rich rt finite.emptyI])
    have finite_x: "finite {x}" by simp
    obtain y where yt: "G y = Arr \<sigma> \<tau>" and yf: "y \<notin> {x}"
      by (rule paper_R_rich_fresh[OF Model.stock_rich rt finite_x])
    have different: "y \<noteq> x" using yf by simp
    have sr: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF rt])
    have finite_xy: "finite {x,y}" by simp
    obtain z where zt: "G z = \<sigma>" and zf: "z \<notin> {x,y}"
      by (rule paper_R_rich_fresh[OF Model.stock_rich sr finite_xy])
    let ?F = "NVar x :: 'c paper_named_term"
    let ?H = "NVar y :: 'c paper_named_term"
    let ?g = "(Map.empty(x := Some d))(y := Some e)"
    let ?P = "named_paper_all \<sigma> (NLam z (named_paper_eq \<tau> (NApp ?F (NVar z)) (NApp ?H (NVar z))))"
    let ?B = "paper_R_named_box G ?P"
    let ?E = "named_paper_eq (Arr \<sigma> \<tau>) ?F ?H"
    have fl: "paper_R_in_language \<Sigma> G ?F (Arr \<sigma> \<tau>)"
      by (rule paper_R_language_Var[where G=G and n=x, OF xt rt])
    have hl: "paper_R_in_language \<Sigma> G ?H (Arr \<sigma> \<tau>)"
      by (rule paper_R_language_Var[where G=G and n=y, OF yt rt])
    have freshF: "z \<notin> named_fv ?F" and freshH: "z \<notin> named_fv ?H" using zf by simp_all
    have empty: "named_env_typed (paper_bbk_domain M) G Map.empty" by (simp add: named_env_typed_def)
    have dx: "d \<in> paper_bbk_domain M (G x)" by (simp only: xt; rule dm)
    have ey: "e \<in> paper_bbk_domain M (G y)" by (simp only: yt; rule em)
    have first_update: "named_env_typed (paper_bbk_domain M) G (Map.empty(x := Some d))"
      by (rule named_assignment_update_typed[where D="paper_bbk_domain M" and G=G and n=x, OF empty dx])
    have typed: "named_env_typed (paper_bbk_domain M) G ?g"
      by (rule named_assignment_update_typed[where D="paper_bbk_domain M" and G=G and n=y, OF first_update ey])
    have gx: "?g x = Some d" using different by simp
    have gy: "?g y = Some e" by simp
    have fa: "named_adequate ?g ?F" and ha: "named_adequate ?g ?H"
      using gx gy by (auto simp: named_adequate_def dom_def)
    have fv: "paper_bbk_denote M ?g ?F = d" by (rule Model.denote_var[where g="?g" and n=x, OF typed gx])
    have hv: "paper_bbk_denote M ?g ?H = e" by (rule Model.denote_var[where g="?g" and n=y, OF typed gy])
    have equal_profiles: "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> (paper_bbk_denote M ?g ?F) =
        paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> (paper_bbk_denote M ?g ?H)"
      by (simp only: fv hv; rule profiles)
    have boxed: "paper_bbk_valuation M (paper_bbk_denote M ?g ?B)"
      by (rule paper_R_equal_profiles_box_pointwise[
        OF category quasi object fl hl zt freshF freshH typed fa ha equal_profiles])
    have pl: "paper_R_in_language \<Sigma> G ?P Prop" by (rule paper_R_pointwise_equality_language[OF fl hl zt])
    have bl: "paper_R_in_language \<Sigma> G ?B Prop" by (rule paper_R_named_box_language[OF Model.stock_rich pl])
    have el: "paper_R_in_language \<Sigma> G ?E Prop" by (rule paper_R_named_eq_language[OF fl hl])
    have pa: "named_adequate ?g ?P" by (rule paper_R_pointwise_equality_adequate[OF fa ha])
    have ba: "named_adequate ?g ?B" using pa by (simp only: named_adequate_def paper_R_named_box_fv)
    have ea: "named_adequate ?g ?E" using fa ha by (auto simp: named_adequate_def named_paper_primitive_fv)
    have ma: "named_adequate ?g (named_paper_imp G ?B ?E)"
      by (rule iffD2[OF paper_R_imp_adequate_iff conjI[OF ba ea]])
    have schema: "Model.paper_R_valid (named_paper_imp G ?B ?E)"
      by (rule modal[OF object fl hl zt freshF freshH])
    have schema_truth: "paper_bbk_valuation M (paper_bbk_denote M ?g (named_paper_imp G ?B ?E))"
      by (rule Model.paper_R_validE[OF schema typed ma])
    have identity_truth: "paper_bbk_valuation M (paper_bbk_denote M ?g ?E)"
      using schema_truth boxed Model.paper_R_named_paper_imp_truth[OF bl el typed ba ea] by blast
    show "d = e" using identity_truth by (simp only: Model.paper_R_named_eq_truth[OF fl hl typed fa ha] fv hv)
  qed
qed

end
