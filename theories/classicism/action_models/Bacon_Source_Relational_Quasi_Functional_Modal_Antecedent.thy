theory Bacon_Source_Relational_Quasi_Functional_Modal_Antecedent
  imports Bacon_Source_Relational_Modal_Functionality_Semantics
    Bacon_Source_Relational_Quasi_Fregean_Box Bacon_Source_Relational_Application_Profile_Action
begin

section \<open>Equal application profiles make the modal premise true\<close>

theorem paper_R_equal_profiles_box_pointwise:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and quasi: "paper_bbk_quasi_fregean_on Obj Arrows" and object: "M \<in> Obj"
    and first: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and second: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and nt: "G n = \<sigma>" and freshF: "n \<notin> named_fv F" and freshH: "n \<notin> named_fv H"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and fa: "named_adequate g F" and ha: "named_adequate g H"
    and profiles: "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> (paper_bbk_denote M g F) =
      paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> (paper_bbk_denote M g H)"
  shows "paper_bbk_valuation M (paper_bbk_denote M g (paper_R_named_box G
    (named_paper_all \<sigma> (NLam n (named_paper_eq \<tau> (NApp F (NVar n)) (NApp H (NVar n)))))))"
proof -
  let ?P = "named_paper_all \<sigma> (NLam n (named_paper_eq \<tau> (NApp F (NVar n)) (NApp H (NVar n))))"
  have language: "paper_R_in_language \<Sigma> G ?P Prop" by (rule paper_R_pointwise_equality_language[OF first second nt])
  have adequate: "named_adequate g ?P" by (rule paper_R_pointwise_equality_adequate[OF fa ha])
  have outgoing: "paper_bbk_valuation (paper_arrow_target r) (paper_arrow_map r Prop (paper_bbk_denote M g ?P))"
    if arrow: "r \<in> Arrows" and src: "paper_arrow_source r = M" for r
  proof -
    let ?N = "paper_arrow_target r"
    let ?k = "paper_hom_assignment G (paper_arrow_map r) g"
    have full: "r \<in> paper_R_bbk_arrows \<Sigma> G Obj" by (rule paper_R_bbk_subcategory_arrow[OF category arrow])
    have morphism: "paper_R_bbk_data_morphism \<Sigma> G M ?N (paper_arrow_map r)"
      using paper_R_bbk_arrows_morphism[OF full] by (simp only: src)
    have hom: "paper_R_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
        (paper_bbk_domain ?N) (paper_bbk_denote ?N) (paper_arrow_map r)"
      by (rule paper_R_bbk_data_morphism_raw[OF morphism])
    interpret Target: paper_R_bbk_model \<Sigma> G "paper_bbk_domain ?N" "paper_bbk_denote ?N" "paper_bbk_valuation ?N"
      by (rule paper_R_bbk_data_model[OF paper_R_bbk_data_morphism_target[OF morphism]])
    have kt: "named_env_typed (paper_bbk_domain ?N) G ?k" by (rule paper_R_bbk_homomorphism_assignment_typed[OF hom typed])
    have kf: "named_adequate ?k F" by (rule paper_R_bbk_homomorphism_assignment_adequate[OF fa])
    have kh: "named_adequate ?k H" by (rule paper_R_bbk_homomorphism_assignment_adequate[OF ha])
    have mappedF: "paper_arrow_map r (Arr \<sigma> \<tau>) (paper_bbk_denote M g F) = paper_bbk_denote ?N ?k F"
      by (rule paper_R_bbk_homomorphism_denote[OF hom first typed fa])
    have mappedH: "paper_arrow_map r (Arr \<sigma> \<tau>) (paper_bbk_denote M g H) = paper_bbk_denote ?N ?k H"
      by (rule paper_R_bbk_homomorphism_denote[OF hom second typed ha])
    have applications: "paper_R_application \<Sigma> G (paper_bbk_domain ?N) (paper_bbk_denote ?N) \<sigma> \<tau>
        (paper_bbk_denote ?N ?k F) a =
      paper_R_application \<Sigma> G (paper_bbk_domain ?N) (paper_bbk_denote ?N) \<sigma> \<tau>
        (paper_bbk_denote ?N ?k H) a" if member: "a \<in> paper_bbk_domain ?N \<sigma>" for a
    proof -
      have at_pair: "paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> (paper_bbk_denote M g F) (r,a) =
        paper_R_app_profile_on \<Sigma> G Arrows M \<sigma> \<tau> (paper_bbk_denote M g H) (r,a)"
        by (rule fun_cong[OF profiles])
      show ?thesis using at_pair
        by (simp only: paper_R_app_profile_on_value[OF arrow src member] mappedF mappedH)
    qed
    have truth: "paper_bbk_valuation ?N (paper_bbk_denote ?N ?k ?P)"
      by (rule Target.paper_R_all_application_equality_truth[OF first second nt freshF freshH kt kf kh applications])
    have mappedP: "paper_arrow_map r Prop (paper_bbk_denote M g ?P) = paper_bbk_denote ?N ?k ?P"
      by (rule paper_R_bbk_homomorphism_denote[OF hom language typed adequate])
    show ?thesis by (simp only: mappedP; rule truth)
  qed
  show ?thesis by (rule iffD2[OF paper_R_quasi_fregean_box_truth[OF category quasi object language typed adequate]];
    intro ballI impI; rule outgoing; assumption)
qed

text \<open>
  Every arrow in the selected category and every argument in its target
  domain is tested. No assertion that target arguments are transported
  from M, nor any surjectivity or injectivity of the arrows, is used.
  This is the modal antecedent only; Modalized Functionality remains an
  explicit additional validity premise in the quasi-functionality result.
\<close>

end
