theory Bacon_Source_Relational_Common_Functionality
  imports Bacon_Source_Relational_Common_Theory
    Bacon_Source_Relational_Quasi_Functional_Denotation
begin

section \<open>The common theory is closed under the fresh-variable rule\<close>

text \<open>
  If Fx=Hx belongs to T𝒞 and x∉FV(F)∪FV(H), then F=H
  belongs to T𝒞 whenever 𝒞 is quasi-functional.
  Source: Bacon–Dorr p.15 and the soundness argument of
  Theorem 3.12, p.51. The heads may be open.

  Identity truth gives the common denotation premise. The
  quasi-functional denotation theorem then tests every argument
  at every target model. Identity truth at the function type
  returns the literal conclusion formula.
  This proves a closure RULE for the common theory, not a
  Functionality axiom in each individual BBK model.
\<close>

theorem paper_R_common_Functionality:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and functional: "paper_R_quasi_functional_on \<Sigma> G Obj Arrows"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and nt: "G n = \<sigma>" and freshF: "n \<notin> named_fv F"
    and freshH: "n \<notin> named_fv H"
    and common: "NApp (NApp (NLogical (SEq \<tau>)) (NApp F (NVar n)))
      (NApp H (NVar n)) \<in> paper_R_common_theory \<Sigma> G Obj"
  shows "NApp (NApp (NLogical (SEq (Arr \<sigma> \<tau>))) F) H
    \<in> paper_R_common_theory \<Sigma> G Obj"
proof -
  have models: "paper_R_bbk_data_valid \<Sigma> G M" if "M \<in> Obj" for M
    by (rule paper_R_bbk_subcategory_models[OF category that])
  have rt: "paper_R_type \<sigma>"
    by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF fl]])
  have variable: "paper_R_in_language \<Sigma> G (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where G=G and n=n, OF nt rt])
  have fa: "paper_R_in_language \<Sigma> G (NApp F (NVar n)) \<tau>"
    by (rule paper_R_language_App[OF fl variable])
  have ha: "paper_R_in_language \<Sigma> G (NApp H (NVar n)) \<tau>"
    by (rule paper_R_language_App[OF hl variable])
  have equal_apps: "\<forall>M\<in>Obj. \<forall>g. named_env_typed (paper_bbk_domain M) G g \<longrightarrow>
      named_adequate g (NApp F (NVar n)) \<longrightarrow>
      named_adequate g (NApp H (NVar n)) \<longrightarrow>
      paper_bbk_denote M g (NApp F (NVar n)) = paper_bbk_denote M g (NApp H (NVar n))"
    by (rule iffD1[OF paper_R_common_identity_iff[OF models fa ha] common])
  have app_premise: "paper_bbk_denote N k (NApp F (NVar n)) =
      paper_bbk_denote N k (NApp H (NVar n))"
    if "N \<in> Obj" "named_env_typed (paper_bbk_domain N) G k"
      "named_adequate k (NApp F (NVar n))" "named_adequate k (NApp H (NVar n))" for N k
    using equal_apps that by blast
  show ?thesis
  proof (rule paper_R_common_theoryI[OF paper_R_identity_language[OF fl hl]])
    fix M g
    assume object: "M \<in> Obj" and typed: "named_env_typed (paper_bbk_domain M) G g"
      and adequate: "named_adequate g (NApp (NApp (NLogical (SEq (Arr \<sigma> \<tau>))) F) H)"
    have adequateF: "named_adequate g F" and adequateH: "named_adequate g H"
      using adequate by (auto simp only: paper_R_identity_adequate_iff)
    have equal: "paper_bbk_denote M g F = paper_bbk_denote M g H"
      by (rule paper_R_quasi_functional_denotation[
        OF category functional fl hl nt freshF freshH app_premise object typed adequateF adequateH])
    interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
      "paper_bbk_denote M" "paper_bbk_valuation M"
      by (rule paper_R_bbk_data_model[OF models[OF object]])
    show "paper_bbk_valuation M
      (paper_bbk_denote M g (NApp (NApp (NLogical (SEq (Arr \<sigma> \<tau>))) F) H))"
      using Model.valuation_identity[OF fl hl typed adequateF adequateH] equal by simp
  qed
qed

end
