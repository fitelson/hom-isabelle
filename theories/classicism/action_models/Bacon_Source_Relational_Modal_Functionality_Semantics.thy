theory Bacon_Source_Relational_Modal_Functionality_Semantics
  imports Bacon_Source_Relational_Identity_Axiom_Truth Bacon_Source_Relational_Quantifier_Axiom_Truth
    Bacon_Source_Relational_Binder_Truth
begin

section \<open>Pointwise application equality gives the universally quantified premise\<close>

lemma paper_R_pointwise_equality_language:
  assumes first: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and second: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)" and nt: "G n = \<sigma>"
  shows "paper_R_in_language \<Sigma> G
    (named_paper_all \<sigma> (NLam n (named_paper_eq \<tau> (NApp F (NVar n)) (NApp H (NVar n))))) Prop"
proof -
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF first]])
  have variable: "paper_R_in_language \<Sigma> G (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where G=G and n=n, OF nt rt])
  have body: "paper_R_in_language \<Sigma> G (named_paper_eq \<tau> (NApp F (NVar n)) (NApp H (NVar n))) Prop"
    by (rule paper_R_named_eq_language[OF paper_R_language_App[OF first variable] paper_R_language_App[OF second variable]])
  have nr: "paper_R_type (G n)" by (simp only: nt; rule rt)
  have predicate: "paper_R_in_language \<Sigma> G (NLam n (named_paper_eq \<tau> (NApp F (NVar n)) (NApp H (NVar n))))
      (Arr \<sigma> Prop)"
    using paper_R_binder_formula_language[OF body nr] by (simp only: nt)
  show ?thesis by (rule paper_R_named_all_language[OF predicate])
qed

lemma paper_R_pointwise_equality_adequate:
  assumes first: "named_adequate g F" and second: "named_adequate g H"
  shows "named_adequate g
    (named_paper_all \<sigma> (NLam n (named_paper_eq \<tau> (NApp F (NVar n)) (NApp H (NVar n)))))"
  using first second by (auto simp: named_adequate_def named_paper_primitive_fv)

context paper_R_bbk_model
begin

theorem paper_R_all_application_equality_truth:
  assumes first: "paper_R_in_language signature stock F (Arr \<sigma> \<tau>)"
    and second: "paper_R_in_language signature stock H (Arr \<sigma> \<tau>)"
    and nt: "stock n = \<sigma>" and freshF: "n \<notin> named_fv F" and freshH: "n \<notin> named_fv H"
    and typed: "named_env_typed domain stock g" and fa: "named_adequate g F" and ha: "named_adequate g H"
    and applications: "\<And>a. a \<in> domain \<sigma> \<Longrightarrow>
      paper_R_application signature stock domain denote \<sigma> \<tau> (denote g F) a =
      paper_R_application signature stock domain denote \<sigma> \<tau> (denote g H) a"
  shows "valuation (denote g
    (named_paper_all \<sigma> (NLam n (named_paper_eq \<tau> (NApp F (NVar n)) (NApp H (NVar n))))))"
proof -
  let ?P = "named_paper_eq \<tau> (NApp F (NVar n)) (NApp H (NVar n))"
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF first]])
  have variable: "paper_R_in_language signature stock (NVar n) \<sigma>"
    by (rule paper_R_language_Var[where G=stock and n=n, OF nt rt])
  have fl: "paper_R_in_language signature stock (NApp F (NVar n)) \<tau>" by (rule paper_R_language_App[OF first variable])
  have hl: "paper_R_in_language signature stock (NApp H (NVar n)) \<tau>" by (rule paper_R_language_App[OF second variable])
  have body: "paper_R_in_language signature stock ?P Prop" by (rule paper_R_named_eq_language[OF fl hl])
  have adequate: "named_adequate g (NLam n ?P)" using fa ha
    by (auto simp: named_adequate_def named_paper_primitive_fv)
  have points: "valuation (denote (g(n := Some a)) ?P)" if member: "a \<in> domain \<sigma>" for a
  proof -
    have slot: "a \<in> domain (stock n)" by (simp only: nt; rule member)
    have updated: "named_env_typed domain stock (g(n := Some a))"
      by (rule named_assignment_update_typed[where D=domain and G=stock and n=n, OF typed slot])
    have left_adequate: "named_adequate (g(n := Some a)) (NApp F (NVar n))"
      by (rule named_quantifier_application_adequate[OF fa])
    have right_adequate: "named_adequate (g(n := Some a)) (NApp H (NVar n))"
      by (rule named_quantifier_application_adequate[OF ha])
    have left_value: "paper_R_application signature stock domain denote \<sigma> \<tau> (denote g F) a =
      denote (g(n := Some a)) (NApp F (NVar n))"
      by (rule paper_R_fresh_application_denote[OF first typed fa nt freshF member])
    have right_value: "paper_R_application signature stock domain denote \<sigma> \<tau> (denote g H) a =
      denote (g(n := Some a)) (NApp H (NVar n))"
      by (rule paper_R_fresh_application_denote[OF second typed ha nt freshH member])
    have same: "denote (g(n := Some a)) (NApp F (NVar n)) = denote (g(n := Some a)) (NApp H (NVar n))"
      using applications[OF member] by (simp only: left_value right_value)
    show ?thesis by (simp only: paper_R_named_eq_truth[OF fl hl updated left_adequate right_adequate]; rule same)
  qed
  show ?thesis by (simp only: paper_R_forall_binder_truth[OF body nt rt typed adequate]; intro ballI; rule points; assumption)
qed

end

end
