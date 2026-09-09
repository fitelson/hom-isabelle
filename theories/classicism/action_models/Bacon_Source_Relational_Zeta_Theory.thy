theory Bacon_Source_Relational_Zeta_Theory
  imports Bacon_Source_Relational_H_Theory
begin

section \<open>Guarded ζ closure as a separate property of a theory\<close>

definition paper_R_zeta_closed ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> bool" where
  "paper_R_zeta_closed \<Sigma> G T \<longleftrightarrow>
    (\<forall>F H \<sigma> \<tau> x.
      paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>) \<longrightarrow>
      paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>) \<longrightarrow>
      G x = \<sigma> \<longrightarrow> x \<notin> named_fv F \<longrightarrow> x \<notin> named_fv H \<longrightarrow>
      named_paper_eq \<tau> (NApp F (NVar x)) (NApp H (NVar x)) \<in> T \<longrightarrow>
      named_paper_eq (Arr \<sigma> \<tau>) F H \<in> T)"

lemma paper_R_zeta_closedD:
  assumes zeta: "paper_R_zeta_closed \<Sigma> G T"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and hl: "paper_R_in_language \<Sigma> G H (Arr \<sigma> \<tau>)"
    and variable: "G x = \<sigma>" and fresh_F: "x \<notin> named_fv F" and fresh_H: "x \<notin> named_fv H"
    and member: "named_paper_eq \<tau> (NApp F (NVar x)) (NApp H (NVar x)) \<in> T"
  shows "named_paper_eq (Arr \<sigma> \<tau>) F H \<in> T"
  using assms unfolding paper_R_zeta_closed_def by blast

text \<open>
  This is exactly the fresh-variable ζ rule of pp.14–16, as a
  property of the ORIGINAL set T. It is not built into H, and it
  asserts no closure after adding a temporary premise. The R-language
  guards exclude functional types ending in e.
\<close>

end
