theory Bacon_Source_Relational_Figure3_Syntax
  imports Bacon_Source_Relational_Logical_Language Bacon_Source_Relational_Binder_Vectors
begin

section \<open>The six literal Boolean operator identities of Figure 3\<close>

datatype paper_R_figure3_law =
  RCommAnd | RCommOr | RDistAndOr | RDistOrAnd | RDissolveAndOr | RDissolveOrAnd

definition paper_R_figure3_variables :: "sgcontext \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "paper_R_figure3_variables G p q r \<longleftrightarrow>
    G p = Prop \<and> G q = Prop \<and> G r = Prop \<and> distinct [p,q,r]"

fun paper_R_figure3_prefix :: "paper_R_figure3_law \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "paper_R_figure3_prefix RCommAnd p q r = [p,q]"
| "paper_R_figure3_prefix RCommOr p q r = [p,q]"
| "paper_R_figure3_prefix RDistAndOr p q r = [p,q,r]"
| "paper_R_figure3_prefix RDistOrAnd p q r = [p,q,r]"
| "paper_R_figure3_prefix RDissolveAndOr p q r = [p,q]"
| "paper_R_figure3_prefix RDissolveOrAnd p q r = [p,q]"

fun paper_R_figure3_bodies ::
  "paper_R_figure3_law \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'c paper_named_term \<times> 'c paper_named_term" where
  "paper_R_figure3_bodies RCommAnd p q r =
    (named_paper_and (NVar p) (NVar q), named_paper_and (NVar q) (NVar p))"
| "paper_R_figure3_bodies RCommOr p q r =
    (named_paper_or (NVar p) (NVar q), named_paper_or (NVar q) (NVar p))"
| "paper_R_figure3_bodies RDistAndOr p q r =
    (named_paper_and (NVar p) (named_paper_or (NVar q) (NVar r)),
     named_paper_or (named_paper_and (NVar p) (NVar q)) (named_paper_and (NVar p) (NVar r)))"
| "paper_R_figure3_bodies RDistOrAnd p q r =
    (named_paper_or (NVar p) (named_paper_and (NVar q) (NVar r)),
     named_paper_and (named_paper_or (NVar p) (NVar q)) (named_paper_or (NVar p) (NVar r)))"
| "paper_R_figure3_bodies RDissolveAndOr p q r =
    (named_paper_and (NVar p) (named_paper_or (NVar q) (named_paper_not (NVar q))), NVar p)"
| "paper_R_figure3_bodies RDissolveOrAnd p q r =
    (named_paper_or (NVar p) (named_paper_and (NVar q) (named_paper_not (NVar q))), NVar p)"

abbreviation paper_R_figure3_left where
  "paper_R_figure3_left law p q r \<equiv> fst (paper_R_figure3_bodies law p q r)"
abbreviation paper_R_figure3_right where
  "paper_R_figure3_right law p q r \<equiv> snd (paper_R_figure3_bodies law p q r)"

definition paper_R_figure3_axiom ::
  "sgcontext \<Rightarrow> paper_R_figure3_law \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'c paper_named_term" where
  "paper_R_figure3_axiom G law p q r =
    named_paper_eq (paper_type_vector (map G (paper_R_figure3_prefix law p q r)) Prop)
      (named_lam_vec (paper_R_figure3_prefix law p q r) (paper_R_figure3_left law p q r))
      (named_lam_vec (paper_R_figure3_prefix law p q r) (paper_R_figure3_right law p q r))"

definition paper_R_figure3_laws :: "paper_R_figure3_law list" where
  "paper_R_figure3_laws = [RCommAnd,RCommOr,RDistAndOr,RDistOrAnd,RDissolveAndOr,RDissolveOrAnd]"

definition paper_R_figure3_axioms :: "sgcontext \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'c paper_named_term list" where
  "paper_R_figure3_axioms G p q r = map (\<lambda>law. paper_R_figure3_axiom G law p q r) paper_R_figure3_laws"

lemma paper_R_figure3_axioms_length:
  "length (paper_R_figure3_axioms G p q r) = 6"
  by (simp add: paper_R_figure3_axioms_def paper_R_figure3_laws_def)

lemma paper_R_figure3_body_fv:
  "named_fv (paper_R_figure3_left law p q r) \<subseteq> set (paper_R_figure3_prefix law p q r)"
  "named_fv (paper_R_figure3_right law p q r) \<subseteq> set (paper_R_figure3_prefix law p q r)"
  by (cases law; auto simp: named_paper_primitive_fv)+

lemma paper_R_figure3_axiom_closed:
  "named_fv (paper_R_figure3_axiom G law p q r) = {}"
  unfolding paper_R_figure3_axiom_def
  using paper_R_figure3_body_fv[where law=law and p=p and q=q and r=r]
  by (simp only: named_paper_primitive_fv named_lam_vec_fv; blast)

text \<open>
  The list follows Figure 3, p.10, in its printed order:
  Commutativity-∧, Commutativity-∨, Distribution-∧∨,
  Distribution-∨∧, Dissolution-∧∨, Dissolution-∨∧.
  Distribution uses λpqr; the other four identities use λpq,
  including the vacuous q binder on each dissolution right side.
  All ∧, ∨ and ¬ occurrences are primitive source applications.

  A source instance uses an explicitly distinct Prop-typed triple.
  The six formulas are closed operator identities, not universally
  quantified scalar equations. No calculus or reverse presentation
  equivalence is defined or asserted here.
\<close>

end
