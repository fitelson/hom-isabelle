theory Bacon_Book_Modalized_Exponential_Domain
  imports Bacon_Book_Preorder_Category
begin

section \<open>All world-indexed homomorphisms on a future cone\<close>

definition book_modalized_exponential_pairs ::
  "'w set \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow> ('w \<Rightarrow> 'a set) \<Rightarrow> 'w \<Rightarrow> ('w \<times> 'a) set" where
  "book_modalized_exponential_pairs W le A w = {(v,a). v \<in> W \<and> le w v \<and> a \<in> A v}"

definition book_modalized_exponential ::
  "'w set \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> bool) \<Rightarrow>
    ('w \<Rightarrow> 'a set) \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    ('w \<Rightarrow> 'b set) \<Rightarrow> ('w \<Rightarrow> 'w \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
    'w \<Rightarrow> (('w \<times> 'a) \<Rightarrow> 'b) set" where
  "book_modalized_exponential W le A iA B iB w =
    {f. (\<forall>p. p \<notin> book_modalized_exponential_pairs W le A w \<longrightarrow> f p = undefined) \<and>
      (\<forall>v a. v \<in> W \<longrightarrow> le w v \<longrightarrow> a \<in> A v \<longrightarrow> f (v,a) \<in> B v) \<and>
      (\<forall>v u a. v \<in> W \<longrightarrow> le w v \<longrightarrow> u \<in> W \<longrightarrow> le v u \<longrightarrow>
        a \<in> A v \<longrightarrow> iB v u (f (v,a)) = f (u,iA v u a))}"

lemma book_modalized_exponential_pairs_iff:
  "(v,a) \<in> book_modalized_exponential_pairs W le A w \<longleftrightarrow> v \<in> W \<and> le w v \<and> a \<in> A v"
  by (simp add: book_modalized_exponential_pairs_def)

lemma book_modalized_exponentialI:
  assumes normal: "\<And>p. p \<notin> book_modalized_exponential_pairs W le A w \<Longrightarrow> f p = undefined"
    and typed: "\<And>v a. v \<in> W \<Longrightarrow> le w v \<Longrightarrow> a \<in> A v \<Longrightarrow> f (v,a) \<in> B v"
    and natural: "\<And>v u a. v \<in> W \<Longrightarrow> le w v \<Longrightarrow> u \<in> W \<Longrightarrow> le v u \<Longrightarrow>
      a \<in> A v \<Longrightarrow> iB v u (f (v,a)) = f (u,iA v u a)"
  shows "f \<in> book_modalized_exponential W le A iA B iB w"
  using normal typed natural unfolding book_modalized_exponential_def by blast

lemma book_modalized_exponential_normal:
  "f \<in> book_modalized_exponential W le A iA B iB w \<Longrightarrow>
    p \<notin> book_modalized_exponential_pairs W le A w \<Longrightarrow> f p = undefined"
  unfolding book_modalized_exponential_def by blast

lemma book_modalized_exponential_type:
  "f \<in> book_modalized_exponential W le A iA B iB w \<Longrightarrow>
    v \<in> W \<Longrightarrow> le w v \<Longrightarrow> a \<in> A v \<Longrightarrow> f (v,a) \<in> B v"
  unfolding book_modalized_exponential_def by blast

lemma book_modalized_exponential_natural:
  "f \<in> book_modalized_exponential W le A iA B iB w \<Longrightarrow>
    v \<in> W \<Longrightarrow> le w v \<Longrightarrow> u \<in> W \<Longrightarrow> le v u \<Longrightarrow> a \<in> A v \<Longrightarrow>
    iB v u (f (v,a)) = f (u,iA v u a)"
  unfolding book_modalized_exponential_def by blast

text \<open>
  Definition 17.9, p.364, admits ALL homomorphisms on A↑w and
  B↑w, not only restrictions of globally defined homomorphisms.
  The definition quantifies over every function satisfying the displayed
  typing and counterpart equations. Its total HOL extension is fixed
  only outside the valid world/argument pairs. Endpoint modalized-set
  laws are separate premises of subsequent action results; this leaf
  assumes no nonempty fibers, injectivity, quotient, or logical model.
\<close>

end
