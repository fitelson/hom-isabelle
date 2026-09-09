theory Bacon_Source_BBK_Application
  imports Bacon_Source_BBK_Model_Data
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Conversion_Contexts
    Bacon_Source_Vocabulary_Development.Bacon_Source_Rich_Stock
begin

section \<open>Recovering appᴹd(a) from named interpretation\<close>

text \<open>
  For d∈Mσ→τ and a∈Mσ, Definition 3.3 (Bacon–Dorr,
  pp.45–46) defines appᴹd(a)=⟦Xy⟧ᴹ[X↦d,y↦a]. Footnote 65
  explains why the choice of variables does not matter, and why
  application need not be an additional ingredient of a BBK model.

  We first collect all values of typed applications with the indicated
  head and argument denotations. Two distinct variables and their
  two-entry partial assignment give an actual witness. Clause (ii.b)
  proves that every such witness has the same result. Hilbert choice
  then selects that result; only guarded lemmas describe its value.
  Off the specified domains the total HOL function is unconstrained.
  No Functionality, fullness, closed denotability or added App field
  is assumed. This is application reconstruction, not extensionalism.
\<close>

definition paper_bbk_application_graph ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data \<Rightarrow>
    otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau> d a b \<longleftrightarrow>
    (\<exists>g F A. named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> \<tau>) \<and>
      named_in_language paper_logical_type \<Sigma> G A \<sigma> \<and>
      named_env_typed (paper_bbk_domain M) G g \<and> named_adequate g (NApp F A) \<and>
      paper_bbk_denote M g F = d \<and> paper_bbk_denote M g A = a \<and>
      paper_bbk_denote M g (NApp F A) = b)"

definition paper_bbk_application ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> ('c,'v) paper_bbk_model_data \<Rightarrow>
    otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v" where
  "paper_bbk_application \<Sigma> G M \<sigma> \<tau> d a =
    (SOME b. paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau> d a b)"

lemma paper_bbk_application_graphI:
  assumes head: "named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g (NApp F A)"
    and head_value: "paper_bbk_denote M g F = d"
    and arg_value: "paper_bbk_denote M g A = a"
    and app_value: "paper_bbk_denote M g (NApp F A) = b"
  shows "paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau> d a b"
  unfolding paper_bbk_application_graph_def
  by (rule exI[where x=g], rule exI[where x=F], rule exI[where x=A],
    intro conjI; fact)

lemma paper_bbk_application_graphE:
  assumes graph: "paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau> d a b"
  obtains g F A where
    "named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> \<tau>)"
    "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    "named_env_typed (paper_bbk_domain M) G g" "named_adequate g (NApp F A)"
    "paper_bbk_denote M g F = d" "paper_bbk_denote M g A = a"
    "paper_bbk_denote M g (NApp F A) = b"
  using graph that unfolding paper_bbk_application_graph_def by blast

section \<open>Actual variable witnesses\<close>

lemma paper_bbk_application_graph_exists:
  fixes M :: "('c,'v) paper_bbk_model_data"
  assumes valid: "paper_bbk_data_valid \<Sigma> G M"
    and dm: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    and am: "a \<in> paper_bbk_domain M \<sigma>"
  shows "\<exists>b. paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau> d a b"
proof -
  interpret Model: paper_named_bbk_model \<Sigma> G "paper_bbk_domain M"
    "paper_bbk_denote M" "paper_bbk_valuation M" by (rule paper_bbk_data_model[OF valid])
  obtain x where xt: "G x = Arr \<sigma> \<tau>"
    using sg_rich_fresh[where G=G and S="{}" and \<sigma>="Arr \<sigma> \<tau>", OF Model.stock_rich]
    by auto
  obtain y where yt: "G y = \<sigma>" and fresh: "y \<notin> {x}"
    using sg_rich_fresh[where G=G and S="{x}" and \<sigma>=\<sigma>, OF Model.stock_rich]
    by auto
  have distinct: "x \<noteq> y" using fresh by auto
  let ?g = "(Map.empty(x := Some d))(y := Some a)"
  have empty_typed: "named_env_typed (paper_bbk_domain M) G Map.empty"
    by (simp only: named_env_typed_def; simp)
  have dx: "d \<in> paper_bbk_domain M (G x)" by (simp only: xt; rule dm)
  have ay: "a \<in> paper_bbk_domain M (G y)" by (simp only: yt; rule am)
  have first_typed: "named_env_typed (paper_bbk_domain M) G (Map.empty(x := Some d))"
    by (rule named_assignment_update_typed[where D="paper_bbk_domain M" and G=G, OF empty_typed dx])
  have typed: "named_env_typed (paper_bbk_domain M) G ?g"
    by (rule named_assignment_update_typed[where D="paper_bbk_domain M" and G=G, OF first_typed ay])
  have gx: "?g x = Some d" by (simp add: distinct)
  have gy: "?g y = Some a" by simp
  have head: "named_in_language paper_logical_type \<Sigma> G (NVar x :: 'c paper_named_term) (Arr \<sigma> \<tau>)"
    unfolding named_in_language_def
    by (simp only: named_var_type_iff named_in_signature.simps xt; simp)
  have argument: "named_in_language paper_logical_type \<Sigma> G (NVar y :: 'c paper_named_term) \<sigma>"
    unfolding named_in_language_def
    by (simp only: named_var_type_iff named_in_signature.simps yt; simp)
  have adequate: "named_adequate ?g (NApp (NVar x) (NVar y) :: 'c paper_named_term)"
    by (simp add: named_adequate_def named_fv.simps dom_def distinct)
  have head_value: "paper_bbk_denote M ?g (NVar x) = d" by (rule Model.denote_var[OF typed gx])
  have arg_value: "paper_bbk_denote M ?g (NVar y) = a" by (rule Model.denote_var[OF typed gy])
  have graph: "paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau> d a
      (paper_bbk_denote M ?g (NApp (NVar x) (NVar y)))"
    by (rule paper_bbk_application_graphI[OF head argument typed adequate head_value arg_value refl])
  show ?thesis by (rule exI[where x="paper_bbk_denote M ?g (NApp (NVar x) (NVar y))"], rule graph)
qed

section \<open>Independence of all application witnesses\<close>

lemma paper_bbk_application_graph_unique:
  assumes valid: "paper_bbk_data_valid \<Sigma> G M"
    and first: "paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau> d a b"
    and second: "paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau> d a c"
  shows "b = c"
proof -
  interpret Model: paper_named_bbk_model \<Sigma> G "paper_bbk_domain M"
    "paper_bbk_denote M" "paper_bbk_valuation M" by (rule paper_bbk_data_model[OF valid])
  obtain g F A where fl: "named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> \<tau>)"
    and al: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and gt: "named_env_typed (paper_bbk_domain M) G g" and ga: "named_adequate g (NApp F A)"
    and fv: "paper_bbk_denote M g F = d" and av: "paper_bbk_denote M g A = a"
    and bv: "paper_bbk_denote M g (NApp F A) = b"
    by (rule paper_bbk_application_graphE[OF first])
  obtain h H B where hl: "named_in_language paper_logical_type \<Sigma> G H (Arr \<sigma> \<tau>)"
    and bl: "named_in_language paper_logical_type \<Sigma> G B \<sigma>"
    and ht: "named_env_typed (paper_bbk_domain M) G h" and ha: "named_adequate h (NApp H B)"
    and hv: "paper_bbk_denote M h H = d" and avb: "paper_bbk_denote M h B = a"
    and cv: "paper_bbk_denote M h (NApp H B) = c"
    by (rule paper_bbk_application_graphE[OF second])
  have heads: "paper_bbk_denote M g F = paper_bbk_denote M h H" by (simp only: fv hv)
  have args: "paper_bbk_denote M g A = paper_bbk_denote M h B" by (simp only: av avb)
  have apps: "paper_bbk_denote M g (NApp F A) = paper_bbk_denote M h (NApp H B)"
    by (rule Model.denote_application_cong[OF fl al hl bl gt ht ga ha heads args])
  show ?thesis using apps by (simp only: bv cv)
qed

lemma paper_bbk_application_graph_type:
  assumes valid: "paper_bbk_data_valid \<Sigma> G M"
    and graph: "paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau> d a b"
  shows "b \<in> paper_bbk_domain M \<tau>"
proof -
  obtain g F A where fl: "named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> \<tau>)"
    and al: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and typed: "named_env_typed (paper_bbk_domain M) G g" and adequate: "named_adequate g (NApp F A)"
    and app_value: "paper_bbk_denote M g (NApp F A) = b"
    by (rule paper_bbk_application_graphE[OF graph]; rule that; assumption)
  have application: "named_in_language paper_logical_type \<Sigma> G (NApp F A) \<tau>"
    by (rule named_language_App[OF fl al])
  have member: "paper_bbk_denote M g (NApp F A) \<in> paper_bbk_domain M \<tau>"
    by (rule paper_bbk_data_denote_type[OF valid application typed adequate])
  show ?thesis using member by (simp only: app_value)
qed

lemma paper_bbk_application_graph_chosen:
  assumes valid: "paper_bbk_data_valid \<Sigma> G M"
    and dm: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)" and am: "a \<in> paper_bbk_domain M \<sigma>"
  shows "paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau> d a
    (paper_bbk_application \<Sigma> G M \<sigma> \<tau> d a)"
  unfolding paper_bbk_application_def
  by (rule someI_ex[OF paper_bbk_application_graph_exists[OF valid dm am]])

lemma paper_bbk_application_type:
  assumes valid: "paper_bbk_data_valid \<Sigma> G M"
    and dm: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)" and am: "a \<in> paper_bbk_domain M \<sigma>"
  shows "paper_bbk_application \<Sigma> G M \<sigma> \<tau> d a \<in> paper_bbk_domain M \<tau>"
  by (rule paper_bbk_application_graph_type[OF valid paper_bbk_application_graph_chosen[OF valid dm am]])

theorem paper_bbk_application_denote:
  assumes valid: "paper_bbk_data_valid \<Sigma> G M"
    and fl: "named_in_language paper_logical_type \<Sigma> G F (Arr \<sigma> \<tau>)"
    and al: "named_in_language paper_logical_type \<Sigma> G A \<sigma>"
    and typed: "named_env_typed (paper_bbk_domain M) G g" and adequate: "named_adequate g (NApp F A)"
  shows "paper_bbk_application \<Sigma> G M \<sigma> \<tau>
    (paper_bbk_denote M g F) (paper_bbk_denote M g A) = paper_bbk_denote M g (NApp F A)"
proof -
  have both_adequate: "named_adequate g F \<and> named_adequate g A"
    using adequate by (auto simp: named_adequate_def)
  have fa: "named_adequate g F" by (rule conjunct1[OF both_adequate])
  have aa: "named_adequate g A" by (rule conjunct2[OF both_adequate])
  have dm: "paper_bbk_denote M g F \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    by (rule paper_bbk_data_denote_type[OF valid fl typed fa])
  have am: "paper_bbk_denote M g A \<in> paper_bbk_domain M \<sigma>"
    by (rule paper_bbk_data_denote_type[OF valid al typed aa])
  have chosen: "paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau>
      (paper_bbk_denote M g F) (paper_bbk_denote M g A)
      (paper_bbk_application \<Sigma> G M \<sigma> \<tau> (paper_bbk_denote M g F) (paper_bbk_denote M g A))"
    by (rule paper_bbk_application_graph_chosen[OF valid dm am])
  have original: "paper_bbk_application_graph \<Sigma> G M \<sigma> \<tau>
      (paper_bbk_denote M g F) (paper_bbk_denote M g A) (paper_bbk_denote M g (NApp F A))"
    by (rule paper_bbk_application_graphI[OF fl al typed adequate refl refl refl])
  show ?thesis by (rule paper_bbk_application_graph_unique[OF valid chosen original])
qed

end
