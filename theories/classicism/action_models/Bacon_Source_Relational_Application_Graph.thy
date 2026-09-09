theory Bacon_Source_Relational_Application_Graph
  imports Bacon_Source_Relational_BBK_Interface
begin

section \<open>R-typed variable witnesses and application graphs\<close>

text \<open>
  For σ→τ∈R, choose X:σ→τ and y:σ with X≠y and use
  the partial assignment [X↦d,y↦a]. Source: Bacon–Dorr §1.1,
  p.5, Definition 3.1, pp.43–44, and Definition 3.3 with footnote
  65, pp.45–46. Only richness at R types is needed.

  The graph below records R-language application witnesses directly.
  It uses separate domain and interpretation parameters, not an F-model
  record. No F-model axiom, F-rich stock, total completion, closed
  denotability or application operation is presumed.
\<close>

lemma paper_R_rich_fresh:
  assumes rich: "paper_R_rich G" and rt: "paper_R_type \<sigma>" and finite: "finite S"
  obtains n where "G n = \<sigma>" and "n \<notin> S"
proof -
  have infinite: "infinite {n. G n = \<sigma>}" by (rule paper_R_rich_type[OF rich rt])
  have exists: "\<exists>n. G n = \<sigma> \<and> n \<notin> S"
  proof (rule ccontr)
    assume absent: "\<not> (\<exists>n. G n = \<sigma> \<and> n \<notin> S)"
    have subset: "{n. G n = \<sigma>} \<subseteq> S" using absent by auto
    have "finite {n. G n = \<sigma>}" by (rule finite_subset[OF subset finite])
    with infinite show False by contradiction
  qed
  obtain n where nt: "G n = \<sigma>" and fresh: "n \<notin> S" using exists by blast
  show thesis by (rule that[OF nt fresh])
qed

lemma paper_R_language_Var:
  assumes nt: "G n = \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_R_in_language \<Sigma> G (NVar n) \<sigma>"
proof -
  have variable_type: "paper_R_type (G n)" by (simp only: nt; rule rt)
  have typed: "paper_R_has_type G (NVar n) (G n)"
    by (rule paper_R_has_type.Var[where G=G and n=n, OF variable_type])
  show ?thesis using typed by (simp add: paper_R_in_language_def nt)
qed

lemma paper_R_language_App:
  assumes head: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "paper_R_in_language \<Sigma> G A \<sigma>"
  shows "paper_R_in_language \<Sigma> G (NApp F A) \<tau>"
  using head argument unfolding paper_R_in_language_def
  by (auto intro: paper_R_has_type.App)

definition paper_R_application_graph ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> (otype \<Rightarrow> 'v set) \<Rightarrow>
    ('v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'v) \<Rightarrow>
    otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "paper_R_application_graph \<Sigma> G D J \<sigma> \<tau> d a b \<longleftrightarrow>
    (\<exists>g F A. paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>) \<and>
      paper_R_in_language \<Sigma> G A \<sigma> \<and>
      named_env_typed D G g \<and> named_adequate g (NApp F A) \<and>
      J g F = d \<and> J g A = a \<and> J g (NApp F A) = b)"

definition paper_R_application ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> (otype \<Rightarrow> 'v set) \<Rightarrow>
    ('v named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'v) \<Rightarrow>
    otype \<Rightarrow> otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v" where
  "paper_R_application \<Sigma> G D J \<sigma> \<tau> d a =
    (SOME b. paper_R_application_graph \<Sigma> G D J \<sigma> \<tau> d a b)"

lemma paper_R_application_graphI:
  assumes head: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "paper_R_in_language \<Sigma> G A \<sigma>"
    and typed: "named_env_typed D G g" and adequate: "named_adequate g (NApp F A)"
    and head_value: "J g F = d" and arg_value: "J g A = a" and app_value: "J g (NApp F A) = b"
  shows "paper_R_application_graph \<Sigma> G D J \<sigma> \<tau> d a b"
  unfolding paper_R_application_graph_def
  by (rule exI[where x=g], rule exI[where x=F], rule exI[where x=A], intro conjI; fact)

lemma paper_R_application_graphE:
  assumes graph: "paper_R_application_graph \<Sigma> G D J \<sigma> \<tau> d a b"
  obtains g F A where
    "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)" "paper_R_in_language \<Sigma> G A \<sigma>"
    "named_env_typed D G g" "named_adequate g (NApp F A)"
    "J g F = d" "J g A = a" "J g (NApp F A) = b"
  using graph that unfolding paper_R_application_graph_def by blast

lemma paper_R_application_graph_arrow_type:
  assumes graph: "paper_R_application_graph \<Sigma> G D J \<sigma> \<tau> d a b"
  shows "paper_R_type (Arr \<sigma> \<tau>)"
proof -
  obtain g F A where head: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    by (rule paper_R_application_graphE[OF graph]; rule that; assumption)
  show ?thesis by (rule paper_R_language_result_type[OF head])
qed

end
