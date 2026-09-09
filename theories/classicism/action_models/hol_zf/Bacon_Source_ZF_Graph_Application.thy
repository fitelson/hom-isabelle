theory Bacon_Source_ZF_Graph_Application
  imports Bacon_Source_ZF_Dependent_Function_Graphs
begin

section \<open>Option-valued application of an actual function graph\<close>

text \<open>
  F(x) is defined when F is a function graph and x∈dom(F).
  Source role: Definition 3.19 and footnote 78(i), p.56.
  The option None marks failure of either guard. This is not a
  totality assertion about a term interpretation or a logical model.
  All graph facts are relative to the standard HOL-ZF foundation.
\<close>

definition paper_ZF_graph_apply :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF option" where
  "paper_ZF_graph_apply F x = (if isFun F \<and> Elem x (Domain F) then Some (app F x) else None)"

lemma paper_ZF_graph_apply_defined_value:
  assumes function_graph: "isFun F" and defined_input: "Elem x (Domain F)"
  shows "paper_ZF_graph_apply F x = Some (app F x)"
  by (simp only: paper_ZF_graph_apply_def function_graph defined_input; simp)

lemma paper_ZF_graph_apply_None_iff:
  "paper_ZF_graph_apply F x = None \<longleftrightarrow> \<not> isFun F \<or> \<not> Elem x (Domain F)"
  by (auto simp: paper_ZF_graph_apply_def)

lemma paper_ZF_graph_apply_Some_iff:
  "paper_ZF_graph_apply F x = Some y \<longleftrightarrow>
    isFun F \<and> Elem x (Domain F) \<and> y = app F x"
  by (auto simp: paper_ZF_graph_apply_def split: if_splits)

lemma paper_ZF_function_graph_domain:
  assumes graph: "F \<in> explode (Fun A B)"
  shows "isFun F \<and> Domain F = A"
proof -
  have member: "Elem F (Fun A B)" using graph by (simp only: explode_Elem)
  obtain f where shape: "F = Lambda A f" using Elem_Fun_Lambda[OF member] by blast
  show ?thesis by (simp only: shape isFun_Lambda domain_Lambda; simp)
qed

lemma paper_ZF_Pi_function_graph:
  assumes graph: "F \<in> explode (paper_ZF_Pi A B)"
  shows "isFun F \<and> Domain F = A"
  by (rule paper_ZF_function_graph_domain[OF paper_ZF_Pi_graph[OF graph]])

end
