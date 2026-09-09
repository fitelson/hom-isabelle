theory Bacon_Source_ZF_Dependent_Function_Graphs
  imports Bacon_Source_ZF_Function_Graphs
begin

section \<open>Dependent functions over an explicit set-theoretic domain\<close>

text \<open>
  For A∈ZF and B:A→ZF, the bound ⋃{B(x) | x∈A} is
  Sum(Repl A B). The dependent function set ∏x∈A.B(x) is
  separated from the actual function set with that bound.
  Source role: dependent arrow/argument fibers in Example 3.16
  and the concrete carriers of Definition 3.18, pp.54–55.

  This leaf is relative to the standard HOL-ZF axioms. It adds
  no local axiom or assumed decoding locale. A and every B(x)
  are explicit ZF sets; no arbitrary HOL-set representability is
  asserted. HOL functions are normalized outside explode(A).
  Empty domains and empty fibers are allowed without an inhabitance
  assumption. Encoding and decoding are the existing Lambda A
  and paper_ZF_decode_function A.
\<close>

definition paper_ZF_Pi :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> ZF" where
  "paper_ZF_Pi A B = Sep (Fun A (Sum (Repl A B)))
    (\<lambda>F. \<forall>x. Elem x A \<longrightarrow> Elem (app F x) (B x))"

definition paper_ZF_dependent_functions :: "ZF \<Rightarrow> (ZF \<Rightarrow> ZF) \<Rightarrow> (ZF \<Rightarrow> ZF) set" where
  "paper_ZF_dependent_functions A B = {f.
    (\<forall>x. \<not> Elem x A \<longrightarrow> f x = undefined) \<and>
    (\<forall>x. Elem x A \<longrightarrow> Elem (f x) (B x))}"

lemma paper_ZF_dependent_bound_member:
  assumes index: "Elem x A" and fiber_value: "Elem y (B x)"
  shows "Elem y (Sum (Repl A B))"
proof -
  have fiber: "Elem (B x) (Repl A B)"
    by (simp only: Repl; rule exI[where x=x], rule conjI[OF index refl])
  show ?thesis
    by (simp only: Sum; rule exI[where x="B x"], rule conjI[OF fiber_value fiber])
qed

lemma paper_ZF_Pi_member:
  "F \<in> explode (paper_ZF_Pi A B) \<longleftrightarrow>
    F \<in> explode (Fun A (Sum (Repl A B))) \<and>
    (\<forall>x. Elem x A \<longrightarrow> Elem (app F x) (B x))"
  by (simp only: paper_ZF_Pi_def explode_Elem Sep)

lemma paper_ZF_Pi_graph:
  "F \<in> explode (paper_ZF_Pi A B) \<Longrightarrow> F \<in> explode (Fun A (Sum (Repl A B)))"
  by (simp only: paper_ZF_Pi_member; blast)

lemma paper_ZF_Pi_value:
  assumes graph: "F \<in> explode (paper_ZF_Pi A B)" and index: "Elem x A"
  shows "Elem (app F x) (B x)"
  using graph index by (simp only: paper_ZF_Pi_member; blast)

lemma paper_ZF_dependent_function_value:
  assumes member: "f \<in> paper_ZF_dependent_functions A B" and index: "Elem x A"
  shows "Elem (f x) (B x)"
  using member index unfolding paper_ZF_dependent_functions_def by blast

lemma paper_ZF_dependent_function_normal:
  assumes member: "f \<in> paper_ZF_dependent_functions A B" and outside: "\<not> Elem x A"
  shows "f x = undefined"
  using member outside unfolding paper_ZF_dependent_functions_def by blast

lemma paper_ZF_dependent_function_bounded:
  assumes member: "f \<in> paper_ZF_dependent_functions A B"
  shows "f \<in> paper_ZF_functions A (Sum (Repl A B))"
proof (unfold paper_ZF_functions_def, rule CollectI, rule conjI)
  show "\<forall>x. \<not> Elem x A \<longrightarrow> f x = undefined"
    by (intro allI impI, rule paper_ZF_dependent_function_normal[OF member], assumption)
next
  show "\<forall>x. Elem x A \<longrightarrow> Elem (f x) (Sum (Repl A B))"
  proof (intro allI impI)
    fix x
    assume index: "Elem x A"
    show "Elem (f x) (Sum (Repl A B))"
      by (rule paper_ZF_dependent_bound_member[where A=A and B=B and x=x and y="f x",
        OF index paper_ZF_dependent_function_value[OF member index]])
  qed
qed

section \<open>Encoding and decoding preserve the dependent fibers\<close>

lemma paper_ZF_encode_dependent_function_type:
  assumes member: "f \<in> paper_ZF_dependent_functions A B"
  shows "Lambda A f \<in> explode (paper_ZF_Pi A B)"
proof (rule iffD2[OF paper_ZF_Pi_member], rule conjI)
  show "Lambda A f \<in> explode (Fun A (Sum (Repl A B)))"
    by (rule paper_ZF_encode_function_type[OF paper_ZF_dependent_function_bounded[OF member]])
next
  show "\<forall>x. Elem x A \<longrightarrow> Elem (app (Lambda A f) x) (B x)"
  proof (intro allI impI)
    fix x
    assume index: "Elem x A"
    show "Elem (app (Lambda A f) x) (B x)"
      by (simp only: Lambda_app[OF index]; rule paper_ZF_dependent_function_value[OF member index])
  qed
qed

lemma paper_ZF_decode_dependent_function_type:
  assumes graph: "F \<in> explode (paper_ZF_Pi A B)"
  shows "paper_ZF_decode_function A F \<in> paper_ZF_dependent_functions A B"
proof (unfold paper_ZF_dependent_functions_def, rule CollectI, rule conjI)
  show "\<forall>x. \<not> Elem x A \<longrightarrow> paper_ZF_decode_function A F x = undefined"
    by (simp only: paper_ZF_decode_function_def; simp)
next
  show "\<forall>x. Elem x A \<longrightarrow> Elem (paper_ZF_decode_function A F x) (B x)"
  proof (intro allI impI)
    fix x
    assume index: "Elem x A"
    show "Elem (paper_ZF_decode_function A F x) (B x)"
      by (simp only: paper_ZF_decode_function_def if_P[OF index]; rule paper_ZF_Pi_value[OF graph index])
  qed
qed

theorem paper_ZF_decode_encode_dependent_function:
  assumes member: "f \<in> paper_ZF_dependent_functions A B"
  shows "paper_ZF_decode_function A (Lambda A f) = f"
  by (rule paper_ZF_decode_encode_function[OF paper_ZF_dependent_function_bounded[OF member]])

theorem paper_ZF_encode_decode_dependent_function:
  assumes graph: "F \<in> explode (paper_ZF_Pi A B)"
  shows "Lambda A (paper_ZF_decode_function A F) = F"
  by (rule paper_ZF_encode_decode_function[OF paper_ZF_Pi_graph[OF graph]])

section \<open>The dependent graph encoding is an actual bijection\<close>

lemma paper_ZF_dependent_function_graph_injective:
  "inj_on (Lambda A) (paper_ZF_dependent_functions A B)"
proof (rule inj_onI)
  fix f g
  assume fm: "f \<in> paper_ZF_dependent_functions A B" and gm: "g \<in> paper_ZF_dependent_functions A B"
    and equal: "Lambda A f = Lambda A g"
  have decoded: "paper_ZF_decode_function A (Lambda A f) = paper_ZF_decode_function A (Lambda A g)"
    by (simp only: equal)
  show "f = g" using decoded by (simp only:
    paper_ZF_decode_encode_dependent_function[OF fm] paper_ZF_decode_encode_dependent_function[OF gm])
qed

theorem paper_ZF_dependent_function_graph_bijection:
  "bij_betw (Lambda A) (paper_ZF_dependent_functions A B) (explode (paper_ZF_Pi A B))"
proof (unfold bij_betw_def, rule conjI[OF paper_ZF_dependent_function_graph_injective])
  show "image (Lambda A) (paper_ZF_dependent_functions A B) = explode (paper_ZF_Pi A B)"
  proof
    show "image (Lambda A) (paper_ZF_dependent_functions A B) \<subseteq> explode (paper_ZF_Pi A B)"
      using paper_ZF_encode_dependent_function_type by blast
  next
    show "explode (paper_ZF_Pi A B) \<subseteq> image (Lambda A) (paper_ZF_dependent_functions A B)"
    proof
      fix F
      assume graph: "F \<in> explode (paper_ZF_Pi A B)"
      have decoded: "paper_ZF_decode_function A F \<in> paper_ZF_dependent_functions A B"
        by (rule paper_ZF_decode_dependent_function_type[OF graph])
      have represented: "Lambda A (paper_ZF_decode_function A F) \<in>
        image (Lambda A) (paper_ZF_dependent_functions A B)" by (rule imageI[OF decoded])
      show "F \<in> image (Lambda A) (paper_ZF_dependent_functions A B)"
        using represented by (simp only: paper_ZF_encode_decode_dependent_function[OF graph])
    qed
  qed
qed

end
