theory Bacon_Source_ZF_Function_Graphs
  imports "HOL-ZF.HOLZF"
begin

section \<open>Actual function graphs on specified set-theoretic domains\<close>

text \<open>
  For sets A and B in HOL-ZF, every function A→B has an actual
  graph Λx∈A.f(x), and application recovers its value on A.
  This is representation groundwork for the typed carriers of
  Bacon–Dorr Definition 3.18, p.55, not an action premodel itself.

  Metalogic: this leaf is relative to the standard HOL-ZF set axioms,
  unlike the separate pure-HOL H/C soundness proofs.
  No additional local axiom is introduced. A and B are specified
  ZF sets: there is no assertion that arbitrary HOL sets, or the
  entire HOL type ZF, can be packaged as an element of ZF.

  Total HOL functions are fixed to undefined outside explode(A).
  That only removes irrelevant extensions; it does not restrict
  their behavior on A or substitute a PER domain for a function space.
\<close>

definition paper_ZF_functions :: "ZF \<Rightarrow> ZF \<Rightarrow> (ZF \<Rightarrow> ZF) set" where
  "paper_ZF_functions A B = {f.
    (\<forall>x. \<not> Elem x A \<longrightarrow> f x = undefined) \<and>
    (\<forall>x. Elem x A \<longrightarrow> Elem (f x) B)}"

definition paper_ZF_decode_function :: "ZF \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_ZF_decode_function A F x = (if Elem x A then app F x else undefined)"

lemma paper_ZF_encode_function_type:
  assumes member: "f \<in> paper_ZF_functions A B"
  shows "Lambda A f \<in> explode (Fun A B)"
  using member by (auto simp: paper_ZF_functions_def explode_Elem Elem_Lambda_Fun)

lemma paper_ZF_decode_function_type:
  assumes graph: "F \<in> explode (Fun A B)"
  shows "paper_ZF_decode_function A F \<in> paper_ZF_functions A B"
proof -
  have member: "Elem F (Fun A B)" using graph by (simp only: explode_Elem)
  obtain f where shape: "F = Lambda A f" using Elem_Fun_Lambda[OF member] by blast
  have maps: "\<forall>x. Elem x A \<longrightarrow> Elem (f x) B"
    using member by (simp only: shape Elem_Lambda_Fun; blast)
  show ?thesis using maps
    by (auto simp: paper_ZF_functions_def paper_ZF_decode_function_def shape Lambda_app)
qed

theorem paper_ZF_decode_encode_function:
  assumes member: "f \<in> paper_ZF_functions A B"
  shows "paper_ZF_decode_function A (Lambda A f) = f"
proof (rule ext)
  fix x
  show "paper_ZF_decode_function A (Lambda A f) x = f x"
    using member
    by (cases "Elem x A") (auto simp: paper_ZF_decode_function_def paper_ZF_functions_def Lambda_app)
qed

theorem paper_ZF_encode_decode_function:
  assumes graph: "F \<in> explode (Fun A B)"
  shows "Lambda A (paper_ZF_decode_function A F) = F"
proof -
  have member: "Elem F (Fun A B)" using graph by (simp only: explode_Elem)
  obtain f where shape: "F = Lambda A f" using Elem_Fun_Lambda[OF member] by blast
  show ?thesis by (simp add: shape Lambda_ext paper_ZF_decode_function_def Lambda_app)
qed

lemma paper_ZF_function_graph_injective:
  "inj_on (Lambda A) (paper_ZF_functions A B)"
proof (rule inj_onI)
  fix f g
  assume fm: "f \<in> paper_ZF_functions A B" and gm: "g \<in> paper_ZF_functions A B"
    and same: "Lambda A f = Lambda A g"
  have decoded: "paper_ZF_decode_function A (Lambda A f) =
    paper_ZF_decode_function A (Lambda A g)" by (simp only: same)
  show "f = g" using decoded
    by (simp only: paper_ZF_decode_encode_function[OF fm] paper_ZF_decode_encode_function[OF gm])
qed

theorem paper_ZF_function_graph_bijection:
  "bij_betw (Lambda A) (paper_ZF_functions A B) (explode (Fun A B))"
proof (unfold bij_betw_def, rule conjI[OF paper_ZF_function_graph_injective])
  show "image (Lambda A) (paper_ZF_functions A B) = explode (Fun A B)"
  proof
    show "image (Lambda A) (paper_ZF_functions A B) \<subseteq> explode (Fun A B)"
      using paper_ZF_encode_function_type by blast
    show "explode (Fun A B) \<subseteq> image (Lambda A) (paper_ZF_functions A B)"
    proof
      fix F
      assume graph: "F \<in> explode (Fun A B)"
      have decoded: "paper_ZF_decode_function A F \<in> paper_ZF_functions A B"
        by (rule paper_ZF_decode_function_type[OF graph])
      have rebuilt: "Lambda A (paper_ZF_decode_function A F) = F"
        by (rule paper_ZF_encode_decode_function[OF graph])
      have in_image: "Lambda A (paper_ZF_decode_function A F) \<in>
        image (Lambda A) (paper_ZF_functions A B)"
        by (rule imageI[OF decoded])
      show "F \<in> image (Lambda A) (paper_ZF_functions A B)"
        using in_image by (simp only: rebuilt)
    qed
  qed
qed

end
