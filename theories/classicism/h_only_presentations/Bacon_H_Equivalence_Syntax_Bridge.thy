theory Bacon_H_Equivalence_Syntax_Bridge
  imports Bacon_H_Equivalence_Presentations Bacon_H_Vector_Body
begin

section \<open>The independent H-only syntax and the checked vector operations\<close>

text \<open>
  The independent H-only presentations use their own structural arrow,
  raising, and application operations so their definitions need not import
  Classicism. These operations represent the same typed variable vectors
  used in the checked Appendix A development.

  Isabelle representation: the following equations are structural inductions,
  not assumptions about theoremhood. H_rule_args and the older reversed
  fresh-variable list have the same order, including mixed types and the
  empty vector. No C, CE, or CEV inference is used here.
\<close>

lemma H_rule_arrow_bridge:
  "H_rule_arrow \<sigma>s \<tau> = arrow_type \<sigma>s \<tau>"
  by (induction \<sigma>s) simp_all

lemma H_rule_raise_bridge:
  "H_rule_raise n F = C_vector_raise n F"
  by (induction n) (simp_all add: shift_def)

lemma H_rule_app_vec_bridge:
  "H_rule_app_vec F xs = app_vec F xs"
  by (induction xs arbitrary: F) simp_all

lemma H_rule_args_bridge:
  "H_rule_args n = rev (fresh_vars n)"
  by (simp only: H_rule_args_def fresh_vars_def)

lemma H_rule_body_bridge:
  "H_rule_body \<Delta> F G =
    (app_vec (C_vector_raise (length \<Delta>) F) (rev (fresh_vars (length \<Delta>)))
      \<longleftrightarrow>\<^sub>o
     app_vec (C_vector_raise (length \<Delta>) G) (rev (fresh_vars (length \<Delta>))))"
  by (simp only: H_rule_body_def H_rule_arrow_bridge H_rule_raise_bridge
    H_rule_app_vec_bridge H_rule_args_bridge)

section \<open>Logical Equivalence for displayed abstractions\<close>

text \<open>
  From an H proof of A ↔ B, Logical Equivalence yields the identity
  (λv̄.A) = (λv̄.B). The H proof is an eligibility condition for an
  axiom of H + Logical Equivalence, not a proof in that stronger calculus.
  Source: Bacon Theorem 6.1, pp.126–127.

  The beta computations are supplied by H_vector_body_logical_equivalence.
  This is the step used to derive each closed Classical Identity from its
  ordinary H biconditional, rather than adding those identities as axioms.
\<close>

theorem HLE_abstraction:
  assumes A: "\<Delta> @ \<Gamma> \<turnstile> A : Prop"
    and B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop"
    and equivalent: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
  shows "HLE_proves \<Gamma> (Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> B))"
proof -
  have F: "\<Gamma> \<turnstile> C_abstract_prefix \<Delta> A : H_rule_arrow (rev \<Delta>) Prop"
    using C_abstract_prefix_type[OF A] by (simp only: H_rule_arrow_bridge)
  have G: "\<Gamma> \<turnstile> C_abstract_prefix \<Delta> B : H_rule_arrow (rev \<Delta>) Prop"
    using C_abstract_prefix_type[OF B] by (simp only: H_rule_arrow_bridge)
  have body: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>H
    H_rule_body \<Delta> (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> B)"
    using H_vector_body_logical_equivalence[OF A B equivalent] by (simp only: H_rule_body_bridge)
  show ?thesis using HLE_proves.LogicalEquivalence[OF F G body]
    by (simp only: H_rule_arrow_bridge)
qed

corollary HLE_PC_abstraction:
  assumes pc: "prop_tautology (\<Delta> @ \<Gamma>) (A \<longleftrightarrow>\<^sub>o B)"
  shows "HLE_proves \<Gamma> (Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> B))"
proof -
  have typed: "\<Delta> @ \<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using pc unfolding prop_tautology_def by (rule conjunct1)
  have A: "\<Delta> @ \<Gamma> \<turnstile> A : Prop" and B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop"
    using typed by (auto elim: has_type.cases)
  show ?thesis by (rule HLE_abstraction[OF A B H_proves.PC[OF pc]])
qed

end
