theory Bacon_C_Appendix_A3
  imports Bacon_C_Appendix_A2 Bacon_C_Equivalence_From_Vector_Truth
begin

section \<open>Appendix A.3: Equivalence in axiom-based C\<close>

text \<open>
  From ⊢C A ↔ B, infer ⊢C (λv̄.A) = (λv̄.B).
  Source: Bacon–Dorr Proposition A.3, p.67, using A.2;
  Bacon Theorem 6.1, pp.126–127.

  Isabelle representation: A.2 identifies the abstraction of the
  biconditional with the constant-truth abstraction. The checked Boolean
  consequence then identifies the abstractions of A and B. Δ lists the
  de Bruijn slots from inner to outer; its reversed type list gives the
  displayed function type. Empty and mixed-type vectors are included.

  Scope: the represented axiom-based C calculus over full F types and its
  unrestricted typed-string constant stock. Literal source vocabulary and
  named-variable proof correspondence remain separate. This derivation
  never imports an Equivalence inference from CE or CEV. Identifying those
  existing presentation judgments requires separate proof inductions and,
  for CEV, checking the order of its variable vector.
\<close>

theorem C_Appendix_A3:
  assumes derivation: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>C (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop)
    (C_abstract_prefix \<Delta> A) (C_abstract_prefix \<Delta> B)"
  by (rule C_vector_biconditional_truth_identity[OF C_Appendix_A2[OF derivation]])

corollary C_Appendix_A3_zeroary:
  assumes derivation: "\<Gamma> \<turnstile>\<^sub>C (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop A B"
proof -
  have premise: "[] @ \<Gamma> \<turnstile>\<^sub>C (A \<longleftrightarrow>\<^sub>o B)" using derivation by simp
  show ?thesis using C_Appendix_A3[OF premise] by simp
qed

end
