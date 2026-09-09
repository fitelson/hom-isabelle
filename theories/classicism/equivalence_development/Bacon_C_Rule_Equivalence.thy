theory Bacon_C_Rule_Equivalence
  imports Bacon_C_Appendix_A3 Bacon_C_Vector_Eta_Contraction
begin

section \<open>The full Rule of Equivalence in source argument order\<close>

text \<open>
  If ⊢C Fv₁…vₙ ↔ Gv₁…vₙ, where the displayed variables are
  distinct and absent from F,G, then ⊢C F = G.
  Sources: Bacon Theorem 6.1 and Bacon–Dorr Appendix A.

  Isabelle representation: F and G are typed in Γ, then raised beneath
  the fresh prefix Δ. The argument list is reversed relative to the
  de Bruijn context, so its order is the function's arrow order.
  A.3 identifies the two abstractions; typed vector η identifies them
  with F and G. This includes zero arguments and mixed argument types.

  Status: an admissible C-only inference, not a new constructor. Adapting
  the older CEV variable ordering remains a separate syntactic bridge.
\<close>

theorem C_rule_equivalence:
  assumes F: "\<Gamma> \<turnstile> F : arrow_type (rev \<Delta>) Prop"
    and G: "\<Gamma> \<turnstile> G : arrow_type (rev \<Delta>) Prop"
    and premise: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>C
      (app_vec (C_vector_raise (length \<Delta>) F) (rev (fresh_vars (length \<Delta>)))
      \<longleftrightarrow>\<^sub>o
      app_vec (C_vector_raise (length \<Delta>) G) (rev (fresh_vars (length \<Delta>))))"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (arrow_type (rev \<Delta>) Prop) F G"
  by (rule C_A1_transport[OF C_Appendix_A3[OF premise]
    C_vector_eta_identity[OF F] C_vector_eta_identity[OF G]])

end
