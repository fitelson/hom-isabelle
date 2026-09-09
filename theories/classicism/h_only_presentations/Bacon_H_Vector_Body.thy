theory Bacon_H_Vector_Body
  imports Bacon_C_Equivalence_Development.Bacon_C_Vector_Beta_Evaluation
begin

section \<open>Logical equivalence of abstraction bodies and their applications\<close>

text \<open>
  If H proves A ↔ B, then H proves
  (λv̄.A)v̄ ↔ (λv̄.B)v̄. This supplies the premise of Logical
  Equivalence for two explicitly displayed abstractions (Bacon Theorem 6.1,
  pp.126–127). It uses contextual β and propositional reasoning in H.

  Isabelle representation: Δ lists the de Bruijn slots from inner to
  outer, so the applications use rev(fresh_vars |Δ|). The imported
  deabstraction theorem has only typing premises and a syntactic βη
  conclusion. Its C-prefixed name does not license a C inference here.

  Scope: represented full-F syntax and unrestricted string constants.
  The proof below concludes H theoremhood, not identity or C theoremhood.
  A separate syntax bridge connects these older structural operations to
  the independent H-only presentation's operations.
\<close>

theorem H_vector_body_logical_equivalence:
  assumes A: "\<Delta> @ \<Gamma> \<turnstile> A : Prop"
    and B: "\<Delta> @ \<Gamma> \<turnstile> B : Prop"
    and equivalent: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Delta> @ \<Gamma> \<turnstile>\<^sub>H
    (app_vec (C_vector_raise (length \<Delta>) (C_abstract_prefix \<Delta> A))
       (rev (fresh_vars (length \<Delta>)))
      \<longleftrightarrow>\<^sub>o
     app_vec (C_vector_raise (length \<Delta>) (C_abstract_prefix \<Delta> B))
       (rev (fresh_vars (length \<Delta>))))"
proof -
  let ?FA = "app_vec (C_vector_raise (length \<Delta>) (C_abstract_prefix \<Delta> A))
    (rev (fresh_vars (length \<Delta>)))"
  let ?FB = "app_vec (C_vector_raise (length \<Delta>) (C_abstract_prefix \<Delta> B))
    (rev (fresh_vars (length \<Delta>)))"
  have FA: "\<Delta> @ \<Gamma> \<turnstile> ?FA : Prop" by (rule C_vector_deabstract_type[OF A])
  have FB: "\<Delta> @ \<Gamma> \<turnstile> ?FB : Prop" by (rule C_vector_deabstract_type[OF B])
  have first: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>H (?FA \<longleftrightarrow>\<^sub>o A)"
    by (rule H_beta_eta_equiv[OF C_vector_deabstract_beta_eta[OF A]])
  have last: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>H (B \<longleftrightarrow>\<^sub>o ?FB)"
    by (rule H_beta_eta_equiv[OF beta_eta_equiv.Sym[OF C_vector_deabstract_beta_eta[OF B]]])
  have middle: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>H (?FA \<longleftrightarrow>\<^sub>o B)"
    by (rule H_bicond_trans[OF FA A B first equivalent])
  show ?thesis by (rule H_bicond_trans[OF FA B FB middle last])
qed

end
