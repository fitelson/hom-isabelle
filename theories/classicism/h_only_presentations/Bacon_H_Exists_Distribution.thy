theory Bacon_H_Exists_Distribution
  imports Bacon_H_Quantifier_Proof_Basics
begin

section \<open>Existential distribution as an H biconditional\<close>

text \<open>
  P ∧ ∃x:σ.A ↔ ∃x:σ.(P ∧ A), where x is not free in P.
  This is the material equivalence underlying Figure 4's existential
  distribution operation (Bacon–Dorr); compare Bacon Theorem 6.1.

  Isabelle representation: P is typed in Γ and A in σ # Γ; shift P
  carries the independent proposition into the binder. EG at the new
  slot and PC supply the premises for Inst in both directions.

  Status: H only. No C/CE/CEV result, model, Equivalence inference, or
  existence axiom is used. These are not identities of the λ-operations.
\<close>

theorem Hq_dist_conj_exists:
  assumes P: "\<Gamma> \<turnstile> P : Prop" and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H
    (Conj P (Exists \<sigma> A) \<longleftrightarrow>\<^sub>o Exists \<sigma> (Conj (shift P) A))"
proof -
  let ?Q = "Exists \<sigma> A"
  let ?B = "Conj (shift P) A"
  let ?R = "Exists \<sigma> ?B"
  let ?S = "Conj P ?Q"
  have qt: "\<Gamma> \<turnstile> ?Q : Prop" by (rule has_type.Exists[OF A])
  have spt: "\<sigma> # \<Gamma> \<turnstile> shift P : Prop" by (rule weakening_front[OF P])
  have bt: "\<sigma> # \<Gamma> \<turnstile> ?B : Prop" by (rule has_type.Conj[OF spt A])
  have rt: "\<Gamma> \<turnstile> ?R : Prop" by (rule has_type.Exists[OF bt])
  have st: "\<Gamma> \<turnstile> ?S : Prop" by (rule has_type.Conj[OF P qt])
  let ?U = "Imp P ?R"
  have ut: "\<Gamma> \<turnstile> ?U : Prop" by (rule has_type.Imp[OF P rt])
  have sut: "\<sigma> # \<Gamma> \<turnstile> shift ?U : Prop" by (rule weakening_front[OF ut])
  have forward_open: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp A (shift ?U)"
  proof (rule Hq_PC_consequence[OF Hq_EG_here[OF bt] has_type.Imp[OF A sut]])
    show "\<And>v. prop_eval v (Imp ?B (shift ?R)) \<Longrightarrow>
      prop_eval v (Imp A (shift ?U))"
      by (simp only: shift_def rename.simps prop_eval.simps; blast)
  qed
  have instantiated: "\<Gamma> \<turnstile>\<^sub>H Imp ?Q ?U"
    by (rule H_proves.Inst[OF A ut forward_open])
  have forward: "\<Gamma> \<turnstile>\<^sub>H Imp ?S ?R"
  proof (rule Hq_PC_consequence[OF instantiated has_type.Imp[OF st rt]])
    show "\<And>v. prop_eval v (Imp ?Q ?U) \<Longrightarrow> prop_eval v (Imp ?S ?R)"
      by (simp only: prop_eval.simps; blast)
  qed

  have sst: "\<sigma> # \<Gamma> \<turnstile> shift ?S : Prop" by (rule weakening_front[OF st])
  have reverse_open: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp ?B (shift ?S)"
  proof (rule Hq_PC_consequence[OF Hq_EG_here[OF A] has_type.Imp[OF bt sst]])
    show "\<And>v. prop_eval v (Imp A (shift ?Q)) \<Longrightarrow>
      prop_eval v (Imp ?B (shift ?S))"
      by (simp only: shift_def rename.simps prop_eval.simps; blast)
  qed
  have reverse: "\<Gamma> \<turnstile>\<^sub>H Imp ?R ?S"
    by (rule H_proves.Inst[OF bt st reverse_open])
  show ?thesis by (rule Hq_iff_intro[OF st rt forward reverse])
qed

corollary Hq_dist_conj_exists_predicate:
  assumes F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop" and P: "\<Gamma> \<turnstile> P : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H
    (Conj P (Exists \<sigma> (App (shift F) (Var 0))) \<longleftrightarrow>\<^sub>o
      Exists \<sigma> (Conj (shift P) (App (shift F) (Var 0))))"
  by (rule Hq_dist_conj_exists[OF P Hq_predicate_body_type[OF F]])

end
