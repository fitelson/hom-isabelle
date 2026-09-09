theory Bacon_H_Forall_Distribution
  imports Bacon_H_Quantifier_Proof_Basics
begin

section \<open>Universal distribution as an H biconditional\<close>

text \<open>
  P ∨ ∀x:σ.A ↔ ∀x:σ.(P ∨ A), where x is not free in P.
  This is the material equivalence underlying Figure 4's universal
  distribution operation (Bacon–Dorr); compare Bacon Theorem 6.1.

  Isabelle representation: Γ ⊢ P:t and σ # Γ ⊢ A:t; shift P expresses
  the independence condition. UI at the fresh slot proves the forward
  direction by Gen. For the reverse direction, UI gives A from
  ∀x.(P ∨ A) ∧ ¬P; Gen and PC finish.

  Status: H only, with no Equivalence rule, C identity, model, or
  domain-inhabitation premise. The orientation is the represented
  Figure 4 P-first convention.
\<close>

theorem Hq_dist_disj_forall:
  assumes P: "\<Gamma> \<turnstile> P : Prop" and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H
    (Disj P (Forall \<sigma> A) \<longleftrightarrow>\<^sub>o Forall \<sigma> (Disj (shift P) A))"
proof -
  let ?Q = "Forall \<sigma> A"
  let ?B = "Disj (shift P) A"
  let ?R = "Forall \<sigma> ?B"
  let ?S = "Disj P ?Q"
  have qt: "\<Gamma> \<turnstile> ?Q : Prop" by (rule has_type.Forall[OF A])
  have spt: "\<sigma> # \<Gamma> \<turnstile> shift P : Prop" by (rule weakening_front[OF P])
  have bt: "\<sigma> # \<Gamma> \<turnstile> ?B : Prop" by (rule has_type.Disj[OF spt A])
  have rt: "\<Gamma> \<turnstile> ?R : Prop" by (rule has_type.Forall[OF bt])
  have st: "\<Gamma> \<turnstile> ?S : Prop" by (rule has_type.Disj[OF P qt])
  have sst: "\<sigma> # \<Gamma> \<turnstile> shift ?S : Prop" by (rule weakening_front[OF st])
  have forward_open: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp (shift ?S) ?B"
  proof (rule Hq_PC_consequence[OF Hq_UI_here[OF A] has_type.Imp[OF sst bt]])
    show "\<And>v. prop_eval v (Imp (shift ?Q) A) \<Longrightarrow>
      prop_eval v (Imp (shift ?S) ?B)"
      by (simp only: shift_def rename.simps prop_eval.simps; blast)
  qed
  have forward: "\<Gamma> \<turnstile>\<^sub>H Imp ?S ?R"
    by (rule H_proves.Gen[OF st bt forward_open])

  let ?D = "Conj ?R (Neg P)"
  have dt: "\<Gamma> \<turnstile> ?D : Prop" by (rule has_type.Conj[OF rt has_type.Neg[OF P]])
  have sdt: "\<sigma> # \<Gamma> \<turnstile> shift ?D : Prop" by (rule weakening_front[OF dt])
  have reverse_open: "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp (shift ?D) A"
  proof (rule Hq_PC_consequence[OF Hq_UI_here[OF bt] has_type.Imp[OF sdt A]])
    show "\<And>v. prop_eval v (Imp (shift ?R) ?B) \<Longrightarrow>
      prop_eval v (Imp (shift ?D) A)"
      by (simp only: shift_def rename.simps prop_eval.simps; blast)
  qed
  have quantified: "\<Gamma> \<turnstile>\<^sub>H Imp ?D ?Q"
    by (rule H_proves.Gen[OF dt A reverse_open])
  have reverse: "\<Gamma> \<turnstile>\<^sub>H Imp ?R ?S"
  proof (rule Hq_PC_consequence[OF quantified has_type.Imp[OF rt st]])
    show "\<And>v. prop_eval v (Imp ?D ?Q) \<Longrightarrow> prop_eval v (Imp ?R ?S)"
      by (simp only: prop_eval.simps; blast)
  qed
  show ?thesis by (rule Hq_iff_intro[OF st rt forward reverse])
qed

corollary Hq_dist_disj_forall_predicate:
  assumes F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop" and P: "\<Gamma> \<turnstile> P : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H
    (Disj P (Forall \<sigma> (App (shift F) (Var 0))) \<longleftrightarrow>\<^sub>o
      Forall \<sigma> (Disj (shift P) (App (shift F) (Var 0))))"
  by (rule Hq_dist_disj_forall[OF P Hq_predicate_body_type[OF F]])

end
