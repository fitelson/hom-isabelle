theory Bacon_C_PC_Boolean_Equivalence
  imports Bacon_C_PC_Single_Abstraction
begin

section \<open>Tautological Boolean equivalence beneath one abstraction\<close>

text \<open>
  If A ↔ B is a propositional tautology, then ⊢C (λv.A) = (λv.B).
  PC gives (λv.(A → B)) = (λv.⊤₀) and the converse implication.
  The Boolean identity A ∧ (A → B) = A ∧ B yields A ≼ B, and
  conversely B ≼ A; antisymmetry gives the required identity.
  Source role: Boolean substitution in the PC case of Bacon–Dorr
  Appendix A.2(i), p.65, using the Boolean identities in Figure 3, p.10.

  Isabelle representation.  C_BA_le is the previously derived meet order
  on one-variable abstractions.  Every equality below is proved in C.
  The premise is prop_tautology, not C theoremhood of a biconditional:
  no general C Equivalence, CE/CEV rule, or arbitrary theorem abstraction
  is used or asserted.
\<close>

lemma C_PC_conj_material_implication:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Imp A B))) (Lam \<sigma> (Conj A B))"
proof -
  have NA: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have AB: "\<sigma> # \<Gamma> \<turnstile> Conj A B : Prop" by (rule has_type.Conj[OF A B])
  have material: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Imp A B))) (Lam \<sigma> (Conj A (Disj (Neg A) B)))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF A] C_PC_lambda_material_imp[OF A B]])
  have distributed: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Disj (Neg A) B))) (Lam \<sigma> (Disj (Conj A (Neg A)) (Conj A B)))"
    by (rule C_boolean_lambda_conj_distributes[OF A NA B])
  have reduced: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Conj A (Neg A)) (Conj A B))) (Lam \<sigma> (Disj ObjFalse (Conj A B)))"
    by (rule C_BA_disj_congruence[OF C_boolean_lambda_contradiction_ObjFalse[OF A]
      C_boolean_lambda_reflexive[OF AB]])
  show ?thesis by (rule C_A1_trans[OF material C_A1_trans[OF distributed
    C_A1_trans[OF reduced C_boolean_lambda_disj_false_left[OF AB]]]])
qed

lemma C_PC_tautological_implication_le:
  assumes tautology: "prop_tautology (\<sigma> # \<Gamma>) (Imp A B)"
  shows "C_BA_le \<Gamma> \<sigma> A B"
proof -
  have formula: "\<sigma> # \<Gamma> \<turnstile> Imp A B : Prop"
    using tautology unfolding prop_tautology_def by (rule conjunct1)
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    using formula by (auto elim: has_type.cases)
  have implication: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Imp A B)) (Lam \<sigma> ObjTrue)"
    by (rule C_PC_single_abstraction[OF tautology])
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Imp A B))) (Lam \<sigma> (Conj A ObjTrue))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF A] implication])
  show ?thesis unfolding C_BA_le_def
    by (rule C_A1_trans[OF C_A1_sym[OF C_PC_conj_material_implication[OF A B]]
      C_A1_trans[OF replacement C_boolean_lambda_conj_true_right[OF A]]])
qed

lemma C_PC_tautological_biconditional_data:
  assumes tautology: "prop_tautology \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> B : Prop"
    and "prop_tautology \<Gamma> (Imp A B)" and "prop_tautology \<Gamma> (Imp B A)"
proof -
  have formula: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using tautology unfolding prop_tautology_def by (rule conjunct1)
  have A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    using formula by (auto elim: has_type.cases)
  have valid: "\<forall>w. prop_eval w (A \<longleftrightarrow>\<^sub>o B)"
    using tautology unfolding prop_tautology_def by (rule conjunct2)
  have forward: "\<forall>w. prop_eval w (Imp A B)" and backward: "\<forall>w. prop_eval w (Imp B A)"
    using valid by (simp only: prop_eval.simps; blast)+
  show "\<Gamma> \<turnstile> A : Prop" by (rule A)
  show "\<Gamma> \<turnstile> B : Prop" by (rule B)
  show "prop_tautology \<Gamma> (Imp A B)" unfolding prop_tautology_def
    by (rule conjI[OF has_type.Imp[OF A B] forward])
  show "prop_tautology \<Gamma> (Imp B A)" unfolding prop_tautology_def
    by (rule conjI[OF has_type.Imp[OF B A] backward])
qed

theorem C_PC_boolean_equivalence_single_abstraction:
  assumes tautology: "prop_tautology (\<sigma> # \<Gamma>) (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> B)"
proof -
  note parts = C_PC_tautological_biconditional_data[OF tautology]
  have AB: "C_BA_le \<Gamma> \<sigma> A B" by (rule C_PC_tautological_implication_le[OF parts(3)])
  have BA: "C_BA_le \<Gamma> \<sigma> B A" by (rule C_PC_tautological_implication_le[OF parts(4)])
  show ?thesis by (rule C_BA_le_antisym[OF parts(1,2) AB BA])
qed

end
