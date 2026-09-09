theory Bacon_C_Boolean_Absorption
  imports Bacon_C_Boolean_Constants
begin

section \<open>Unconditional domination and absorption beneath λ\<close>

text \<open>
  We derive A ∨ ⊤₀ = ⊤₀, A ∧ ⊥₀ = ⊥₀,
  A ∧ (A ∨ B) = A, and A ∨ (A ∧ B) = A, all beneath λv.
  Source use: Bacon--Dorr Figure 3, p.10, towards the unconditional
  Boolean equational argument in Appendix A.2(i), p.65.

  Isabelle representation.  Typed C identities are composed at predicate
  type σ → t.  The short congruence helpers recover body typing from their
  identity premises; they add no new inference principle.
  Status.  A and B are arbitrary typed bodies, possibly depending on v.
  No atomic-constancy, Functionality, CE/CEV, or semantic premise occurs.
\<close>

lemma C_BA_conj_congruence:
  assumes AB: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> B)"
    and DE: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> D) (Lam \<sigma> E)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A D)) (Lam \<sigma> (Conj B E))"
proof -
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and D: "\<sigma> # \<Gamma> \<turnstile> D : Prop" and E: "\<sigma> # \<Gamma> \<turnstile> E : Prop"
    using C_proves_formula[OF AB] C_proves_formula[OF DE] by (auto elim: has_type.cases)
  have connective: "Conj = Conj \<or> Conj = Disj \<or> Conj = Imp" by simp
  show ?thesis by (rule C_PC_binary_lambda_congruence[OF connective A B D E AB DE])
qed

lemma C_BA_disj_congruence:
  assumes AB: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> B)"
    and DE: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> D) (Lam \<sigma> E)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A D)) (Lam \<sigma> (Disj B E))"
proof -
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and D: "\<sigma> # \<Gamma> \<turnstile> D : Prop" and E: "\<sigma> # \<Gamma> \<turnstile> E : Prop"
    using C_proves_formula[OF AB] C_proves_formula[OF DE] by (auto elim: has_type.cases)
  have connective: "Disj = Conj \<or> Disj = Disj \<or> Disj = Imp" by simp
  show ?thesis by (rule C_PC_binary_lambda_congruence[OF connective A B D E AB DE])
qed

subsection \<open>Domination without associativity\<close>

text \<open>
  Distribute A ∨ (⊤₀ ∧ ¬A).  Its left side reduces to ⊤₀; its right
  side (A ∨ ⊤₀) ∧ (A ∨ ¬A) reduces to A ∨ ⊤₀.  The dual calculation
  starts from A ∧ (⊥₀ ∨ ¬A).
  Status.  Neither calculation uses an associativity law.
\<close>

theorem C_boolean_lambda_disj_true_right:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A ObjTrue)) (Lam \<sigma> ObjTrue)"
proof -
  have NA: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have AT: "\<sigma> # \<Gamma> \<turnstile> Disj A ObjTrue : Prop"
    by (rule has_type.Disj[OF A typed_ObjTrue])
  have distribution: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A (Conj ObjTrue (Neg A))))
    (Lam \<sigma> (Conj (Disj A ObjTrue) (Disj A (Neg A))))"
    by (rule C_boolean_lambda_disj_distributes[OF A typed_ObjTrue NA])
  have left_step: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A (Conj ObjTrue (Neg A)))) (Lam \<sigma> (Disj A (Neg A)))"
    by (rule C_BA_disj_congruence[OF C_boolean_lambda_reflexive[OF A]
      C_boolean_lambda_conj_true_left[OF NA]])
  have left_truth: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A (Conj ObjTrue (Neg A)))) (Lam \<sigma> ObjTrue)"
    by (rule C_A1_trans[OF left_step C_boolean_lambda_excluded_middle_ObjTrue[OF A]])
  have right_step: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Disj A ObjTrue) (Disj A (Neg A))))
    (Lam \<sigma> (Conj (Disj A ObjTrue) ObjTrue))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF AT]
      C_boolean_lambda_excluded_middle_ObjTrue[OF A]])
  have right_normal: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Disj A ObjTrue) (Disj A (Neg A)))) (Lam \<sigma> (Disj A ObjTrue))"
    by (rule C_A1_trans[OF right_step C_boolean_lambda_conj_true_right[OF AT]])
  show ?thesis by (rule C_A1_sym[OF C_A1_transport[OF distribution left_truth right_normal]])
qed

lemma C_boolean_lambda_disj_true_left:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj ObjTrue A)) (Lam \<sigma> ObjTrue)"
  by (rule C_A1_trans[OF C_boolean_lambda_disj_commutes[OF typed_ObjTrue A]
    C_boolean_lambda_disj_true_right[OF A]])

theorem C_boolean_lambda_conj_false_right:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A ObjFalse)) (Lam \<sigma> ObjFalse)"
proof -
  have NA: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have AF: "\<sigma> # \<Gamma> \<turnstile> Conj A ObjFalse : Prop"
    by (rule has_type.Conj[OF A typed_ObjFalse])
  have distribution: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Disj ObjFalse (Neg A))))
    (Lam \<sigma> (Disj (Conj A ObjFalse) (Conj A (Neg A))))"
    by (rule C_boolean_lambda_conj_distributes[OF A typed_ObjFalse NA])
  have left_step: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Disj ObjFalse (Neg A)))) (Lam \<sigma> (Conj A (Neg A)))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF A]
      C_boolean_lambda_disj_false_left[OF NA]])
  have left_false: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Disj ObjFalse (Neg A)))) (Lam \<sigma> ObjFalse)"
    by (rule C_A1_trans[OF left_step C_boolean_lambda_contradiction_ObjFalse[OF A]])
  have right_step: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Conj A ObjFalse) (Conj A (Neg A))))
    (Lam \<sigma> (Disj (Conj A ObjFalse) ObjFalse))"
    by (rule C_BA_disj_congruence[OF C_boolean_lambda_reflexive[OF AF]
      C_boolean_lambda_contradiction_ObjFalse[OF A]])
  have right_normal: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Conj A ObjFalse) (Conj A (Neg A)))) (Lam \<sigma> (Conj A ObjFalse))"
    by (rule C_A1_trans[OF right_step C_boolean_lambda_disj_false_right[OF AF]])
  show ?thesis by (rule C_A1_sym[OF C_A1_transport[OF distribution left_false right_normal]])
qed

lemma C_boolean_lambda_conj_false_left:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj ObjFalse A)) (Lam \<sigma> ObjFalse)"
  by (rule C_A1_trans[OF C_boolean_lambda_conj_commutes[OF typed_ObjFalse A]
    C_boolean_lambda_conj_false_right[OF A]])

subsection \<open>Absorption for arbitrary typed bodies\<close>

text \<open>
  Distribute A ∨ (⊥₀ ∧ B).  Domination reduces the left side to A;
  the unit equation reduces the right side to A ∧ (A ∨ B).
  The dual calculation gives A ∨ (A ∧ B) = A.
  Status.  These unconditional identities apply to nonconstant predicates.
\<close>

theorem C_boolean_lambda_conj_absorbs:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Disj A B))) (Lam \<sigma> A)"
proof -
  have AB: "\<sigma> # \<Gamma> \<turnstile> Disj A B : Prop" by (rule has_type.Disj[OF A B])
  have distribution: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A (Conj ObjFalse B)))
    (Lam \<sigma> (Conj (Disj A ObjFalse) (Disj A B)))"
    by (rule C_boolean_lambda_disj_distributes[OF A typed_ObjFalse B])
  have left_step: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A (Conj ObjFalse B))) (Lam \<sigma> (Disj A ObjFalse))"
    by (rule C_BA_disj_congruence[OF C_boolean_lambda_reflexive[OF A]
      C_boolean_lambda_conj_false_left[OF B]])
  have left_normal: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A (Conj ObjFalse B))) (Lam \<sigma> A)"
    by (rule C_A1_trans[OF left_step C_boolean_lambda_disj_false_right[OF A]])
  have right_normal: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Disj A ObjFalse) (Disj A B))) (Lam \<sigma> (Conj A (Disj A B)))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_disj_false_right[OF A]
      C_boolean_lambda_reflexive[OF AB]])
  show ?thesis by (rule C_A1_sym[OF C_A1_transport[OF distribution left_normal right_normal]])
qed

theorem C_boolean_lambda_disj_absorbs:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A (Conj A B))) (Lam \<sigma> A)"
proof -
  have AB: "\<sigma> # \<Gamma> \<turnstile> Conj A B : Prop" by (rule has_type.Conj[OF A B])
  have distribution: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Disj ObjTrue B)))
    (Lam \<sigma> (Disj (Conj A ObjTrue) (Conj A B)))"
    by (rule C_boolean_lambda_conj_distributes[OF A typed_ObjTrue B])
  have left_step: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Disj ObjTrue B))) (Lam \<sigma> (Conj A ObjTrue))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF A]
      C_boolean_lambda_disj_true_left[OF B]])
  have left_normal: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Disj ObjTrue B))) (Lam \<sigma> A)"
    by (rule C_A1_trans[OF left_step C_boolean_lambda_conj_true_right[OF A]])
  have right_normal: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Conj A ObjTrue) (Conj A B))) (Lam \<sigma> (Disj A (Conj A B)))"
    by (rule C_BA_disj_congruence[OF C_boolean_lambda_conj_true_right[OF A]
      C_boolean_lambda_reflexive[OF AB]])
  show ?thesis by (rule C_A1_sym[OF C_A1_transport[OF distribution left_normal right_normal]])
qed

text \<open>
  A direct route to the unconditional PC case is now to complete the
  Boolean algebra laws on typed bodies modulo predicate identity, then
  prove a finite Boolean normal-form or Shannon-expansion theorem there.
  Associativity and the needed complement-normalization laws remain to
  be established before importing any Boolean-algebra completeness result.
  No such completeness result or quotient instance is claimed here.
\<close>

end
