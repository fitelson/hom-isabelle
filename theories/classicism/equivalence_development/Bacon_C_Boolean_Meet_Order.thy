theory Bacon_C_Boolean_Meet_Order
  imports Bacon_C_Boolean_Absorption
begin

section \<open>The induced meet-order and conjunction associativity\<close>

text \<open>
  Write A ≼ B when ⊢C (λv.A ∧ B) = (λv.A).  On typed bodies,
  A ≼ B is equivalent to ⊢C (λv.A ∨ B) = (λv.B).  We prove
  transitivity and the greatest-lower-bound property of ∧, and obtain
  ⊢C (λv.(A ∧ B) ∧ D) = (λv.A ∧ (B ∧ D)).
  Source use: Booleanism in Bacon--Dorr Figure 3, p.10, and A.2(i), p.65.

  Isabelle representation.  C_BA_le is a relation on syntax, parameterized
  by Γ and the abstraction type σ.  Antisymmetry concludes C predicate
  identity, not equality of syntax trees.  No quotient type is introduced.
  Status.  The order laws are derived in C; no lattice axioms or atomic
  constancy hypotheses are assumed.
\<close>

definition C_BA_le :: "ctx \<Rightarrow> otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> bool" where
  "C_BA_le \<Gamma> \<sigma> A B \<longleftrightarrow>
    \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> (Conj A B)) (Lam \<sigma> A)"

lemma C_BA_le_refl:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "C_BA_le \<Gamma> \<sigma> A A"
  unfolding C_BA_le_def by (rule C_boolean_lambda_conj_idempotent[OF A])

lemma C_BA_le_to_join:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and AB: "C_BA_le \<Gamma> \<sigma> A B"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A B)) (Lam \<sigma> B)"
proof -
  have meet: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A B)) (Lam \<sigma> A)" using AB unfolding C_BA_le_def .
  have reversed_meet: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj B A)) (Lam \<sigma> A)"
    by (rule C_A1_trans[OF C_boolean_lambda_conj_commutes[OF B A] meet])
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj B (Conj B A))) (Lam \<sigma> (Disj B A))"
    by (rule C_BA_disj_congruence[OF C_boolean_lambda_reflexive[OF B] reversed_meet])
  have reversed_join: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj B A)) (Lam \<sigma> B)"
    by (rule C_A1_trans[OF C_A1_sym[OF replacement] C_boolean_lambda_disj_absorbs[OF B A]])
  show ?thesis by (rule C_A1_trans[OF C_boolean_lambda_disj_commutes[OF A B] reversed_join])
qed

lemma C_BA_join_to_le:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and join_eq: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Disj A B)) (Lam \<sigma> B)"
  shows "C_BA_le \<Gamma> \<sigma> A B"
proof -
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Disj A B))) (Lam \<sigma> (Conj A B))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF A] join_eq])
  show ?thesis unfolding C_BA_le_def
    by (rule C_A1_trans[OF C_A1_sym[OF replacement] C_boolean_lambda_conj_absorbs[OF A B]])
qed

lemma C_BA_le_join_iff:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "C_BA_le \<Gamma> \<sigma> A B \<longleftrightarrow>
    \<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> (Disj A B)) (Lam \<sigma> B)"
  using C_BA_le_to_join[OF A B] C_BA_join_to_le[OF A B] by blast

lemma C_BA_le_antisym:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and AB: "C_BA_le \<Gamma> \<sigma> A B" and BA: "C_BA_le \<Gamma> \<sigma> B A"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> B)"
proof -
  have left: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A B)) (Lam \<sigma> A)" using AB unfolding C_BA_le_def .
  have right: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj B A)) (Lam \<sigma> B)" using BA unfolding C_BA_le_def .
  show ?thesis by (rule C_A1_transport[OF C_boolean_lambda_conj_commutes[OF A B] left right])
qed

subsection \<open>Transitivity without an associativity assumption\<close>

text \<open>
  If A ≼ B ≼ D, distribute D ∨ (A ∧ B).  The left side is D ∨ A;
  the right side is (D ∨ A) ∧ D = D by absorption.  Thus A ≼ D.
  Status.  This avoids using the associativity law being established.
\<close>

lemma C_BA_le_trans:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and D: "\<sigma> # \<Gamma> \<turnstile> D : Prop"
    and AB: "C_BA_le \<Gamma> \<sigma> A B" and BD: "C_BA_le \<Gamma> \<sigma> B D"
  shows "C_BA_le \<Gamma> \<sigma> A D"
proof -
  have DA: "\<sigma> # \<Gamma> \<turnstile> Disj D A : Prop" by (rule has_type.Disj[OF D A])
  have meet: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A B)) (Lam \<sigma> A)" using AB unfolding C_BA_le_def .
  have join_DB: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj D B)) (Lam \<sigma> D)"
    by (rule C_A1_trans[OF C_boolean_lambda_disj_commutes[OF D B] C_BA_le_to_join[OF B D BD]])
  have distribution: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj D (Conj A B))) (Lam \<sigma> (Conj (Disj D A) (Disj D B)))"
    by (rule C_boolean_lambda_disj_distributes[OF D A B])
  have left: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj D (Conj A B))) (Lam \<sigma> (Disj D A))"
    by (rule C_BA_disj_congruence[OF C_boolean_lambda_reflexive[OF D] meet])
  have right_step: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Disj D A) (Disj D B))) (Lam \<sigma> (Conj (Disj D A) D))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF DA] join_DB])
  have absorb: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Disj D A) D)) (Lam \<sigma> D)"
    by (rule C_A1_trans[OF C_boolean_lambda_conj_commutes[OF DA D]
      C_boolean_lambda_conj_absorbs[OF D A]])
  have right: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Disj D A) (Disj D B))) (Lam \<sigma> D)"
    by (rule C_A1_trans[OF right_step absorb])
  have reversed_join: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj D A)) (Lam \<sigma> D)"
    by (rule C_A1_transport[OF distribution left right])
  have join_eq: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A D)) (Lam \<sigma> D)"
    by (rule C_A1_trans[OF C_boolean_lambda_disj_commutes[OF A D] reversed_join])
  show ?thesis by (rule C_BA_join_to_le[OF A D join_eq])
qed

subsection \<open>Conjunction is a greatest lower bound\<close>

lemma C_BA_meet_le_left:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "C_BA_le \<Gamma> \<sigma> (Conj A B) A"
proof -
  have meet_type: "\<sigma> # \<Gamma> \<turnstile> Conj A B : Prop" by (rule has_type.Conj[OF A B])
  have join_eq: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Conj A B) A)) (Lam \<sigma> A)"
    by (rule C_A1_trans[OF C_boolean_lambda_disj_commutes[OF meet_type A]
      C_boolean_lambda_disj_absorbs[OF A B]])
  show ?thesis by (rule C_BA_join_to_le[OF meet_type A join_eq])
qed

lemma C_BA_meet_le_right:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "C_BA_le \<Gamma> \<sigma> (Conj A B) B"
proof -
  have meet_type: "\<sigma> # \<Gamma> \<turnstile> Conj A B : Prop" by (rule has_type.Conj[OF A B])
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj B (Conj A B))) (Lam \<sigma> (Disj B (Conj B A)))"
    by (rule C_BA_disj_congruence[OF C_boolean_lambda_reflexive[OF B]
      C_boolean_lambda_conj_commutes[OF A B]])
  have join_eq: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Conj A B) B)) (Lam \<sigma> B)"
    by (rule C_A1_trans[OF C_boolean_lambda_disj_commutes[OF meet_type B]
      C_A1_trans[OF replacement C_boolean_lambda_disj_absorbs[OF B A]]])
  show ?thesis by (rule C_BA_join_to_le[OF meet_type B join_eq])
qed

lemma C_BA_meet_greatest:
  assumes X: "\<sigma> # \<Gamma> \<turnstile> X : Prop" and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and XA: "C_BA_le \<Gamma> \<sigma> X A" and XB: "C_BA_le \<Gamma> \<sigma> X B"
  shows "C_BA_le \<Gamma> \<sigma> X (Conj A B)"
proof -
  have meet_type: "\<sigma> # \<Gamma> \<turnstile> Conj A B : Prop" by (rule has_type.Conj[OF A B])
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Disj X A) (Disj X B))) (Lam \<sigma> (Conj A B))"
    by (rule C_BA_conj_congruence[OF C_BA_le_to_join[OF X A XA] C_BA_le_to_join[OF X B XB]])
  have join_eq: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj X (Conj A B))) (Lam \<sigma> (Conj A B))"
    by (rule C_A1_trans[OF C_boolean_lambda_disj_distributes[OF X A B] replacement])
  show ?thesis by (rule C_BA_join_to_le[OF X meet_type join_eq])
qed

subsection \<open>Associativity from the two universal properties\<close>

text \<open>
  Both (A ∧ B) ∧ D and A ∧ (B ∧ D) are greatest lower bounds of
  A, B, and D.  Transitivity supplies their three lower-bound facts;
  the binary greatest-lower-bound property gives comparison in both
  directions.  Antisymmetry yields predicate identity.
  Status.  This establishes conjunction associativity.  The final group
  derives the dual join result; neither assumes a Boolean-algebra quotient.
\<close>

theorem C_boolean_lambda_conj_associative:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and D: "\<sigma> # \<Gamma> \<turnstile> D : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Conj A B) D)) (Lam \<sigma> (Conj A (Conj B D)))"
proof -
  let ?AB = "Conj A B"
  let ?BD = "Conj B D"
  let ?L = "Conj ?AB D"
  let ?R = "Conj A ?BD"
  have AB: "\<sigma> # \<Gamma> \<turnstile> ?AB : Prop" by (rule has_type.Conj[OF A B])
  have BD: "\<sigma> # \<Gamma> \<turnstile> ?BD : Prop" by (rule has_type.Conj[OF B D])
  have L: "\<sigma> # \<Gamma> \<turnstile> ?L : Prop" by (rule has_type.Conj[OF AB D])
  have R: "\<sigma> # \<Gamma> \<turnstile> ?R : Prop" by (rule has_type.Conj[OF A BD])
  have L_AB: "C_BA_le \<Gamma> \<sigma> ?L ?AB" by (rule C_BA_meet_le_left[OF AB D])
  have L_A: "C_BA_le \<Gamma> \<sigma> ?L A"
    by (rule C_BA_le_trans[OF L AB A L_AB C_BA_meet_le_left[OF A B]])
  have L_B: "C_BA_le \<Gamma> \<sigma> ?L B"
    by (rule C_BA_le_trans[OF L AB B L_AB C_BA_meet_le_right[OF A B]])
  have L_D: "C_BA_le \<Gamma> \<sigma> ?L D" by (rule C_BA_meet_le_right[OF AB D])
  have L_BD: "C_BA_le \<Gamma> \<sigma> ?L ?BD" by (rule C_BA_meet_greatest[OF L B D L_B L_D])
  have LR: "C_BA_le \<Gamma> \<sigma> ?L ?R" by (rule C_BA_meet_greatest[OF L A BD L_A L_BD])
  have R_A: "C_BA_le \<Gamma> \<sigma> ?R A" by (rule C_BA_meet_le_left[OF A BD])
  have R_BD: "C_BA_le \<Gamma> \<sigma> ?R ?BD" by (rule C_BA_meet_le_right[OF A BD])
  have R_B: "C_BA_le \<Gamma> \<sigma> ?R B"
    by (rule C_BA_le_trans[OF R BD B R_BD C_BA_meet_le_left[OF B D]])
  have R_D: "C_BA_le \<Gamma> \<sigma> ?R D"
    by (rule C_BA_le_trans[OF R BD D R_BD C_BA_meet_le_right[OF B D]])
  have R_AB: "C_BA_le \<Gamma> \<sigma> ?R ?AB" by (rule C_BA_meet_greatest[OF R A B R_A R_B])
  have RL: "C_BA_le \<Gamma> \<sigma> ?R ?L" by (rule C_BA_meet_greatest[OF R AB D R_AB R_D])
  show ?thesis by (rule C_BA_le_antisym[OF L R LR RL])
qed

subsection \<open>Disjunction is a least upper bound and is associative\<close>

lemma C_BA_le_join_left:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "C_BA_le \<Gamma> \<sigma> A (Disj A B)"
  unfolding C_BA_le_def by (rule C_boolean_lambda_conj_absorbs[OF A B])

lemma C_BA_le_join_right:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "C_BA_le \<Gamma> \<sigma> B (Disj A B)"
proof -
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj B (Disj A B))) (Lam \<sigma> (Conj B (Disj B A)))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF B]
      C_boolean_lambda_disj_commutes[OF A B]])
  show ?thesis unfolding C_BA_le_def
    by (rule C_A1_trans[OF replacement C_boolean_lambda_conj_absorbs[OF B A]])
qed

lemma C_BA_join_least:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and X: "\<sigma> # \<Gamma> \<turnstile> X : Prop"
    and AX: "C_BA_le \<Gamma> \<sigma> A X" and BX: "C_BA_le \<Gamma> \<sigma> B X"
  shows "C_BA_le \<Gamma> \<sigma> (Disj A B) X"
proof -
  have AB: "\<sigma> # \<Gamma> \<turnstile> Disj A B : Prop" by (rule has_type.Disj[OF A B])
  have meet_AX: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A X)) (Lam \<sigma> A)" using AX unfolding C_BA_le_def .
  have meet_BX: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj B X)) (Lam \<sigma> B)" using BX unfolding C_BA_le_def .
  have XA: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj X A)) (Lam \<sigma> A)"
    by (rule C_A1_trans[OF C_boolean_lambda_conj_commutes[OF X A] meet_AX])
  have XB: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj X B)) (Lam \<sigma> B)"
    by (rule C_A1_trans[OF C_boolean_lambda_conj_commutes[OF X B] meet_BX])
  have normalized: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj X (Disj A B))) (Lam \<sigma> (Disj A B))"
    by (rule C_A1_trans[OF C_boolean_lambda_conj_distributes[OF X A B]
      C_BA_disj_congruence[OF XA XB]])
  show ?thesis unfolding C_BA_le_def
    by (rule C_A1_trans[OF C_boolean_lambda_conj_commutes[OF AB X] normalized])
qed

theorem C_boolean_lambda_disj_associative:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and D: "\<sigma> # \<Gamma> \<turnstile> D : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Disj A B) D)) (Lam \<sigma> (Disj A (Disj B D)))"
proof -
  let ?AB = "Disj A B"
  let ?BD = "Disj B D"
  let ?L = "Disj ?AB D"
  let ?R = "Disj A ?BD"
  have AB: "\<sigma> # \<Gamma> \<turnstile> ?AB : Prop" by (rule has_type.Disj[OF A B])
  have BD: "\<sigma> # \<Gamma> \<turnstile> ?BD : Prop" by (rule has_type.Disj[OF B D])
  have L: "\<sigma> # \<Gamma> \<turnstile> ?L : Prop" by (rule has_type.Disj[OF AB D])
  have R: "\<sigma> # \<Gamma> \<turnstile> ?R : Prop" by (rule has_type.Disj[OF A BD])
  have A_R: "C_BA_le \<Gamma> \<sigma> A ?R" by (rule C_BA_le_join_left[OF A BD])
  have BD_R: "C_BA_le \<Gamma> \<sigma> ?BD ?R" by (rule C_BA_le_join_right[OF A BD])
  have B_R: "C_BA_le \<Gamma> \<sigma> B ?R"
    by (rule C_BA_le_trans[OF B BD R C_BA_le_join_left[OF B D] BD_R])
  have D_R: "C_BA_le \<Gamma> \<sigma> D ?R"
    by (rule C_BA_le_trans[OF D BD R C_BA_le_join_right[OF B D] BD_R])
  have AB_R: "C_BA_le \<Gamma> \<sigma> ?AB ?R" by (rule C_BA_join_least[OF A B R A_R B_R])
  have LR: "C_BA_le \<Gamma> \<sigma> ?L ?R" by (rule C_BA_join_least[OF AB D R AB_R D_R])
  have AB_L: "C_BA_le \<Gamma> \<sigma> ?AB ?L" by (rule C_BA_le_join_left[OF AB D])
  have A_L: "C_BA_le \<Gamma> \<sigma> A ?L"
    by (rule C_BA_le_trans[OF A AB L C_BA_le_join_left[OF A B] AB_L])
  have B_L: "C_BA_le \<Gamma> \<sigma> B ?L"
    by (rule C_BA_le_trans[OF B AB L C_BA_le_join_right[OF A B] AB_L])
  have D_L: "C_BA_le \<Gamma> \<sigma> D ?L" by (rule C_BA_le_join_right[OF AB D])
  have BD_L: "C_BA_le \<Gamma> \<sigma> ?BD ?L" by (rule C_BA_join_least[OF B D L B_L D_L])
  have RL: "C_BA_le \<Gamma> \<sigma> ?R ?L" by (rule C_BA_join_least[OF A BD L A_L BD_L])
  show ?thesis by (rule C_BA_le_antisym[OF L R LR RL])
qed

text \<open>
  Both associative laws now follow from the derived universal properties.
  Complement uniqueness, negation normalization, and the unconditional
  finite Boolean completeness argument remain separate obligations.
\<close>

end
