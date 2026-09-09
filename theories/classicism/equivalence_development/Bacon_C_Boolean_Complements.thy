theory Bacon_C_Boolean_Complements
  imports Bacon_C_Boolean_Meet_Order
begin

section \<open>Complement uniqueness and negation normalization beneath λ\<close>

text \<open>
  Complements are unique modulo C predicate identity.  Consequently
  ¬¬A = A, ¬(A ∧ B) = ¬A ∨ ¬B, and ¬(A ∨ B) = ¬A ∧ ¬B
  hold beneath λv.  Source use: Booleanism in Bacon--Dorr Figure 3,
  p.10, towards the unconditional PC case of Appendix A.2(i), p.65.
  Isabelle representation.  All equalities are C theorems at σ → t;
  C_BA_le is the derived order from the preceding leaf.
  Status.  No atomic-constancy, semantic completeness, CE/CEV, or new axiom
  is used.  A finite unconditional Boolean normalization theorem is still
  a separate obligation.
\<close>

lemma C_BA_neg_congruence:
  assumes AB: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> B)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Neg A)) (Lam \<sigma> (Neg B))"
proof -
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    using C_proves_formula[OF AB] by (auto elim: has_type.cases)
  show ?thesis by (rule C_boolean_lambda_neg_congruence[OF A B AB])
qed

lemma C_BA_complement_bound:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and D: "\<sigma> # \<Gamma> \<turnstile> D : Prop"
    and disjoint: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Conj A B)) (Lam \<sigma> ObjFalse)"
    and covering: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Disj A D)) (Lam \<sigma> ObjTrue)"
  shows "C_BA_le \<Gamma> \<sigma> B D"
proof -
  have BD: "\<sigma> # \<Gamma> \<turnstile> Conj B D : Prop" by (rule has_type.Conj[OF B D])
  have reversed_disjoint: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj B A)) (Lam \<sigma> ObjFalse)"
    by (rule C_A1_trans[OF C_boolean_lambda_conj_commutes[OF B A] disjoint])
  have left_step: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj B (Disj A D))) (Lam \<sigma> (Conj B ObjTrue))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF B] covering])
  have left_normal: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj B (Disj A D))) (Lam \<sigma> B)"
    by (rule C_A1_trans[OF left_step C_boolean_lambda_conj_true_right[OF B]])
  have right_step: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Conj B A) (Conj B D))) (Lam \<sigma> (Disj ObjFalse (Conj B D)))"
    by (rule C_BA_disj_congruence[OF reversed_disjoint C_boolean_lambda_reflexive[OF BD]])
  have right_normal: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Conj B A) (Conj B D))) (Lam \<sigma> (Conj B D))"
    by (rule C_A1_trans[OF right_step C_boolean_lambda_disj_false_left[OF BD]])
  show ?thesis unfolding C_BA_le_def
    by (rule C_A1_sym[OF C_A1_transport[OF
      C_boolean_lambda_conj_distributes[OF B A D] left_normal right_normal]])
qed

theorem C_boolean_lambda_complement_unique:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and D: "\<sigma> # \<Gamma> \<turnstile> D : Prop"
    and AB: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> (Conj A B)) (Lam \<sigma> ObjFalse)"
    and AD: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> (Conj A D)) (Lam \<sigma> ObjFalse)"
    and cover_B: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> (Disj A B)) (Lam \<sigma> ObjTrue)"
    and cover_D: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> (Disj A D)) (Lam \<sigma> ObjTrue)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> B) (Lam \<sigma> D)"
  by (rule C_BA_le_antisym[OF B D C_BA_complement_bound[OF A B D AB cover_D]
    C_BA_complement_bound[OF A D B AD cover_B]])

theorem C_boolean_lambda_double_negation:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> (Neg (Neg A))) (Lam \<sigma> A)"
proof -
  have NA: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have NNA: "\<sigma> # \<Gamma> \<turnstile> Neg (Neg A) : Prop" by (rule has_type.Neg[OF NA])
  have disjoint: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Neg A) A)) (Lam \<sigma> ObjFalse)"
    by (rule C_A1_trans[OF C_boolean_lambda_conj_commutes[OF NA A]
      C_boolean_lambda_contradiction_ObjFalse[OF A]])
  have covering: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Neg A) A)) (Lam \<sigma> ObjTrue)"
    by (rule C_A1_trans[OF C_boolean_lambda_disj_commutes[OF NA A]
      C_boolean_lambda_excluded_middle_ObjTrue[OF A]])
  show ?thesis by (rule C_boolean_lambda_complement_unique[OF NA NNA A
    C_boolean_lambda_contradiction_ObjFalse[OF NA] disjoint
    C_boolean_lambda_excluded_middle_ObjTrue[OF NA] covering])
qed

subsection \<open>Two reassociations with a complementary factor\<close>

lemma C_BA_conj_complement_factor:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Conj A B) (Neg A))) (Lam \<sigma> ObjFalse)"
proof -
  have NA: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have AB: "\<sigma> # \<Gamma> \<turnstile> Conj A B : Prop" by (rule has_type.Conj[OF A B])
  have reordered: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Conj A B) (Neg A))) (Lam \<sigma> (Conj (Conj (Neg A) A) B))"
    by (rule C_A1_trans[OF C_boolean_lambda_conj_commutes[OF AB NA]
      C_A1_sym[OF C_boolean_lambda_conj_associative[OF NA A B]]])
  have pair: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Neg A) A)) (Lam \<sigma> ObjFalse)"
    by (rule C_A1_trans[OF C_boolean_lambda_conj_commutes[OF NA A]
      C_boolean_lambda_contradiction_ObjFalse[OF A]])
  have reduced: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Conj (Neg A) A) B)) (Lam \<sigma> (Conj ObjFalse B))"
    by (rule C_BA_conj_congruence[OF pair C_boolean_lambda_reflexive[OF B]])
  show ?thesis by (rule C_A1_trans[OF C_A1_trans[OF reordered reduced]
    C_boolean_lambda_conj_false_left[OF B]])
qed

lemma C_BA_disj_complement_front:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Disj (Neg A) B) A)) (Lam \<sigma> ObjTrue)"
proof -
  have NA: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have NAB: "\<sigma> # \<Gamma> \<turnstile> Disj (Neg A) B : Prop" by (rule has_type.Disj[OF NA B])
  have reordered: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Disj (Neg A) B) A)) (Lam \<sigma> (Disj (Disj A (Neg A)) B))"
    by (rule C_A1_trans[OF C_boolean_lambda_disj_commutes[OF NAB A]
      C_A1_sym[OF C_boolean_lambda_disj_associative[OF A NA B]]])
  have reduced: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Disj A (Neg A)) B)) (Lam \<sigma> (Disj ObjTrue B))"
    by (rule C_BA_disj_congruence[OF C_boolean_lambda_excluded_middle_ObjTrue[OF A]
      C_boolean_lambda_reflexive[OF B]])
  show ?thesis by (rule C_A1_trans[OF C_A1_trans[OF reordered reduced]
    C_boolean_lambda_disj_true_left[OF B]])
qed

subsection \<open>De Morgan's laws by complement uniqueness\<close>

theorem C_boolean_lambda_de_morgan_conj:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Neg (Conj A B))) (Lam \<sigma> (Disj (Neg A) (Neg B)))"
proof -
  let ?P = "Conj A B"
  let ?Q = "Disj (Neg A) (Neg B)"
  have NA: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have NB: "\<sigma> # \<Gamma> \<turnstile> Neg B : Prop" by (rule has_type.Neg[OF B])
  have P: "\<sigma> # \<Gamma> \<turnstile> ?P : Prop" by (rule has_type.Conj[OF A B])
  have NP: "\<sigma> # \<Gamma> \<turnstile> Neg ?P : Prop" by (rule has_type.Neg[OF P])
  have Q: "\<sigma> # \<Gamma> \<turnstile> ?Q : Prop" by (rule has_type.Disj[OF NA NB])
  have second_factor: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj ?P (Neg B))) (Lam \<sigma> ObjFalse)"
    by (rule C_A1_trans[OF C_BA_conj_congruence[OF C_boolean_lambda_conj_commutes[OF A B]
      C_boolean_lambda_reflexive[OF NB]] C_BA_conj_complement_factor[OF B A]])
  have meet_reduced: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Conj ?P (Neg A)) (Conj ?P (Neg B))))
    (Lam \<sigma> (Disj ObjFalse ObjFalse))"
    by (rule C_BA_disj_congruence[OF C_BA_conj_complement_factor[OF A B] second_factor])
  have disjoint: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj ?P ?Q)) (Lam \<sigma> ObjFalse)"
    by (rule C_A1_trans[OF C_boolean_lambda_conj_distributes[OF P NA NB]
      C_A1_trans[OF meet_reduced C_boolean_lambda_disj_false_right[OF typed_ObjFalse]]])
  have second_join: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj ?Q B)) (Lam \<sigma> ObjTrue)"
    by (rule C_A1_trans[OF C_BA_disj_congruence[OF C_boolean_lambda_disj_commutes[OF NA NB]
      C_boolean_lambda_reflexive[OF B]] C_BA_disj_complement_front[OF B NA]])
  have join_reduced: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Disj ?Q A) (Disj ?Q B))) (Lam \<sigma> (Conj ObjTrue ObjTrue))"
    by (rule C_BA_conj_congruence[OF C_BA_disj_complement_front[OF A NB] second_join])
  have reversed_cover: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj ?Q ?P)) (Lam \<sigma> ObjTrue)"
    by (rule C_A1_trans[OF C_boolean_lambda_disj_distributes[OF Q A B]
      C_A1_trans[OF join_reduced C_boolean_lambda_conj_true_right[OF typed_ObjTrue]]])
  have covering: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj ?P ?Q)) (Lam \<sigma> ObjTrue)"
    by (rule C_A1_trans[OF C_boolean_lambda_disj_commutes[OF P Q] reversed_cover])
  show ?thesis by (rule C_boolean_lambda_complement_unique[OF P NP Q
    C_boolean_lambda_contradiction_ObjFalse[OF P] disjoint
    C_boolean_lambda_excluded_middle_ObjTrue[OF P] covering])
qed

theorem C_boolean_lambda_de_morgan_disj:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Neg (Disj A B))) (Lam \<sigma> (Conj (Neg A) (Neg B)))"
proof -
  have NA: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have NB: "\<sigma> # \<Gamma> \<turnstile> Neg B : Prop" by (rule has_type.Neg[OF B])
  have product: "\<sigma> # \<Gamma> \<turnstile> Conj (Neg A) (Neg B) : Prop"
    by (rule has_type.Conj[OF NA NB])
  have reduced: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Neg (Neg A)) (Neg (Neg B)))) (Lam \<sigma> (Disj A B))"
    by (rule C_BA_disj_congruence[OF C_boolean_lambda_double_negation[OF A]
      C_boolean_lambda_double_negation[OF B]])
  have complement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Neg (Conj (Neg A) (Neg B)))) (Lam \<sigma> (Disj A B))"
    by (rule C_A1_trans[OF C_boolean_lambda_de_morgan_conj[OF NA NB] reduced])
  have negated: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Neg (Neg (Conj (Neg A) (Neg B))))) (Lam \<sigma> (Neg (Disj A B)))"
    by (rule C_BA_neg_congruence[OF complement])
  show ?thesis by (rule C_A1_trans[OF C_A1_sym[OF negated]
    C_boolean_lambda_double_negation[OF product]])
qed

end
