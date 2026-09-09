theory Bacon_C_Boolean_Masks
  imports Bacon_C_Boolean_Complements
begin

section \<open>Masked congruence and the unconditional Boolean split\<close>

text \<open>
  To prove the PC case without assuming constant predicates, normalize
  A separately beneath the masks p and ¬p.  We establish that
  p ∧ A = p ∧ B entails p ∧ ¬A = p ∧ ¬B, and similarly that masked
  identity is preserved by each binary Boolean connective.  Finally,
  A = (p ∧ A) ∨ (¬p ∧ A).

  Isabelle representation.  Every displayed equation is beneath λv
  and proved in C.  A mask is itself an arbitrary typed proposition body.
  Status.  Masking is proof-engineering for the Booleanism obligation in
  Bacon--Dorr Appendix A.2(i), p.65; no atomic-constancy assumption,
  Equivalence rule, or completed PC theorem is introduced.
\<close>

lemma C_boolean_mask_negation:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> P : Prop" and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj P (Neg (Conj P A)))) (Lam \<sigma> (Conj P (Neg A)))"
proof -
  have NP: "\<sigma> # \<Gamma> \<turnstile> Neg P : Prop" by (rule has_type.Neg[OF P])
  have NA: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have PNA: "\<sigma> # \<Gamma> \<turnstile> Conj P (Neg A) : Prop" by (rule has_type.Conj[OF P NA])
  have de_morgan: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj P (Neg (Conj P A)))) (Lam \<sigma> (Conj P (Disj (Neg P) (Neg A))))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF P]
      C_boolean_lambda_de_morgan_conj[OF P A]])
  have reduced: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Conj P (Neg P)) (Conj P (Neg A))))
    (Lam \<sigma> (Disj ObjFalse (Conj P (Neg A))))"
    by (rule C_BA_disj_congruence[OF C_boolean_lambda_contradiction_ObjFalse[OF P]
      C_boolean_lambda_reflexive[OF PNA]])
  show ?thesis by (rule C_A1_trans[OF de_morgan
    C_A1_trans[OF C_boolean_lambda_conj_distributes[OF P NP NA]
      C_A1_trans[OF reduced C_boolean_lambda_disj_false_left[OF PNA]]]])
qed

theorem C_boolean_mask_neg_congruence:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> P : Prop" and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and masked: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Conj P A)) (Lam \<sigma> (Conj P B))"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj P (Neg A))) (Lam \<sigma> (Conj P (Neg B)))"
proof -
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj P (Neg (Conj P A)))) (Lam \<sigma> (Conj P (Neg (Conj P B))))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF P]
      C_BA_neg_congruence[OF masked]])
  show ?thesis by (rule C_A1_transport[OF replacement
    C_boolean_mask_negation[OF P A] C_boolean_mask_negation[OF P B]])
qed

lemma C_boolean_mask_conjunction:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> P : Prop" and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj P (Conj A B))) (Lam \<sigma> (Conj (Conj P A) (Conj P B)))"
proof -
  have PA: "\<sigma> # \<Gamma> \<turnstile> Conj P A : Prop" by (rule has_type.Conj[OF P A])
  have repeat: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Conj P A) P)) (Lam \<sigma> (Conj P A))"
    using C_BA_meet_le_left[OF P A] unfolding C_BA_le_def .
  have reduced: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Conj (Conj P A) P) B)) (Lam \<sigma> (Conj (Conj P A) B))"
    by (rule C_BA_conj_congruence[OF repeat C_boolean_lambda_reflexive[OF B]])
  have reversed: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Conj P A) (Conj P B))) (Lam \<sigma> (Conj P (Conj A B)))"
    by (rule C_A1_trans[OF C_A1_sym[OF C_boolean_lambda_conj_associative[OF PA P B]]
      C_A1_trans[OF reduced C_boolean_lambda_conj_associative[OF P A B]]])
  show ?thesis by (rule C_A1_sym[OF reversed])
qed

theorem C_boolean_mask_conj_congruence:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> P : Prop" and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop" and D: "\<sigma> # \<Gamma> \<turnstile> D : Prop"
    and E: "\<sigma> # \<Gamma> \<turnstile> E : Prop"
    and AB: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Conj P A)) (Lam \<sigma> (Conj P B))"
    and DE: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Conj P D)) (Lam \<sigma> (Conj P E))"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj P (Conj A D))) (Lam \<sigma> (Conj P (Conj B E)))"
proof -
  have middle: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Conj P A) (Conj P D))) (Lam \<sigma> (Conj (Conj P B) (Conj P E)))"
    by (rule C_BA_conj_congruence[OF AB DE])
  show ?thesis by (rule C_A1_trans[OF C_boolean_mask_conjunction[OF P A D]
    C_A1_trans[OF middle C_A1_sym[OF C_boolean_mask_conjunction[OF P B E]]]])
qed

theorem C_boolean_mask_disj_congruence:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> P : Prop" and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop" and D: "\<sigma> # \<Gamma> \<turnstile> D : Prop"
    and E: "\<sigma> # \<Gamma> \<turnstile> E : Prop"
    and AB: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Conj P A)) (Lam \<sigma> (Conj P B))"
    and DE: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Conj P D)) (Lam \<sigma> (Conj P E))"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj P (Disj A D))) (Lam \<sigma> (Conj P (Disj B E)))"
proof -
  have middle: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Conj P A) (Conj P D))) (Lam \<sigma> (Disj (Conj P B) (Conj P E)))"
    by (rule C_BA_disj_congruence[OF AB DE])
  show ?thesis by (rule C_A1_trans[OF C_boolean_lambda_conj_distributes[OF P A D]
    C_A1_trans[OF middle C_A1_sym[OF C_boolean_lambda_conj_distributes[OF P B E]]]])
qed

theorem C_boolean_mask_imp_congruence:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> P : Prop" and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop" and D: "\<sigma> # \<Gamma> \<turnstile> D : Prop"
    and E: "\<sigma> # \<Gamma> \<turnstile> E : Prop"
    and AB: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Conj P A)) (Lam \<sigma> (Conj P B))"
    and DE: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Conj P D)) (Lam \<sigma> (Conj P E))"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj P (Imp A D))) (Lam \<sigma> (Conj P (Imp B E)))"
proof -
  have NA: "\<sigma> # \<Gamma> \<turnstile> Neg A : Prop" by (rule has_type.Neg[OF A])
  have NB: "\<sigma> # \<Gamma> \<turnstile> Neg B : Prop" by (rule has_type.Neg[OF B])
  have middle: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj P (Disj (Neg A) D))) (Lam \<sigma> (Conj P (Disj (Neg B) E)))"
    by (rule C_boolean_mask_disj_congruence[OF P NA NB D E
      C_boolean_mask_neg_congruence[OF P A B AB] DE])
  have left_basis: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj P (Imp A D))) (Lam \<sigma> (Conj P (Disj (Neg A) D)))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF P] C_PC_lambda_material_imp[OF A D]])
  have right_basis: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj P (Imp B E))) (Lam \<sigma> (Conj P (Disj (Neg B) E)))"
    by (rule C_BA_conj_congruence[OF C_boolean_lambda_reflexive[OF P] C_PC_lambda_material_imp[OF B E]])
  show ?thesis by (rule C_A1_trans[OF left_basis C_A1_trans[OF middle C_A1_sym[OF right_basis]]])
qed

subsection \<open>Splitting and selecting an atomic cofactor\<close>

theorem C_boolean_lambda_mask_split:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> P : Prop" and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> A) (Lam \<sigma> (Disj (Conj P A) (Conj (Neg P) A)))"
proof -
  have NP: "\<sigma> # \<Gamma> \<turnstile> Neg P : Prop" by (rule has_type.Neg[OF P])
  have expanded: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> A) (Lam \<sigma> (Disj (Conj A P) (Conj A (Neg P))))"
    by (rule C_A1_trans[OF C_A1_sym[OF C_boolean_lambda_conj_dissolves[OF A P]]
      C_boolean_lambda_conj_distributes[OF A P NP]])
  have reordered: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Conj A P) (Conj A (Neg P))))
    (Lam \<sigma> (Disj (Conj P A) (Conj (Neg P) A)))"
    by (rule C_BA_disj_congruence[OF C_boolean_lambda_conj_commutes[OF A P]
      C_boolean_lambda_conj_commutes[OF A NP]])
  show ?thesis by (rule C_A1_trans[OF expanded reordered])
qed

definition C_boolean_mask :: "bool \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_boolean_mask b P = (if b then P else Neg P)"

lemma C_boolean_mask_type:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
  shows "\<sigma> # \<Gamma> \<turnstile> C_boolean_mask b P : Prop"
  using P has_type.Neg[OF P] by (cases b) (simp_all add: C_boolean_mask_def)

lemma C_boolean_mask_selected_atom:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (C_boolean_mask b P) P))
    (Lam \<sigma> (Conj (C_boolean_mask b P) (C_boolean_constant b)))"
proof (cases b)
  case True
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj P P)) (Lam \<sigma> (Conj P ObjTrue))"
    by (rule C_A1_trans[OF C_boolean_lambda_conj_idempotent[OF P]
      C_A1_sym[OF C_boolean_lambda_conj_true_right[OF P]]])
  show ?thesis using identity by (simp add: True C_boolean_mask_def C_boolean_constant_def)
next
  case False
  have NP: "\<sigma> # \<Gamma> \<turnstile> Neg P : Prop" by (rule has_type.Neg[OF P])
  have contradiction: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Neg P) P)) (Lam \<sigma> ObjFalse)"
    by (rule C_A1_trans[OF C_boolean_lambda_conj_commutes[OF NP P]
      C_boolean_lambda_contradiction_ObjFalse[OF P]])
  have identity: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Neg P) P)) (Lam \<sigma> (Conj (Neg P) ObjFalse))"
    by (rule C_A1_trans[OF contradiction C_A1_sym[OF C_boolean_lambda_conj_false_right[OF NP]]])
  show ?thesis using identity by (simp add: False C_boolean_mask_def C_boolean_constant_def)
qed

text \<open>
  The next step may recursively replace one selected opaque atom p by
  ε(b) throughout the Boolean skeleton, preserving equality beneath its
  mask C_boolean_mask b p.  Combining the two cofactors with mask_split
  gives Shannon expansion.  A finite-atom induction must still justify
  the unconditional PC-to-truth theorem.
\<close>

end
