theory Bacon_C_Boolean_Constants
  imports Bacon_C_Boolean_Idempotence
begin

section \<open>Truth, falsity, and constant evaluation beneath λ\<close>

text \<open>
  With ⊤₀ := ∀p.(p → p) and ⊥₀ := ¬⊤₀, we derive
  A ∧ ⊤₀ = A, A ∨ ⊥₀ = A, A ∧ ¬A = ⊥₀, and ¬⊥₀ = ⊤₀
  beneath λv.  Source use: Bacon--Dorr Figure 3, p.10, and the Boolean
  normalization argument of Appendix A.2(i), p.65.

  Isabelle representation.  ObjTrue and ObjFalse remain the existing
  object-language abbreviations.  C_boolean_constant selects these
  representatives using a metatheoretic Boolean value.
  Status.  All displayed identities are derived in axiom-based C.
  The constant truth tables do not assume that arbitrary propositions
  are identical to one of these constants.
\<close>

lemma C_boolean_lambda_reflexive:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> A)"
  by (intro C_proves.H H_proves.Ref has_type.Lam A)

lemma C_boolean_lambda_conj_true_right:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A ObjTrue)) (Lam \<sigma> A)"
proof -
  let ?T = "Disj ObjTrue (Neg ObjTrue)"
  have T: "\<sigma> # \<Gamma> \<turnstile> ?T : Prop"
    by (intro has_type.Disj has_type.Neg typed_ObjTrue)
  have connective: "Conj = Conj \<or> Conj = Disj \<or> Conj = Imp" by simp
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A ?T)) (Lam \<sigma> (Conj A ObjTrue))"
    by (rule C_PC_binary_lambda_congruence[OF connective A A T typed_ObjTrue
      C_boolean_lambda_reflexive[OF A]
      C_boolean_lambda_excluded_middle_ObjTrue[OF typed_ObjTrue]])
  show ?thesis by (rule C_A1_trans[OF C_A1_sym[OF replacement]
    C_boolean_lambda_conj_dissolves[OF A typed_ObjTrue]])
qed

lemma C_boolean_lambda_conj_true_left:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj ObjTrue A)) (Lam \<sigma> A)"
  by (rule C_A1_trans[OF C_boolean_lambda_conj_commutes[OF typed_ObjTrue A]
    C_boolean_lambda_conj_true_right[OF A]])

lemma C_boolean_lambda_contradiction_identity:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Neg A))) (Lam \<sigma> (Conj B (Neg B)))"
proof -
  let ?L = "Conj A (Neg A)"
  let ?R = "Conj B (Neg B)"
  have L: "\<sigma> # \<Gamma> \<turnstile> ?L : Prop" by (intro has_type.Conj has_type.Neg A)
  have R: "\<sigma> # \<Gamma> \<turnstile> ?R : Prop" by (intro has_type.Conj has_type.Neg B)
  have left: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj ?L ?R)) (Lam \<sigma> ?L)"
    by (rule C_boolean_lambda_disj_dissolves[OF L B])
  have right: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj ?R ?L)) (Lam \<sigma> ?R)"
    by (rule C_boolean_lambda_disj_dissolves[OF R A])
  have comm: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj ?L ?R)) (Lam \<sigma> (Disj ?R ?L))"
    by (rule C_boolean_lambda_disj_commutes[OF L R])
  show ?thesis by (rule C_A1_trans[OF C_A1_trans[OF C_A1_sym[OF left] comm] right])
qed

theorem C_boolean_lambda_contradiction_ObjFalse:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj A (Neg A))) (Lam \<sigma> ObjFalse)"
proof -
  have negation: "\<sigma> # \<Gamma> \<turnstile> Neg ObjTrue : Prop"
    by (rule has_type.Neg[OF typed_ObjTrue])
  have bottom: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj ObjTrue (Neg ObjTrue))) (Lam \<sigma> ObjFalse)"
    using C_boolean_lambda_conj_true_left[OF negation] by (simp only: ObjFalse_def)
  show ?thesis by (rule C_A1_trans[OF
    C_boolean_lambda_contradiction_identity[OF A typed_ObjTrue] bottom])
qed

lemma C_boolean_lambda_disj_false_right:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A ObjFalse)) (Lam \<sigma> A)"
proof -
  let ?F = "Conj ObjTrue (Neg ObjTrue)"
  have F: "\<sigma> # \<Gamma> \<turnstile> ?F : Prop"
    by (intro has_type.Conj has_type.Neg typed_ObjTrue)
  have connective: "Disj = Conj \<or> Disj = Disj \<or> Disj = Imp" by simp
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj A ?F)) (Lam \<sigma> (Disj A ObjFalse))"
    by (rule C_PC_binary_lambda_congruence[OF connective A A F typed_ObjFalse
      C_boolean_lambda_reflexive[OF A]
      C_boolean_lambda_contradiction_ObjFalse[OF typed_ObjTrue]])
  show ?thesis by (rule C_A1_trans[OF C_A1_sym[OF replacement]
    C_boolean_lambda_disj_dissolves[OF A typed_ObjTrue]])
qed

lemma C_boolean_lambda_disj_false_left:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj ObjFalse A)) (Lam \<sigma> A)"
  by (rule C_A1_trans[OF C_boolean_lambda_disj_commutes[OF typed_ObjFalse A]
    C_boolean_lambda_disj_false_right[OF A]])

lemma C_boolean_lambda_neg_false:
  "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Neg ObjFalse)) (Lam \<sigma> ObjTrue)"
proof -
  have negation: "\<sigma> # \<Gamma> \<turnstile> Neg ObjFalse : Prop"
    by (rule has_type.Neg[OF typed_ObjFalse])
  have unit: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj ObjFalse (Neg ObjFalse))) (Lam \<sigma> (Neg ObjFalse))"
    by (rule C_boolean_lambda_disj_false_left[OF negation])
  show ?thesis by (rule C_A1_trans[OF C_A1_sym[OF unit]
    C_boolean_lambda_excluded_middle_ObjTrue[OF typed_ObjFalse]])
qed

subsection \<open>All four connectives on constant representatives\<close>

definition C_boolean_constant :: "bool \<Rightarrow> oterm" where
  "C_boolean_constant b = (if b then ObjTrue else ObjFalse)"

lemma C_boolean_constant_type:
  "\<Gamma> \<turnstile> C_boolean_constant b : Prop"
  unfolding C_boolean_constant_def by (cases b) (simp_all add: typed_ObjTrue typed_ObjFalse)

lemma C_boolean_lambda_neg_constant:
  "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Neg (C_boolean_constant b))) (Lam \<sigma> (C_boolean_constant (\<not> b)))"
proof (cases b)
  case True
  show ?thesis using C_boolean_lambda_reflexive[OF typed_ObjFalse, where \<sigma> = \<sigma> and \<Gamma> = \<Gamma>]
    by (simp add: True C_boolean_constant_def ObjFalse_def)
next
  case False
  show ?thesis using C_boolean_lambda_neg_false[where \<Gamma> = \<Gamma> and \<sigma> = \<sigma>]
    by (simp add: False C_boolean_constant_def)
qed

lemma C_boolean_lambda_conj_constants:
  "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (C_boolean_constant b) (C_boolean_constant c)))
    (Lam \<sigma> (C_boolean_constant (b \<and> c)))"
  using C_boolean_lambda_conj_idempotent[OF typed_ObjTrue, where \<tau> = \<sigma> and \<Gamma> = \<Gamma>]
    C_boolean_lambda_conj_idempotent[OF typed_ObjFalse, where \<tau> = \<sigma> and \<Gamma> = \<Gamma>]
    C_boolean_lambda_conj_true_right[OF typed_ObjFalse, where \<sigma> = \<sigma> and \<Gamma> = \<Gamma>]
    C_boolean_lambda_conj_true_left[OF typed_ObjFalse, where \<sigma> = \<sigma> and \<Gamma> = \<Gamma>]
  by (cases b; cases c; simp add: C_boolean_constant_def)

lemma C_boolean_lambda_disj_constants:
  "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (C_boolean_constant b) (C_boolean_constant c)))
    (Lam \<sigma> (C_boolean_constant (b \<or> c)))"
  using C_boolean_lambda_disj_idempotent[OF typed_ObjTrue, where \<tau> = \<sigma> and \<Gamma> = \<Gamma>]
    C_boolean_lambda_disj_idempotent[OF typed_ObjFalse, where \<tau> = \<sigma> and \<Gamma> = \<Gamma>]
    C_boolean_lambda_disj_false_right[OF typed_ObjTrue, where \<sigma> = \<sigma> and \<Gamma> = \<Gamma>]
    C_boolean_lambda_disj_false_left[OF typed_ObjTrue, where \<sigma> = \<sigma> and \<Gamma> = \<Gamma>]
  by (cases b; cases c; simp add: C_boolean_constant_def)

lemma C_boolean_lambda_imp_constants:
  "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Imp (C_boolean_constant b) (C_boolean_constant c)))
    (Lam \<sigma> (C_boolean_constant (b \<longrightarrow> c)))"
proof -
  have negation: "\<sigma> # \<Gamma> \<turnstile> Neg (C_boolean_constant b) : Prop"
    by (rule has_type.Neg[OF C_boolean_constant_type])
  have connective: "Disj = Conj \<or> Disj = Disj \<or> Disj = Imp" by simp
  have replacement: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Disj (Neg (C_boolean_constant b)) (C_boolean_constant c)))
    (Lam \<sigma> (Disj (C_boolean_constant (\<not> b)) (C_boolean_constant c)))"
    by (rule C_PC_binary_lambda_congruence[OF connective negation C_boolean_constant_type
      C_boolean_constant_type C_boolean_constant_type C_boolean_lambda_neg_constant
      C_boolean_lambda_reflexive[OF C_boolean_constant_type]])
  have material: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Imp (C_boolean_constant b) (C_boolean_constant c)))
    (Lam \<sigma> (Disj (Neg (C_boolean_constant b)) (C_boolean_constant c)))"
    by (rule C_PC_lambda_material_imp[OF C_boolean_constant_type C_boolean_constant_type])
  have result: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Imp (C_boolean_constant b) (C_boolean_constant c)))
    (Lam \<sigma> (C_boolean_constant ((\<not> b) \<or> c)))"
    by (rule C_A1_trans[OF C_A1_trans[OF material replacement] C_boolean_lambda_disj_constants])
  show ?thesis using result by simp
qed

text \<open>
  These tables permit a structural evaluation theorem when each atomic
  predicate is already supplied with an identity to its chosen constant.
  Eliminating that hypothesis uniformly for a tautology is a further
  equational-completeness obligation.  Associativity and absorption of
  arbitrary, nonconstant propositions are not asserted in this leaf.
\<close>

end
