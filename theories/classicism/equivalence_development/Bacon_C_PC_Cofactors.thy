theory Bacon_C_PC_Cofactors
  imports Bacon_C_Boolean_Masks Bacon_C_PC_Atomic_Evaluation
begin

section \<open>Opaque-atom cofactors and Shannon expansion\<close>

text \<open>
  A[p := ε(b)] replaces the opaque propositional atom p by the constant
  ε(b), where ε(True) = ⊤₀ and ε(False) = ⊥₀.  Under the corresponding
  mask p or ¬p, this replacement preserves C predicate identity.
  Therefore A = (p ∧ A[p := ⊤₀]) ∨ (¬p ∧ A[p := ⊥₀]) beneath λv.
  Source obligation: Bacon--Dorr Appendix A.2(i), p.65.

  Isabelle representation.  C_PC_replace follows the prop_eval skeleton
  and does not descend into opaque atoms.  This cofactor algorithm is
  proof-engineering for Booleanism, not a further source inference rule.
  Status.  Shannon expansion is unconditional apart from typing.
  Its semantic cofactor equation requires w ObjTrue = True: prop_eval
  treats the quantified abbreviation ObjTrue as an opaque atom.
\<close>

fun C_PC_replace :: "oterm \<Rightarrow> bool \<Rightarrow> oterm \<Rightarrow> oterm" where
  "C_PC_replace p b (Neg A) = Neg (C_PC_replace p b A)"
| "C_PC_replace p b (Conj A B) = Conj (C_PC_replace p b A) (C_PC_replace p b B)"
| "C_PC_replace p b (Disj A B) = Disj (C_PC_replace p b A) (C_PC_replace p b B)"
| "C_PC_replace p b (Imp A B) = Imp (C_PC_replace p b A) (C_PC_replace p b B)"
| "C_PC_replace p b A = (if A = p then C_boolean_constant b else A)"

lemma C_PC_atoms_typed:
  assumes typed: "\<Gamma> \<turnstile> A : Prop" and member: "a \<in> C_PC_atoms A"
  shows "\<Gamma> \<turnstile> a : Prop"
  using typed member by (induction A) (auto elim: has_type.cases)

lemma C_PC_atoms_constant:
  "C_PC_atoms (C_boolean_constant b) = {ObjTrue}"
  by (cases b) (simp_all add: C_boolean_constant_def ObjFalse_def ObjTrue_def)

lemma C_PC_replace_atoms:
  "C_PC_atoms (C_PC_replace p b A) \<subseteq> (C_PC_atoms A - {p}) \<union> {ObjTrue}"
  by (induction A) (auto simp: C_PC_atoms_constant)

lemma C_PC_replace_type:
  assumes typed: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> C_PC_replace p b A : Prop"
  using typed
proof (induction A)
  case (Neg A)
  have A: "\<Gamma> \<turnstile> A : Prop" using Neg.prems by (auto elim: has_type.cases)
  show ?case using has_type.Neg[OF Neg.IH[OF A]] by simp
next
  case (Conj A B)
  have A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    using Conj.prems by (auto elim: has_type.cases)
  show ?case using has_type.Conj[OF Conj.IH(1)[OF A] Conj.IH(2)[OF B]] by simp
next
  case (Disj A B)
  have A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    using Disj.prems by (auto elim: has_type.cases)
  show ?case using has_type.Disj[OF Disj.IH(1)[OF A] Disj.IH(2)[OF B]] by simp
next
  case (Imp A B)
  have A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop"
    using Imp.prems by (auto elim: has_type.cases)
  show ?case using has_type.Imp[OF Imp.IH(1)[OF A] Imp.IH(2)[OF B]] by simp
next
  case (Var n)
  show ?case using Var.prems C_boolean_constant_type by (simp split: if_splits)
next
  case (Const c \<tau>)
  show ?case using Const.prems C_boolean_constant_type by (simp split: if_splits)
next
  case (App A B)
  show ?case using App.prems C_boolean_constant_type by (simp split: if_splits)
next
  case (Lam \<tau> A)
  show ?case using Lam.prems C_boolean_constant_type by (simp split: if_splits)
next
  case (Eq \<tau> A B)
  show ?case using Eq.prems C_boolean_constant_type by (simp split: if_splits)
next
  case (Forall \<tau> A)
  show ?case using Forall.prems C_boolean_constant_type by (simp split: if_splits)
next
  case (Exists \<tau> A)
  show ?case using Exists.prems C_boolean_constant_type by (simp split: if_splits)
qed

subsection \<open>The qualified semantic cofactor equation\<close>

lemma C_PC_constant_eval:
  assumes truth: "w ObjTrue"
  shows "prop_eval w (C_boolean_constant b) = b"
  using truth by (cases b) (simp_all add: C_boolean_constant_def ObjFalse_def ObjTrue_def)

lemma C_PC_replace_eval:
  assumes truth: "w ObjTrue"
  shows "prop_eval w (C_PC_replace p b A) = prop_eval (w(p := b)) A"
  using truth by (induction A) (auto simp: C_PC_constant_eval)

lemma C_PC_update_preserves_truth:
  assumes truth: "w ObjTrue" and distinct: "p \<noteq> ObjTrue"
  shows "(w(p := b)) ObjTrue"
  using truth distinct by simp

lemma C_PC_replace_restricted_valid:
  assumes valid: "\<And>w. w ObjTrue \<Longrightarrow> prop_eval w A"
    and distinct: "p \<noteq> ObjTrue"
  shows "\<And>w. w ObjTrue \<Longrightarrow> prop_eval w (C_PC_replace p b A)"
proof -
  fix w
  assume truth: "w ObjTrue"
  have updated: "(w(p := b)) ObjTrue"
    by (rule C_PC_update_preserves_truth[where w=w and p=p and b=b, OF truth distinct])
  have evaluation: "prop_eval (w(p := b)) A"
    by (rule valid[where w="w(p := b)", OF updated])
  show "prop_eval w (C_PC_replace p b A)"
    using C_PC_replace_eval[where w=w and p=p and b=b and A=A, OF truth]
      evaluation by simp
qed

subsection \<open>Structural cofactor identity under its mask\<close>

lemma C_PC_replace_atomic_mask:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> p : Prop" and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (C_boolean_mask b p) A))
    (Lam \<sigma> (Conj (C_boolean_mask b p) (if A = p then C_boolean_constant b else A)))"
proof (cases "A = p")
  case True
  show ?thesis using C_boolean_mask_selected_atom[OF P, where b = b] by (simp add: True)
next
  case False
  have masked_type: "\<sigma> # \<Gamma> \<turnstile> Conj (C_boolean_mask b p) A : Prop"
    by (rule has_type.Conj[OF C_boolean_mask_type[OF P] A])
  show ?thesis using C_boolean_lambda_reflexive[OF masked_type] by (simp add: False)
qed

theorem C_PC_replace_mask_identity:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> p : Prop" and typed: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (C_boolean_mask b p) A))
    (Lam \<sigma> (Conj (C_boolean_mask b p) (C_PC_replace p b A)))"
  using typed
proof (induction A)
  case (Neg A)
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" using Neg.prems by (auto elim: has_type.cases)
  show ?case using C_boolean_mask_neg_congruence[OF C_boolean_mask_type[OF P]
    A C_PC_replace_type[OF A] Neg.IH[OF A]] by simp
next
  case (Conj A B)
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    using Conj.prems by (auto elim: has_type.cases)
  show ?case using C_boolean_mask_conj_congruence[OF C_boolean_mask_type[OF P]
    A C_PC_replace_type[OF A] B C_PC_replace_type[OF B] Conj.IH(1)[OF A] Conj.IH(2)[OF B]] by simp
next
  case (Disj A B)
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    using Disj.prems by (auto elim: has_type.cases)
  show ?case using C_boolean_mask_disj_congruence[OF C_boolean_mask_type[OF P]
    A C_PC_replace_type[OF A] B C_PC_replace_type[OF B] Disj.IH(1)[OF A] Disj.IH(2)[OF B]] by simp
next
  case (Imp A B)
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    using Imp.prems by (auto elim: has_type.cases)
  show ?case using C_boolean_mask_imp_congruence[OF C_boolean_mask_type[OF P]
    A C_PC_replace_type[OF A] B C_PC_replace_type[OF B] Imp.IH(1)[OF A] Imp.IH(2)[OF B]] by simp
next
  case (Var n)
  show ?case using C_PC_replace_atomic_mask[OF P Var.prems] by simp
next
  case (Const c \<tau>)
  show ?case using C_PC_replace_atomic_mask[OF P Const.prems] by simp
next
  case (App A B)
  show ?case using C_PC_replace_atomic_mask[OF P App.prems] by simp
next
  case (Lam \<tau> A)
  show ?case using C_PC_replace_atomic_mask[OF P Lam.prems] by simp
next
  case (Eq \<tau> A B)
  show ?case using C_PC_replace_atomic_mask[OF P Eq.prems] by simp
next
  case (Forall \<tau> A)
  show ?case using C_PC_replace_atomic_mask[OF P Forall.prems] by simp
next
  case (Exists \<tau> A)
  show ?case using C_PC_replace_atomic_mask[OF P Exists.prems] by simp
qed

theorem C_PC_Shannon_expansion:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> p : Prop" and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> A)
    (Lam \<sigma> (Disj (Conj p (C_PC_replace p True A))
      (Conj (Neg p) (C_PC_replace p False A))))"
proof -
  have positive: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj p A)) (Lam \<sigma> (Conj p (C_PC_replace p True A)))"
    using C_PC_replace_mask_identity[OF P A, where b = True] by (simp add: C_boolean_mask_def)
  have negative: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Conj (Neg p) A)) (Lam \<sigma> (Conj (Neg p) (C_PC_replace p False A)))"
    using C_PC_replace_mask_identity[OF P A, where b = False] by (simp add: C_boolean_mask_def)
  show ?thesis by (rule C_A1_trans[OF C_boolean_lambda_mask_split[OF P A]
    C_BA_disj_congruence[OF positive negative]])
qed

text \<open>
  The atom bound adds only ObjTrue, since ObjFalse = ¬ObjTrue.
  Thus choosing p ∈ At(A) − {ObjTrue} strictly decreases the finite
  nontruth-atom set in both cofactors.  Restricted validity at valuations
  with w ObjTrue = True is preserved because p is distinct from ObjTrue.
  This is the appropriate induction invariant for completing PC; arbitrary
  all-valuations tautology preservation of cofactors is not claimed.
\<close>

end
