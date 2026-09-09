theory Bacon_H_Quantifier_Proof_Basics
  imports Bacon_Base.Bacon_Deduction
begin

section \<open>H-only propositional and quantifier reasoning\<close>

text \<open>
  UI: ∀x:σ.A → A[T/x]; EG: A[T/x] → ∃x:σ.A.
  PC and MP supply the propositional consequences used below
  (Bacon–Dorr Figure 2, p.8). These will establish material equivalences
  between the bodies of the Figure 4 operations.

  Isabelle representation: H_proves is the represented full-F calculus
  with unrestricted typed-string constants. Γ is a type context.
  Status: H-only proofs; no C, CE, CEV, Equivalence rule, model, or
  object-language identity of the operations is imported or assumed.
  The represented IndividualExistence constructor is not used here.
\<close>

lemma Hq_PC:
  assumes typed: "\<Gamma> \<turnstile> A : Prop" and truth: "\<And>v. prop_eval v A"
  shows "\<Gamma> \<turnstile>\<^sub>H A"
proof (rule H_proves.PC)
  show "prop_tautology \<Gamma> A" unfolding prop_tautology_def
    by (rule conjI[OF typed], rule allI, rule truth)
qed

lemma Hq_PC_consequence:
  assumes proved: "\<Gamma> \<turnstile>\<^sub>H A" and target: "\<Gamma> \<turnstile> B : Prop"
    and truth: "\<And>v. prop_eval v A \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> \<turnstile>\<^sub>H B"
proof -
  have at: "\<Gamma> \<turnstile> A : Prop" by (rule H_proves_formula[OF proved])
  have bt: "\<Gamma> \<turnstile> Imp A B : Prop" by (rule has_type.Imp[OF at target])
  have bridge: "\<Gamma> \<turnstile>\<^sub>H Imp A B"
  proof (rule Hq_PC[OF bt])
    show "\<And>v. prop_eval v (Imp A B)" using truth by (simp only: prop_eval.simps; blast)
  qed
  show ?thesis by (rule H_proves.MP[OF proved bridge])
qed

lemma Hq_PC_two:
  assumes a: "\<Gamma> \<turnstile>\<^sub>H A" and b: "\<Gamma> \<turnstile>\<^sub>H B"
    and ct: "\<Gamma> \<turnstile> C : Prop"
    and truth: "\<And>v. prop_eval v A \<Longrightarrow> prop_eval v B \<Longrightarrow> prop_eval v C"
  shows "\<Gamma> \<turnstile>\<^sub>H C"
proof -
  have at: "\<Gamma> \<turnstile> A : Prop" by (rule H_proves_formula[OF a])
  have bt: "\<Gamma> \<turnstile> B : Prop" by (rule H_proves_formula[OF b])
  have typed: "\<Gamma> \<turnstile> Imp A (Imp B C) : Prop"
    by (rule has_type.Imp[OF at has_type.Imp[OF bt ct]])
  have bridge: "\<Gamma> \<turnstile>\<^sub>H Imp A (Imp B C)"
  proof (rule Hq_PC[OF typed])
    show "\<And>v. prop_eval v (Imp A (Imp B C))"
      using truth by (simp only: prop_eval.simps; blast)
  qed
  show ?thesis by (rule H_proves.MP[OF b H_proves.MP[OF a bridge]])
qed

lemma Hq_iff_intro:
  assumes at: "\<Gamma> \<turnstile> A : Prop" and bt: "\<Gamma> \<turnstile> B : Prop"
    and ab: "\<Gamma> \<turnstile>\<^sub>H Imp A B" and ba: "\<Gamma> \<turnstile>\<^sub>H Imp B A"
  shows "\<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
proof (rule Hq_PC_two[OF ab ba])
  show "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    by (intro has_type.Conj has_type.Imp at bt)
  show "\<And>v. prop_eval v (Imp A B) \<Longrightarrow> prop_eval v (Imp B A) \<Longrightarrow>
    prop_eval v (A \<longleftrightarrow>\<^sub>o B)" by (simp only: prop_eval.simps; blast)
qed

subsection \<open>Fresh-slot substitution calculations\<close>

text \<open>
  In a context with a new x:σ, ∀x.A instantiates to A and A yields ∃x.A.
  The old free variables must move past the new slot.
  Status: syntax algebra and H rules only; no quantifier identity is used.
\<close>

lemma Hq_subst_rename_inverse:
  assumes "\<And>n. s (r n) = Var n"
  shows "subst s (rename r A) = A"
  using assms
proof (induction A arbitrary: s r)
  case (Lam \<sigma> A)
  have "subst (lift_subst s) (rename (lift_ren r) A) = A"
    by (rule Lam.IH) (case_tac n; simp add: Lam.prems)
  then show ?case by simp
next
  case (Forall \<sigma> A)
  have "subst (lift_subst s) (rename (lift_ren r) A) = A"
    by (rule Forall.IH) (case_tac n; simp add: Forall.prems)
  then show ?case by simp
next
  case (Exists \<sigma> A)
  have "subst (lift_subst s) (rename (lift_ren r) A) = A"
    by (rule Exists.IH) (case_tac n; simp add: Exists.prems)
  then show ?case by simp
qed (simp_all only: rename.simps subst.simps)

lemma Hq_subst_shift:
  "subst (case_nat T Var) (rename Suc A) = A"
  by (rule Hq_subst_rename_inverse) simp

lemma Hq_slot_restore:
  "subst0 (Var 0) (rename (lift_ren Suc) A) = A"
  unfolding subst0_def
  by (rule Hq_subst_rename_inverse) (case_tac n; simp)

lemma Hq_insert_below_binder:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<sigma> # \<sigma> # \<Gamma> \<turnstile> rename (lift_ren Suc) A : Prop"
proof (rule renaming_preserves_typing[OF assms])
  fix n \<tau>
  assume look: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "lookup (\<sigma> # \<sigma> # \<Gamma>) (lift_ren Suc n) = Some \<tau>"
    using look by (cases n) simp_all
qed

lemma Hq_UI_here:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp (shift (Forall \<sigma> A)) A"
proof -
  have variable: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  note ui = H_proves.UI[OF Hq_insert_below_binder[OF assms] variable]
  show ?thesis using ui by (simp only: shift_def rename.simps Hq_slot_restore)
qed

lemma Hq_EG_here:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<sigma> # \<Gamma> \<turnstile>\<^sub>H Imp A (shift (Exists \<sigma> A))"
proof -
  have variable: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  note eg = H_proves.EG[OF Hq_insert_below_binder[OF assms] variable]
  show ?thesis using eg by (simp only: shift_def rename.simps Hq_slot_restore)
qed

lemma Hq_predicate_body_type:
  assumes "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "\<sigma> # \<Gamma> \<turnstile> App (shift F) (Var 0) : Prop"
  by (rule has_type.App[OF weakening_front[OF assms] has_type.Var[OF lookup_Cons_0]])

lemma Hq_predicate_subst0:
  "subst0 T (App (shift F) (Var 0)) = App F T"
  by (simp add: subst0_def shift_def Hq_subst_shift)

lemma Hq_UI_predicate:
  assumes F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop" and T: "\<Gamma> \<turnstile> T : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp (Forall \<sigma> (App (shift F) (Var 0))) (App F T)"
  using H_proves.UI[OF Hq_predicate_body_type[OF F] T] by (simp only: Hq_predicate_subst0)

lemma Hq_EG_predicate:
  assumes F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop" and T: "\<Gamma> \<turnstile> T : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>H Imp (App F T) (Exists \<sigma> (App (shift F) (Var 0)))"
  using H_proves.EG[OF Hq_predicate_body_type[OF F] T] by (simp only: Hq_predicate_subst0)

subsection \<open>The two absorption biconditionals\<close>

text \<open>
  FT ∨ ∀x.Fx ↔ FT, and FT ∧ ∃x.Fx ↔ FT.
  These are the material equivalences underlying Figure 4's absorption
  operations. F and T are arbitrary terms of the displayed types.
  Status: H biconditionals, not C identities of the corresponding λ-terms.
\<close>

theorem Hq_absorb_disj_forall:
  assumes F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop" and T: "\<Gamma> \<turnstile> T : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>H (Disj (App F T) (Forall \<sigma> (App (shift F) (Var 0)))
    \<longleftrightarrow>\<^sub>o App F T)"
proof (rule Hq_PC_consequence[OF Hq_UI_predicate[OF F T]])
  have ft: "\<Gamma> \<turnstile> App F T : Prop" by (rule has_type.App[OF F T])
  have qt: "\<Gamma> \<turnstile> Forall \<sigma> (App (shift F) (Var 0)) : Prop"
    by (rule has_type.Forall[OF Hq_predicate_body_type[OF F]])
  show "\<Gamma> \<turnstile> (Disj (App F T) (Forall \<sigma> (App (shift F) (Var 0)))
    \<longleftrightarrow>\<^sub>o App F T) : Prop"
    by (intro has_type.Conj has_type.Imp has_type.Disj ft qt)
  show "\<And>v. prop_eval v (Imp (Forall \<sigma> (App (shift F) (Var 0))) (App F T)) \<Longrightarrow>
    prop_eval v (Disj (App F T) (Forall \<sigma> (App (shift F) (Var 0))) \<longleftrightarrow>\<^sub>o App F T)"
    by (simp only: prop_eval.simps; blast)
qed

theorem Hq_absorb_conj_exists:
  assumes F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop" and T: "\<Gamma> \<turnstile> T : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>H (Conj (App F T) (Exists \<sigma> (App (shift F) (Var 0)))
    \<longleftrightarrow>\<^sub>o App F T)"
proof (rule Hq_PC_consequence[OF Hq_EG_predicate[OF F T]])
  have ft: "\<Gamma> \<turnstile> App F T : Prop" by (rule has_type.App[OF F T])
  have qt: "\<Gamma> \<turnstile> Exists \<sigma> (App (shift F) (Var 0)) : Prop"
    by (rule has_type.Exists[OF Hq_predicate_body_type[OF F]])
  show "\<Gamma> \<turnstile> (Conj (App F T) (Exists \<sigma> (App (shift F) (Var 0)))
    \<longleftrightarrow>\<^sub>o App F T) : Prop"
    by (intro has_type.Conj has_type.Imp ft qt)
  show "\<And>v. prop_eval v (Imp (App F T) (Exists \<sigma> (App (shift F) (Var 0)))) \<Longrightarrow>
    prop_eval v (Conj (App F T) (Exists \<sigma> (App (shift F) (Var 0))) \<longleftrightarrow>\<^sub>o App F T)"
    by (simp only: prop_eval.simps; blast)
qed

end
