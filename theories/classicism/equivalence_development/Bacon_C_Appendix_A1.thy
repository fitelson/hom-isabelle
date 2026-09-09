theory Bacon_C_Appendix_A1
  imports Bacon_C_Quantified_Truth
begin

section \<open>Bacon--Dorr Appendix A.1: universally quantified truth\<close>

text \<open>
  The represented A.1 result is ⊢C (∀x:σ.⊤₀) =ₜ ⊤₀ and hence
  ⊢C □∀x:σ.⊤₀, for every type σ.  Source: Bacon--Dorr Proposition A.1,
  p.65.  Here ⊤₀ := ∀p.(p → p), and □A abbreviates A =ₜ ⊤₀ in this
  implementation; the paper's primitive-basis conventions remain distinct.

  Isabelle representation.  ObjTrue represents ⊤₀.  The proof chooses
  the constant predicate λx:σ.(⊤₀ ∧ ¬⊤₀), applies universal absorption
  and distribution, and simplifies by the supplied Boolean identities.

  Status.  The concluding theorem and boxed corollary are derived in
  axiom-based C.  Neither Equivalence nor necessitation is used, and
  the proof does not require the unresolved identity ⊤ᴮ =ₜ ⊤₀.
\<close>

subsection \<open>Small equality-transport helpers\<close>

text \<open>
  Identities may be reversed and composed; if A =τ B, A =τ C,
  and B =τ D are C theorems, then ⊢C C =τ D.
  Sources: Bacon--Dorr Figure 2, p.8, Ref and LL; A.1, p.65.

  Isabelle representation.  These helpers also replace equal propositions
  in ∨ and in a constant quantified body.
  Status.  All hypotheses and conclusions are C identities.
\<close>

lemma C_A1_sym:
  assumes "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> A B"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> B A"
proof -
  have A: "\<Gamma> \<turnstile> A : \<tau>" and B: "\<Gamma> \<turnstile> B : \<tau>"
    using C_proves_formula[OF assms] by (auto elim: has_type.cases)
  show ?thesis by (rule C_closure_eq_sym_from[OF A B assms])
qed

lemma C_A1_trans:
  assumes AB: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> A B"
    and BC: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> B C"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> A C"
proof -
  have A: "\<Gamma> \<turnstile> A : \<tau>" and B: "\<Gamma> \<turnstile> B : \<tau>"
    and C: "\<Gamma> \<turnstile> C : \<tau>"
    using C_proves_formula[OF AB] C_proves_formula[OF BC]
    by (auto elim: has_type.cases)
  show ?thesis by (rule C_closure_eq_trans_from[OF A B C AB BC])
qed

lemma C_A1_transport:
  assumes AB: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> A B"
    and AC: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> A C"
    and BD: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> B D"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> C D"
  by (rule C_A1_trans[OF C_A1_trans[OF C_A1_sym[OF AC] AB] BD])

lemma C_A1_disj_congruence:
  assumes MN: "\<Gamma> \<turnstile>\<^sub>C Eq Prop M N"
    and PQ: "\<Gamma> \<turnstile>\<^sub>C Eq Prop P Q"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj M P) (Disj N Q)"
proof -
  have M: "\<Gamma> \<turnstile> M : Prop" and N: "\<Gamma> \<turnstile> N : Prop"
    and P: "\<Gamma> \<turnstile> P : Prop" and Q: "\<Gamma> \<turnstile> Q : Prop"
    using C_proves_formula[OF MN] C_proves_formula[OF PQ]
    by (auto elim: has_type.cases)
  have SP: "Prop # \<Gamma> \<turnstile> shift P : Prop" by (rule weakening_front[OF P])
  have SN: "Prop # \<Gamma> \<turnstile> shift N : Prop" by (rule weakening_front[OF N])
  have body1: "Prop # \<Gamma> \<turnstile> Disj (Var 0) (shift P) : Prop"
    using SP by auto
  have body2: "Prop # \<Gamma> \<turnstile> Disj (shift N) (Var 0) : Prop"
    using SN by auto
  have first: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj M P) (Disj N P)"
    using C_closure_congruence[OF M N body1 MN] by (simp add: subst0_def)
  have second: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj N P) (Disj N Q)"
    using C_closure_congruence[OF P Q body2 PQ] by (simp add: subst0_def)
  show ?thesis by (rule C_A1_trans[OF first second])
qed

lemma C_A1_forall_constant_congruence:
  assumes MN: "\<Gamma> \<turnstile>\<^sub>C Eq Prop M N"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Forall \<sigma> (shift M)) (Forall \<sigma> (shift N))"
proof -
  have M: "\<Gamma> \<turnstile> M : Prop" and N: "\<Gamma> \<turnstile> N : Prop"
    using C_proves_formula[OF MN] by (auto elim: has_type.cases)
  have body: "Prop # \<Gamma> \<turnstile> Forall \<sigma> (Var 1) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  show ?thesis using C_closure_congruence[OF M N body MN]
    by (simp add: subst0_def shift_def)
qed

subsection \<open>Two-argument source identities at arbitrary input types\<close>

text \<open>
  From ⊢C (λx:σ.λy:τ.P) = (λx:σ.λy:τ.Q), derive the identity
  between P[A/x,B/y] and Q[A/x,B/y].
  Sources: Bacon--Dorr Figure 4, p.13, and A.1, p.65.

  Isabelle representation.  The nested substitutions retain the first
  parameter while the second binder is processed.
  Status.  The argument types need not both be t.
\<close>

lemma C_A1_binary_instance:
  assumes P: "\<tau> # \<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q: "\<tau> # \<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and A: "\<Gamma> \<turnstile> A : \<sigma>" and B: "\<Gamma> \<turnstile> B : \<tau>"
    and FG: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o \<tau> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (Lam \<tau> P)) (Lam \<sigma> (Lam \<tau> Q))"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (subst0 B (subst (lift_subst (case_nat A Var)) P))
    (subst0 B (subst (lift_subst (case_nat A Var)) Q))"
proof -
  let ?F = "Lam \<sigma> (Lam \<tau> P)"
  let ?G = "Lam \<sigma> (Lam \<tau> Q)"
  have F: "\<Gamma> \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o \<tau> \<rightarrow>\<^sub>o Prop"
    by (intro has_type.Lam P)
  have G: "\<Gamma> \<turnstile> ?G : \<sigma> \<rightarrow>\<^sub>o \<tau> \<rightarrow>\<^sub>o Prop"
    by (intro has_type.Lam Q)
  have FA: "\<Gamma> \<turnstile> App ?F A : \<tau> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.App[OF F A])
  have GA: "\<Gamma> \<turnstile> App ?G A : \<tau> \<rightarrow>\<^sub>o Prop"
    by (rule has_type.App[OF G A])
  have first: "\<Gamma> \<turnstile>\<^sub>C Eq (\<tau> \<rightarrow>\<^sub>o Prop) (App ?F A) (App ?G A)"
    by (rule C_closure_app_congruence_left[OF F G A FG])
  have second: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (App (App ?F A) B) (App (App ?G A) B)"
    by (rule C_closure_app_congruence_left[OF FA GA B first])
  show ?thesis
    by (rule C_A1_transport[OF second
      C_closure_binary_beta_identity[OF P A B]
      C_closure_binary_beta_identity[OF Q A B]])
qed

subsection \<open>Constant Boolean bottom and its predicate\<close>

text \<open>
  Put b := ⊤₀ ∧ ¬⊤₀ and Bσ := λx:σ.b.  Then ⊢C Bσ A =ₜ b.
  Sources: Bacon--Dorr Figure 3, p.10, dissolution; Figure 2, p.8, β.

  Isabelle representation.  C_A1_bottom names b and C_A1_bottom_pred σ
  names Bσ.  Both are closed, so shifting does not change them.
  Status.  This is the particular contradiction used in the A.1 proof,
  not a declaration that every false proposition is identical to b.
\<close>

definition C_A1_bottom :: oterm where
  "C_A1_bottom = Conj ObjTrue (Neg ObjTrue)"

definition C_A1_bottom_pred :: "otype \<Rightarrow> oterm" where
  "C_A1_bottom_pred \<sigma> = Lam \<sigma> C_A1_bottom"

lemma C_A1_bottom_type:
  "\<Gamma> \<turnstile> C_A1_bottom : Prop"
  unfolding C_A1_bottom_def by (intro has_type.Conj has_type.Neg typed_ObjTrue)

lemma C_A1_bottom_pred_type:
  "\<Gamma> \<turnstile> C_A1_bottom_pred \<sigma> : \<sigma> \<rightarrow>\<^sub>o Prop"
  unfolding C_A1_bottom_pred_def by (intro has_type.Lam C_A1_bottom_type)

lemma C_A1_closed_terms[simp]:
  "shift ObjTrue = ObjTrue"
  "shift C_A1_bottom = C_A1_bottom"
  "shift (C_A1_bottom_pred \<sigma>) = C_A1_bottom_pred \<sigma>"
  by (simp_all add: shift_def ObjTrue_def C_A1_bottom_def C_A1_bottom_pred_def)

lemma C_A1_predicate_application:
  assumes T: "\<Gamma> \<turnstile> T : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq Prop (App (C_A1_bottom_pred \<sigma>) T) C_A1_bottom"
proof -
  have app: "\<Gamma> \<turnstile> App (C_A1_bottom_pred \<sigma>) T : Prop"
    by (rule has_type.App[OF C_A1_bottom_pred_type T])
  have step: "compatible_step beta_contract (App (C_A1_bottom_pred \<sigma>) T) C_A1_bottom"
  proof -
    have "compatible_step beta_contract (App (Lam \<sigma> C_A1_bottom) T)
      (subst0 T C_A1_bottom)"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis
      by (simp add: C_A1_bottom_pred_def C_A1_bottom_def ObjTrue_def subst0_def)
  qed
  show ?thesis by (rule C_closure_beta_identity[OF app C_A1_bottom_type step])
qed

lemma C_A1_quantified_predicate:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Forall \<sigma> (App (C_A1_bottom_pred \<sigma>) (Var 0))) (Forall \<sigma> C_A1_bottom)"
  using C_forall_predicate_beta[OF C_A1_bottom_type, where \<sigma> = \<sigma> and \<Gamma> = \<Gamma>]
  by (simp add: C_A1_bottom_pred_def shift_def C_A1_bottom_def ObjTrue_def)

subsection \<open>Appendix A.1, universal absorption instance\<close>

text \<open>
  Absorption gives ⊢C Bσ c ∨ (∀x:σ.Bσ x) =ₜ Bσ c.
  After β reduction and Boolean dissolution, ⊢C (∀x:σ.b) =ₜ b.
  Sources: Bacon--Dorr Figure 4, p.13, Absorption-∨∀; A.1, p.65.

  Isabelle representation.  The typed constant named A1-witness supplies c.
  Status.  The proof uses a constant instance, not a general necessitation rule.
\<close>

lemma C_A1_absorption_instance:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Disj (App (C_A1_bottom_pred \<sigma>) (Const ''A1-witness'' \<sigma>))
      (Forall \<sigma> (App (C_A1_bottom_pred \<sigma>) (Var 0))))
    (App (C_A1_bottom_pred \<sigma>) (Const ''A1-witness'' \<sigma>))"
proof -
  let ?P = "Disj (App (Var 1) (Var 0)) (Forall \<sigma> (App (Var 2) (Var 0)))"
  let ?Q = "App (Var 1) (Var 0)"
  have P: "\<sigma> # pred_ty \<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: lookup_def pred_ty_def)
  have Q: "\<sigma> # pred_ty \<sigma> # \<Gamma> \<turnstile> ?Q : Prop"
    by (rule infer_type_sound) (simp add: lookup_def pred_ty_def)
  have X: "\<Gamma> \<turnstile> C_A1_bottom_pred \<sigma> : pred_ty \<sigma>"
    using C_A1_bottom_pred_type[of \<Gamma> \<sigma>] by (simp add: pred_ty_def)
  have witness: "\<Gamma> \<turnstile> Const ''A1-witness'' \<sigma> : \<sigma>" by (rule has_type.Const)
  have eq: "\<Gamma> \<turnstile>\<^sub>C Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam (pred_ty \<sigma>) (Lam \<sigma> ?P)) (Lam (pred_ty \<sigma>) (Lam \<sigma> ?Q))"
    using C_proves.AbsorbDisjForall[of \<Gamma> \<sigma>]
    by (simp add: classic_absorb_disj_forall_def)
  show ?thesis using C_A1_binary_instance[OF P Q X witness eq]
    by (simp add: subst0_def numeral_2_eq_2 C_A1_bottom_pred_def C_A1_bottom_def ObjTrue_def)
qed

lemma C_A1_forall_bottom:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall \<sigma> C_A1_bottom) C_A1_bottom"
proof -
  let ?V = "App (C_A1_bottom_pred \<sigma>) (Const ''A1-witness'' \<sigma>)"
  let ?F = "Forall \<sigma> (App (C_A1_bottom_pred \<sigma>) (Var 0))"
  let ?B = "Forall \<sigma> C_A1_bottom"
  have V: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?V C_A1_bottom"
    by (rule C_A1_predicate_application) (rule has_type.Const)
  have norm: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj ?V ?F) (Disj C_A1_bottom ?B)"
    by (rule C_A1_disj_congruence[OF V C_A1_quantified_predicate])
  have absorb: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj C_A1_bottom ?B) C_A1_bottom"
    by (rule C_A1_transport[OF C_A1_absorption_instance norm V])
  have B: "\<Gamma> \<turnstile> ?B : Prop" by (rule has_type.Forall[OF C_A1_bottom_type])
  have dissolve: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj ?B C_A1_bottom) ?B"
    using C_boolean_disj_dissolves[OF B typed_ObjTrue] by (simp add: C_A1_bottom_def)
  have comm: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj ?B C_A1_bottom) (Disj C_A1_bottom ?B)"
    by (rule C_boolean_disj_commutes[OF B C_A1_bottom_type])
  show ?thesis by (rule C_A1_trans[OF C_A1_trans[OF C_A1_sym[OF dissolve] comm] absorb])
qed

subsection \<open>Appendix A.1, universal distribution instance\<close>

text \<open>
  Distribution gives ⊢C ⊤₀ ∨ (∀x:σ.Bσ x) =ₜ
  ∀x:σ.(⊤₀ ∨ Bσ x).
  Sources: Bacon--Dorr Figure 4, p.13, Distribution-∨∀; A.1, p.65.

  Isabelle representation.  Predicate β conversion and constant-body
  congruence normalize the two sides.
  Status.  The final theorem below identifies ∀x:σ.⊤₀ with ⊤₀ in C.
\<close>

lemma C_A1_distribution_instance:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Disj ObjTrue (Forall \<sigma> (App (C_A1_bottom_pred \<sigma>) (Var 0))))
    (Forall \<sigma> (Disj ObjTrue (App (C_A1_bottom_pred \<sigma>) (Var 0))))"
proof -
  let ?P = "Disj (Var 0) (Forall \<sigma> (App (Var 2) (Var 0)))"
  let ?Q = "Forall \<sigma> (Disj (Var 1) (App (Var 2) (Var 0)))"
  have P: "Prop # pred_ty \<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    by (rule infer_type_sound) (simp add: lookup_def pred_ty_def)
  have Q: "Prop # pred_ty \<sigma> # \<Gamma> \<turnstile> ?Q : Prop"
    by (rule infer_type_sound) (simp add: lookup_def pred_ty_def)
  have X: "\<Gamma> \<turnstile> C_A1_bottom_pred \<sigma> : pred_ty \<sigma>"
    using C_A1_bottom_pred_type[of \<Gamma> \<sigma>] by (simp add: pred_ty_def)
  have eq: "\<Gamma> \<turnstile>\<^sub>C Eq (pred_ty \<sigma> \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o Prop)
    (Lam (pred_ty \<sigma>) (Lam Prop ?P)) (Lam (pred_ty \<sigma>) (Lam Prop ?Q))"
    using C_proves.DistDisjForall[of \<Gamma> \<sigma>]
    by (simp add: classic_dist_disj_forall_def)
  show ?thesis using C_A1_binary_instance[OF P Q X typed_ObjTrue eq]
    by (simp add: subst0_def numeral_2_eq_2 C_A1_bottom_pred_def C_A1_bottom_def ObjTrue_def)
qed

lemma C_A1_quantified_disjunction:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Forall \<sigma> (Disj ObjTrue (App (C_A1_bottom_pred \<sigma>) (Var 0))))
    (Forall \<sigma> (Disj ObjTrue C_A1_bottom))"
proof -
  have var: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by (rule has_type.Var) simp
  have app: "\<sigma> # \<Gamma> \<turnstile> App (C_A1_bottom_pred \<sigma>) (Var 0) : Prop"
    by (rule has_type.App[OF C_A1_bottom_pred_type var])
  have L: "\<sigma> # \<Gamma> \<turnstile> Disj ObjTrue (App (C_A1_bottom_pred \<sigma>) (Var 0)) : Prop"
    by (rule has_type.Disj[OF typed_ObjTrue app])
  have R: "\<sigma> # \<Gamma> \<turnstile> Disj ObjTrue C_A1_bottom : Prop"
    by (rule has_type.Disj[OF typed_ObjTrue C_A1_bottom_type])
  have step: "compatible_step beta_contract
    (Disj ObjTrue (App (C_A1_bottom_pred \<sigma>) (Var 0))) (Disj ObjTrue C_A1_bottom)"
  proof -
    have "compatible_step beta_contract (App (Lam \<sigma> C_A1_bottom) (Var 0))
      (subst0 (Var 0) C_A1_bottom)"
      by (intro compatible_step.root beta_contract.beta)
    then have "compatible_step beta_contract (App (C_A1_bottom_pred \<sigma>) (Var 0)) C_A1_bottom"
      by (simp add: C_A1_bottom_pred_def C_A1_bottom_def ObjTrue_def subst0_def)
    then show ?thesis by (rule compatible_step.Disj_right)
  qed
  show ?thesis by (rule C_forall_beta_step_identity[OF L R step])
qed

text \<open>
  ⊢C (∀x:σ.⊤₀) =ₜ ⊤₀; hence ⊢C □∀x:σ.⊤₀.
  Locator: Bacon--Dorr Proposition A.1, p.65.

  Isabelle representation.  The theorem composes the absorption,
  distribution, and Boolean calculations above.  The boxed corollary
  unfolds ObjBox, whose meaning here is identity with ObjTrue.
  Status.  This represented A.1 result is proved; A.2 and A.3 are not.
\<close>

theorem C_Appendix_A1_universal_truth:
  "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Forall \<sigma> (shift ObjTrue)) ObjTrue"
proof -
  let ?F = "Forall \<sigma> (App (C_A1_bottom_pred \<sigma>) (Var 0))"
  let ?R = "Forall \<sigma> (Disj ObjTrue (App (C_A1_bottom_pred \<sigma>) (Var 0)))"
  have true_ref: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ObjTrue ObjTrue"
    by (intro C_proves.H H_proves.Ref typed_ObjTrue)
  have F_bottom: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?F C_A1_bottom"
    by (rule C_A1_trans[OF C_A1_quantified_predicate C_A1_forall_bottom])
  have left_norm: "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Disj ObjTrue ?F) (Disj ObjTrue C_A1_bottom)"
    by (rule C_A1_disj_congruence[OF true_ref F_bottom])
  have dissolve: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj ObjTrue C_A1_bottom) ObjTrue"
    using C_boolean_disj_dissolves[OF typed_ObjTrue typed_ObjTrue]
    by (simp add: C_A1_bottom_def)
  have left_truth: "\<Gamma> \<turnstile>\<^sub>C Eq Prop (Disj ObjTrue ?F) ObjTrue"
    by (rule C_A1_trans[OF left_norm dissolve])
  have constant_norm: "\<Gamma> \<turnstile>\<^sub>C Eq Prop
    (Forall \<sigma> (Disj ObjTrue C_A1_bottom)) (Forall \<sigma> ObjTrue)"
    using C_A1_forall_constant_congruence[OF dissolve, where \<sigma> = \<sigma>]
    by (simp add: shift_def C_A1_bottom_def ObjTrue_def)
  have right_truth: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ?R (Forall \<sigma> ObjTrue)"
    by (rule C_A1_trans[OF C_A1_quantified_disjunction constant_norm])
  have eq: "\<Gamma> \<turnstile>\<^sub>C Eq Prop ObjTrue (Forall \<sigma> ObjTrue)"
    by (rule C_A1_transport[OF C_A1_distribution_instance left_truth right_truth])
  show ?thesis using C_A1_sym[OF eq] by simp
qed

corollary C_Appendix_A1_boxed_universal_truth:
  "\<Gamma> \<turnstile>\<^sub>C \<box>\<^sub>o (Forall \<sigma> (shift ObjTrue))"
  using C_Appendix_A1_universal_truth[of \<Gamma> \<sigma>] by (simp add: ObjBox_def)

text \<open>
  The independent bridge ⊢C ⊤ᴮ =ₜ ⊤₀ is not proved here.
  Its remaining predicate-level premise is
  ⊢C (λp.¬p ∨ p) = (λp.⊤ᴮ).
  Locators: Bacon--Dorr Appendix A.2(i), p.65, and the use of Booleanism
  beneath abstraction in A.2(iv), pp.65–66.

  Isabelle representation.  C_boolean_truth names ⊤ᴮ.  The bridge
  would use C_forall_of_predicate_identity and C_ObjTrue_material_basis,
  together with the corresponding constant-truth quantifier calculation.

  Status.  Pointwise truth or pointwise identity of excluded middles does
  not itself establish this predicate identity.  The A.1 theorem above
  is independent of that remaining obligation.
\<close>

end
