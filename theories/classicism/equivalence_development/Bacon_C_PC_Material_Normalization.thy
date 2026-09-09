theory Bacon_C_PC_Material_Normalization
  imports Bacon_C_Predicate_Context
begin

section \<open>Structural normalization of the propositional skeleton\<close>

text \<open>
  Write N(A) for the recursive replacement of B → D by ¬N(B) ∨ N(D),
  commuting with ¬, ∧, and ∨.  Every other outer constructor is an
  opaque propositional atom.  We prove ⊢C (λv.A) = (λv.N(A)).
  Source use: Bacon--Dorr Appendix A.2(i), p.65; the primitive material
  implication equation connects the implementation's → with Figure 3.

  Isabelle representation.  The recursion follows exactly the Boolean
  constructors inspected by prop_eval.  It does not descend into an
  application, identity, abstraction, or quantifier regarded as an atom.
  Status.  This is a C-only, all-PC-skeleton normalization pass, not yet
  Boolean equational completeness or normalization of every tautology to ⊤₀.
\<close>

subsection \<open>Binary connective congruence at predicate type\<close>

lemma C_PC_binary_lambda_congruence:
  assumes connective: "f = Conj \<or> f = Disj \<or> f = Imp"
    and A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    and D: "\<sigma> # \<Gamma> \<turnstile> D : Prop"
    and E: "\<sigma> # \<Gamma> \<turnstile> E : Prop"
    and AB: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> B)"
    and DE: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> D) (Lam \<sigma> E)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (f A D)) (Lam \<sigma> (f B E))"
proof -
  have variable: "Prop # \<sigma> # \<Gamma> \<turnstile> Var 0 : Prop" by (rule has_type.Var) simp
  have SD: "Prop # \<sigma> # \<Gamma> \<turnstile> shift D : Prop" by (rule weakening_front[OF D])
  have SB: "Prop # \<sigma> # \<Gamma> \<turnstile> shift B : Prop" by (rule weakening_front[OF B])
  have P: "Prop # \<sigma> # \<Gamma> \<turnstile> f (Var 0) (shift D) : Prop"
    using connective has_type.Conj[OF variable SD] has_type.Disj[OF variable SD]
      has_type.Imp[OF variable SD] by blast
  have Q: "Prop # \<sigma> # \<Gamma> \<turnstile> f (shift B) (Var 0) : Prop"
    using connective has_type.Conj[OF SB variable] has_type.Disj[OF SB variable]
      has_type.Imp[OF SB variable] by blast
  have first_raw: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (subst0 A (f (Var 0) (shift D))))
    (Lam \<sigma> (subst0 B (f (Var 0) (shift D))))"
    by (rule C_predicate_context_replacement[OF A B P AB])
  have first: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (f A D)) (Lam \<sigma> (f B D))"
    using connective first_raw by (elim disjE; simp add: subst0_def)
  have second_raw: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (subst0 D (f (shift B) (Var 0))))
    (Lam \<sigma> (subst0 E (f (shift B) (Var 0))))"
    by (rule C_predicate_context_replacement[OF D E Q DE])
  have second: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (f B D)) (Lam \<sigma> (f B E))"
    using connective second_raw by (elim disjE; simp add: subst0_def)
  show ?thesis by (rule C_A1_trans[OF first second])
qed

lemma C_PC_lambda_material_imp:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Imp A B)) (Lam \<sigma> (Disj (Neg A) B))"
proof -
  have P: "Prop # Prop # \<Gamma> \<turnstile> Imp (Var 1) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  have Q: "Prop # Prop # \<Gamma> \<turnstile> Disj (Neg (Var 1)) (Var 0) : Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
  show ?thesis using C_binary_lambda_identity_instance[OF P Q A B
      C_closure_material_imp_operator]
    by (simp add: subst0_def C_subst_raised)
qed

subsection \<open>The implication-free skeleton and its invariants\<close>

fun C_PC_material_normalize :: "oterm \<Rightarrow> oterm" where
  "C_PC_material_normalize (Neg A) = Neg (C_PC_material_normalize A)"
| "C_PC_material_normalize (Conj A B) =
    Conj (C_PC_material_normalize A) (C_PC_material_normalize B)"
| "C_PC_material_normalize (Disj A B) =
    Disj (C_PC_material_normalize A) (C_PC_material_normalize B)"
| "C_PC_material_normalize (Imp A B) =
    Disj (Neg (C_PC_material_normalize A)) (C_PC_material_normalize B)"
| "C_PC_material_normalize A = A"

fun C_PC_imp_free :: "oterm \<Rightarrow> bool" where
  "C_PC_imp_free (Neg A) = C_PC_imp_free A"
| "C_PC_imp_free (Conj A B) = (C_PC_imp_free A \<and> C_PC_imp_free B)"
| "C_PC_imp_free (Disj A B) = (C_PC_imp_free A \<and> C_PC_imp_free B)"
| "C_PC_imp_free (Imp A B) = False"
| "C_PC_imp_free A = True"

lemma C_PC_material_normalize_imp_free:
  "C_PC_imp_free (C_PC_material_normalize A)"
  by (induction A) simp_all

lemma C_PC_material_normalize_idempotent:
  "C_PC_material_normalize (C_PC_material_normalize A) = C_PC_material_normalize A"
  by (induction A) simp_all

lemma C_PC_material_normalize_type:
  assumes A: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile> C_PC_material_normalize A : Prop"
  using A
proof (induction A)
  case (Neg A)
  have typed: "\<Gamma> \<turnstile> A : Prop" using Neg.prems by (cases rule: has_type.cases) simp_all
  show ?case using has_type.Neg[OF Neg.IH[OF typed]] by simp
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
  show ?case using has_type.Disj[OF has_type.Neg[OF Imp.IH(1)[OF A]] Imp.IH(2)[OF B]] by simp
qed simp_all

lemma C_PC_material_normalize_eval:
  "prop_eval v (C_PC_material_normalize A) = prop_eval v A"
  by (induction A) auto

lemma C_PC_material_normalize_tautology:
  assumes "prop_tautology \<Gamma> A"
  shows "prop_tautology \<Gamma> (C_PC_material_normalize A)"
  using assms C_PC_material_normalize_type C_PC_material_normalize_eval
  unfolding prop_tautology_def by blast

subsection \<open>Constructor induction in axiom-based C\<close>

lemma C_PC_lambda_reflexive:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> A)"
  by (rule C_proves.H, rule H_proves.Ref, rule has_type.Lam[OF assms])

text \<open>
  If A:t in the context of v:σ, then ⊢C (λv.A) = (λv.N(A)).
  The induction covers arbitrary nesting of all four PC connectives.
  At each binary node, previously established predicate identities are
  replaced in the corresponding typed connective context.

  Isabelle representation.  Non-Boolean constructors are unchanged and
  discharged by Ref, even when their internal syntax contains →.
  Status.  The result justifies this syntactic normalization in C itself;
  preservation of prop_eval alone would not establish predicate identity.
\<close>

theorem C_PC_material_normalize_under_lambda:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> A) (Lam \<sigma> (C_PC_material_normalize A))"
  using A
proof (induction A)
  case (Neg A)
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    using Neg.prems by (auto elim: has_type.cases)
  have normalized: "\<sigma> # \<Gamma> \<turnstile> C_PC_material_normalize A : Prop"
    by (rule C_PC_material_normalize_type[OF A])
  show ?case using C_boolean_lambda_neg_congruence[OF A normalized Neg.IH[OF A]] by simp
next
  case (Conj A B)
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    using Conj.prems by (auto elim: has_type.cases)
  have NA: "\<sigma> # \<Gamma> \<turnstile> C_PC_material_normalize A : Prop"
    by (rule C_PC_material_normalize_type[OF A])
  have NB: "\<sigma> # \<Gamma> \<turnstile> C_PC_material_normalize B : Prop"
    by (rule C_PC_material_normalize_type[OF B])
  have connective: "Conj = Conj \<or> Conj = Disj \<or> Conj = Imp" by (rule disjI1) (rule refl)
  show ?case using C_PC_binary_lambda_congruence[OF connective A NA B NB
      Conj.IH(1)[OF A] Conj.IH(2)[OF B]] by simp
next
  case (Disj A B)
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    using Disj.prems by (auto elim: has_type.cases)
  have NA: "\<sigma> # \<Gamma> \<turnstile> C_PC_material_normalize A : Prop"
    by (rule C_PC_material_normalize_type[OF A])
  have NB: "\<sigma> # \<Gamma> \<turnstile> C_PC_material_normalize B : Prop"
    by (rule C_PC_material_normalize_type[OF B])
  have connective: "Disj = Conj \<or> Disj = Disj \<or> Disj = Imp"
    by (rule disjI2, rule disjI1, rule refl)
  show ?case using C_PC_binary_lambda_congruence[OF connective A NA B NB
      Disj.IH(1)[OF A] Disj.IH(2)[OF B]] by simp
next
  case (Imp A B)
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and B: "\<sigma> # \<Gamma> \<turnstile> B : Prop"
    using Imp.prems by (auto elim: has_type.cases)
  have NA: "\<sigma> # \<Gamma> \<turnstile> C_PC_material_normalize A : Prop"
    by (rule C_PC_material_normalize_type[OF A])
  have NB: "\<sigma> # \<Gamma> \<turnstile> C_PC_material_normalize B : Prop"
    by (rule C_PC_material_normalize_type[OF B])
  have connective: "Imp = Conj \<or> Imp = Disj \<or> Imp = Imp"
    by (rule disjI2, rule disjI2, rule refl)
  have congruence: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
    (Lam \<sigma> (Imp A B))
    (Lam \<sigma> (Imp (C_PC_material_normalize A) (C_PC_material_normalize B)))"
    by (rule C_PC_binary_lambda_congruence[OF connective A NA B NB
      Imp.IH(1)[OF A] Imp.IH(2)[OF B]])
  show ?case using C_A1_trans[OF congruence C_PC_lambda_material_imp[OF NA NB]] by simp
next
  case (Var n)
  show ?case by (simp only: C_PC_material_normalize.simps;
      rule C_PC_lambda_reflexive[OF Var.prems])
next
  case (Const c \<tau>)
  show ?case by (simp only: C_PC_material_normalize.simps;
      rule C_PC_lambda_reflexive[OF Const.prems])
next
  case (App F B)
  show ?case by (simp only: C_PC_material_normalize.simps;
      rule C_PC_lambda_reflexive[OF App.prems])
next
  case (Lam \<tau> B)
  show ?case by (simp only: C_PC_material_normalize.simps;
      rule C_PC_lambda_reflexive[OF Lam.prems])
next
  case (Eq \<tau> B D)
  show ?case by (simp only: C_PC_material_normalize.simps;
      rule C_PC_lambda_reflexive[OF Eq.prems])
next
  case (Forall \<tau> B)
  show ?case by (simp only: C_PC_material_normalize.simps;
      rule C_PC_lambda_reflexive[OF Forall.prems])
next
  case (Exists \<tau> B)
  show ?case by (simp only: C_PC_material_normalize.simps;
      rule C_PC_lambda_reflexive[OF Exists.prems])
qed

corollary C_PC_imp_free_tautology_reduction:
  assumes tautology: "prop_tautology (\<sigma> # \<Gamma>) A"
    and normalized: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop)
      (Lam \<sigma> (C_PC_material_normalize A)) (Lam \<sigma> ObjTrue)"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma> A) (Lam \<sigma> ObjTrue)"
proof -
  have A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    using tautology by (simp add: prop_tautology_def)
  show ?thesis by (rule C_A1_trans[OF C_PC_material_normalize_under_lambda[OF A] normalized])
qed

text \<open>
  The remaining PC obligation may now be restricted to implication-free
  Boolean skeletons: from prop_tautology (σ # Γ) B and C_PC_imp_free B,
  derive ⊢C (λv.B) = (λv.⊤₀).  That requires the equational completeness
  argument for the supplied Boolean identities, followed separately by
  the abstraction-vector argument.  Neither is hidden in this reduction.
\<close>

end
