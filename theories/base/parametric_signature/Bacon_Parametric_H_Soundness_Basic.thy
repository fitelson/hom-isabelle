theory Bacon_Parametric_H_Soundness_Basic
  imports Bacon_Parametric_Deduction Bacon_Parametric_BBK_Semantics
begin

section \<open>Truth of the H axiom schemata in arbitrary-name BBK models\<close>

text \<open>
  Σ; Γ ⊢H A ⇒ M,g ⊨ A, for each model M of Σ and each Γ-typed g,
  is the soundness direction of Bacon–Dorr Theorem 3.2.

  Isabelle representation: within pbbk_model, the following lemmas check the
  H axiom schemata and MP against denote/valuation.  pH_BBK_prop_eval
  relates V(⟦A⟧ᴹᵍ) to the syntactic Boolean evaluator.

  Status: axiom and MP soundness for arbitrary names/signatures.  Gen, Inst,
  and induction on all derivations are in H_Soundness; no completeness is
  claimed by these local validity lemmas.
\<close>

context pbbk_model
begin

lemma pH_BBK_prop_eval:
  assumes typed: "has_ptype \<Gamma> A Prop" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g A) = pprop_eval (\<lambda>B. valuation (denote g B)) A"
  using typed sig env
proof (induction A arbitrary: \<Gamma> g)
  case (PNeg A)
  have A: "has_ptype \<Gamma> A Prop" using PNeg.prems(1) by (auto elim: has_ptype.cases)
  have sigA: "pterm_in_signature signature A" using PNeg.prems(2) by simp
  have rec: "valuation (denote g A) = pprop_eval (\<lambda>B. valuation (denote g B)) A"
    by (rule PNeg.IH[where \<Gamma>=\<Gamma> and g=g, OF A sigA PNeg.prems(3)])
  show ?case by (simp only: valuation_neg[OF A sigA PNeg.prems(3)] pprop_eval.simps rec)
next
  case (PConj A B)
  have A: "has_ptype \<Gamma> A Prop" and B: "has_ptype \<Gamma> B Prop"
    using PConj.prems(1) by (auto elim: has_ptype.cases)
  have sigA: "pterm_in_signature signature A" and sigB: "pterm_in_signature signature B"
    using PConj.prems(2) by simp_all
  have left: "valuation (denote g A) = pprop_eval (\<lambda>C. valuation (denote g C)) A"
    by (rule PConj.IH(1)[where \<Gamma>=\<Gamma> and g=g, OF A sigA PConj.prems(3)])
  have right: "valuation (denote g B) = pprop_eval (\<lambda>C. valuation (denote g C)) B"
    by (rule PConj.IH(2)[where \<Gamma>=\<Gamma> and g=g, OF B sigB PConj.prems(3)])
  show ?case by (simp only: valuation_conj[OF A B sigA sigB PConj.prems(3)] pprop_eval.simps left right)
next
  case (PDisj A B)
  have A: "has_ptype \<Gamma> A Prop" and B: "has_ptype \<Gamma> B Prop"
    using PDisj.prems(1) by (auto elim: has_ptype.cases)
  have sigA: "pterm_in_signature signature A" and sigB: "pterm_in_signature signature B"
    using PDisj.prems(2) by simp_all
  have left: "valuation (denote g A) = pprop_eval (\<lambda>C. valuation (denote g C)) A"
    by (rule PDisj.IH(1)[where \<Gamma>=\<Gamma> and g=g, OF A sigA PDisj.prems(3)])
  have right: "valuation (denote g B) = pprop_eval (\<lambda>C. valuation (denote g C)) B"
    by (rule PDisj.IH(2)[where \<Gamma>=\<Gamma> and g=g, OF B sigB PDisj.prems(3)])
  show ?case by (simp only: valuation_disj[OF A B sigA sigB PDisj.prems(3)] pprop_eval.simps left right)
next
  case (PImp A B)
  have A: "has_ptype \<Gamma> A Prop" and B: "has_ptype \<Gamma> B Prop"
    using PImp.prems(1) by (auto elim: has_ptype.cases)
  have sigA: "pterm_in_signature signature A" and sigB: "pterm_in_signature signature B"
    using PImp.prems(2) by simp_all
  have left: "valuation (denote g A) = pprop_eval (\<lambda>C. valuation (denote g C)) A"
    by (rule PImp.IH(1)[where \<Gamma>=\<Gamma> and g=g, OF A sigA PImp.prems(3)])
  have right: "valuation (denote g B) = pprop_eval (\<lambda>C. valuation (denote g C)) B"
    by (rule PImp.IH(2)[where \<Gamma>=\<Gamma> and g=g, OF B sigB PImp.prems(3)])
  show ?case by (simp only: valuation_imp[OF A B sigA sigB PImp.prems(3)] pprop_eval.simps left right)
qed simp_all

lemma pH_BBK_PC:
  assumes taut: "pprop_tautology \<Gamma> A" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g A)"
proof -
  have typed: "has_ptype \<Gamma> A Prop" using taut unfolding pprop_tautology_def by blast
  have truth: "pprop_eval (\<lambda>B. valuation (denote g B)) A"
    using taut unfolding pprop_tautology_def by blast
  show ?thesis using truth by (simp only: pH_BBK_prop_eval[OF typed sig env])
qed

text \<open>
  M,g ⊨ ∃x:e(x =e x) because De is nonempty.

  Isabelle representation: pH_BBK_IndividualExistence selects a semantic domain
  element and uses actual-identity truth; it does not require a named
  constant from Σe.

  Status: validity of the explicit IndividualExistence axiom.
\<close>

lemma pH_BBK_IndividualExistence:
  assumes env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (PExists Ind (PEq Ind (PVar 0) (PVar 0))))"
proof -
  have zero: "has_ptype (Ind # \<Gamma>) (PVar 0) Ind" by (rule has_ptype.PVar) simp
  have body: "has_ptype (Ind # \<Gamma>) (PEq Ind (PVar 0) (PVar 0)) Prop"
    by (rule has_ptype.PEq[OF zero zero])
  have sigzero: "pterm_in_signature signature (PVar 0)" by simp
  have sigbody: "pterm_in_signature signature (PEq Ind (PVar 0) (PVar 0))" by simp
  obtain a where domain: "a \<in> domain Ind" using domain_nonempty[of Ind] by blast
  have extended: "pbbk_env_typed domain (Ind # \<Gamma>) (pbbk_extend a g)"
    by (rule pbbk_env_extend[OF env domain])
  have truth: "valuation (denote (pbbk_extend a g) (PEq Ind (PVar 0) (PVar 0)))"
    by (simp only: valuation_identity[OF zero zero sigzero sigzero extended] refl)
  have witness: "\<exists>a \<in> domain Ind. valuation (denote (pbbk_extend a g) (PEq Ind (PVar 0) (PVar 0)))"
    by (rule bexI[where x=a]) (rule truth, rule domain)
  show ?thesis using witness by (simp only: valuation_exists[OF body sigbody env])
qed

text \<open>
  M,g ⊨ (∀v:σ.A) → A[B/v] and M,g ⊨ A[B/v] → ∃v:σ.A for B:σ.

  Isabelle representation: pH_BBK_UI and pH_BBK_EG use the value ⟦B⟧ᴹᵍ as a
  quantified instance and invoke pbbk_one_binder.

  Status: UI/EG validity with both A and B in the model’s actual language.
\<close>

lemma pH_BBK_UI:
  assumes body: "has_ptype (\<sigma> # \<Gamma>) A Prop" and arg: "has_ptype \<Gamma> T \<sigma>"
    and sigA: "pterm_in_signature signature A" and sigT: "pterm_in_signature signature T"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (PImp (PForall \<sigma> A) (psubst0 T A)))"
proof -
  have quantified: "has_ptype \<Gamma> (PForall \<sigma> A) Prop" by (rule has_ptype.PForall[OF body])
  have instantiated: "has_ptype \<Gamma> (psubst0 T A) Prop" by (rule psubst0_preserves_typing[OF body arg])
  have sigQ: "pterm_in_signature signature (PForall \<sigma> A)" using sigA by simp
  have sigI: "pterm_in_signature signature (psubst0 T A)" by (rule psubst0_signature[OF sigA sigT])
  have element: "denote g T \<in> domain \<sigma>" by (rule denote_type[OF arg sigT env])
  have substitution: "denote (pbbk_extend (denote g T) g) A = denote g (psubst0 T A)"
    by (rule pbbk_one_binder[OF body arg sigA sigT env])
  have condition: "valuation (denote g (PForall \<sigma> A)) \<longrightarrow> valuation (denote g (psubst0 T A))"
  proof (rule impI)
    assume all_true: "valuation (denote g (PForall \<sigma> A))"
    have all_instances: "\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) A)"
      using all_true by (simp only: valuation_forall[OF body sigA env])
    have instance_true: "valuation (denote (pbbk_extend (denote g T) g) A)"
      by (rule bspec[OF all_instances element])
    show "valuation (denote g (psubst0 T A))"
      using instance_true by (simp only: substitution)
  qed
  show ?thesis using condition by (simp only: valuation_imp[OF quantified instantiated sigQ sigI env])
qed

lemma pH_BBK_EG:
  assumes body: "has_ptype (\<sigma> # \<Gamma>) A Prop" and arg: "has_ptype \<Gamma> T \<sigma>"
    and sigA: "pterm_in_signature signature A" and sigT: "pterm_in_signature signature T"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (PImp (psubst0 T A) (PExists \<sigma> A)))"
proof -
  have quantified: "has_ptype \<Gamma> (PExists \<sigma> A) Prop" by (rule has_ptype.PExists[OF body])
  have instantiated: "has_ptype \<Gamma> (psubst0 T A) Prop" by (rule psubst0_preserves_typing[OF body arg])
  have sigQ: "pterm_in_signature signature (PExists \<sigma> A)" using sigA by simp
  have sigI: "pterm_in_signature signature (psubst0 T A)" by (rule psubst0_signature[OF sigA sigT])
  have element: "denote g T \<in> domain \<sigma>" by (rule denote_type[OF arg sigT env])
  have substitution: "denote (pbbk_extend (denote g T) g) A = denote g (psubst0 T A)"
    by (rule pbbk_one_binder[OF body arg sigA sigT env])
  have condition: "valuation (denote g (psubst0 T A)) \<longrightarrow> valuation (denote g (PExists \<sigma> A))"
  proof (rule impI)
    assume instance_true: "valuation (denote g (psubst0 T A))"
    have witness_true: "valuation (denote (pbbk_extend (denote g T) g) A)"
      using instance_true by (simp only: substitution)
    have witness: "\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a g) A)"
    proof (rule bexI[where x="denote g T"])
      show "valuation (denote (pbbk_extend (denote g T) g) A)" by (rule witness_true)
      show "denote g T \<in> domain \<sigma>" by (rule element)
    qed
    show "valuation (denote g (PExists \<sigma> A))"
      using witness by (simp only: valuation_exists[OF body sigA env])
  qed
  show ?thesis using condition by (simp only: valuation_imp[OF instantiated quantified sigI sigQ env])
qed

text \<open>
  M,g ⊨ A =σ A; if M,g ⊨ A =σ B and M,g ⊨ FA, then M,g ⊨ FB.

  Isabelle representation: pH_BBK_Ref and pH_BBK_LL use actual equality of
  denotations and application coherence.

  Status: Ref/LL validity.  This is not an extensionality or Functionality
  axiom.
\<close>

lemma pH_BBK_Ref:
  assumes typed: "has_ptype \<Gamma> A \<sigma>" and sig: "pterm_in_signature signature A"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (PEq \<sigma> A A))"
  by (simp only: valuation_identity[OF typed typed sig sig env] refl)

lemma pH_BBK_LL:
  assumes A: "has_ptype \<Gamma> A \<sigma>" and B: "has_ptype \<Gamma> B \<sigma>"
    and F: "has_ptype \<Gamma> F (\<sigma> \<rightarrow>\<^sub>o Prop)"
    and sigA: "pterm_in_signature signature A" and sigB: "pterm_in_signature signature B"
    and sigF: "pterm_in_signature signature F" and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (PImp (PEq \<sigma> A B) (PImp (PApp F A) (PApp F B))))"
proof -
  have eqt: "has_ptype \<Gamma> (PEq \<sigma> A B) Prop" by (rule has_ptype.PEq[OF A B])
  have FA: "has_ptype \<Gamma> (PApp F A) Prop" by (rule has_ptype.PApp[OF F A])
  have FB: "has_ptype \<Gamma> (PApp F B) Prop" by (rule has_ptype.PApp[OF F B])
  have implication: "has_ptype \<Gamma> (PImp (PApp F A) (PApp F B)) Prop" by (rule has_ptype.PImp[OF FA FB])
  have sigFA: "pterm_in_signature signature (PApp F A)" and sigFB: "pterm_in_signature signature (PApp F B)"
    using sigF sigA sigB by simp_all
  have sigEq: "pterm_in_signature signature (PEq \<sigma> A B)"
    and sigImp: "pterm_in_signature signature (PImp (PApp F A) (PApp F B))"
    using sigA sigB sigFA sigFB by simp_all
  have condition: "valuation (denote g (PEq \<sigma> A B)) \<longrightarrow>
      (valuation (denote g (PApp F A)) \<longrightarrow> valuation (denote g (PApp F B)))"
  proof (intro impI)
    assume equality: "valuation (denote g (PEq \<sigma> A B))" and truth: "valuation (denote g (PApp F A))"
    have same: "denote g A = denote g B" using valuation_identity[OF A B sigA sigB env] equality by blast
    have apps: "denote g (PApp F A) = denote g (PApp F B)"
      by (rule denote_application_cong[OF F A F B sigFA sigFB env env refl same])
    show "valuation (denote g (PApp F B))" using apps truth by simp
  qed
  show ?thesis using condition
    by (simp only: valuation_imp[OF eqt implication sigEq sigImp env] valuation_imp[OF FA FB sigFA sigFB env])
qed

text \<open>
  A ≡βη B within ℒ(Σ) preserves denotation, so propositionally typed
  endpoints satisfy M,g ⊨ A ↔ B.

  Isabelle representation: pH_BBK_conversion uses the signature-indexed
  denote_beta_eta clause; the Beta and Eta lemmas construct its corresponding
  guarded compatible step.

  Status: validity of the formula conversion axioms, not identity inferred
  from an arbitrary true biconditional.
\<close>

lemma pH_BBK_conversion:
  assumes conversion: "pbeta_eta_equiv_in_signature signature \<Gamma> Prop A B"
    and sigA: "pterm_in_signature signature A" and sigB: "pterm_in_signature signature B"
    and env: "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (PObjIff A B))"
proof -
  have A: "has_ptype \<Gamma> A Prop" and B: "has_ptype \<Gamma> B Prop"
    using pbeta_eta_equiv_in_signature_data[OF conversion] by blast+
  have AB: "has_ptype \<Gamma> (PImp A B) Prop" by (rule has_ptype.PImp[OF A B])
  have BA: "has_ptype \<Gamma> (PImp B A) Prop" by (rule has_ptype.PImp[OF B A])
  have sigAB: "pterm_in_signature signature (PImp A B)" and sigBA: "pterm_in_signature signature (PImp B A)"
    using sigA sigB by simp_all
  have same: "denote g A = denote g B" by (rule denote_beta_eta[OF conversion sigA sigB env])
  show ?thesis
    by (simp only: valuation_conj[OF AB BA sigAB sigBA env] valuation_imp[OF A B sigA sigB env]
          valuation_imp[OF B A sigB sigA env] same simp_thms)
qed

lemma pH_BBK_Beta:
  assumes "has_ptype \<Gamma> A Prop" and "has_ptype \<Gamma> B Prop" and "pcompatible_step pbeta_contract A B"
    and "pterm_in_signature signature A" and "pterm_in_signature signature B" and "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (PObjIff A B))"
  by (rule pH_BBK_conversion[OF
      pbeta_eta_equiv_in_signature.Beta[OF assms(1,2,4,5,3)] assms(4,5,6)])

lemma pH_BBK_Eta:
  assumes "has_ptype \<Gamma> A Prop" and "has_ptype \<Gamma> B Prop" and "pcompatible_step peta_contract A B"
    and "pterm_in_signature signature A" and "pterm_in_signature signature B" and "pbbk_env_typed domain \<Gamma> g"
  shows "valuation (denote g (PObjIff A B))"
  by (rule pH_BBK_conversion[OF
      pbeta_eta_equiv_in_signature.Eta[OF assms(1,2,4,5,3)] assms(4,5,6)])

text \<open>
  M,g ⊨ A and M,g ⊨ A → B entail M,g ⊨ B.

  Isabelle representation: pH_BBK_MP applies the primitive implication truth
  clause to two established truths in one typed environment.

  Status: truth preservation by MP; closure of all H derivations is proved
  in the following theory.
\<close>

lemma pH_BBK_MP:
  assumes A: "has_ptype \<Gamma> A Prop" and B: "has_ptype \<Gamma> B Prop"
    and sigA: "pterm_in_signature signature A" and sigB: "pterm_in_signature signature B"
    and env: "pbbk_env_typed domain \<Gamma> g"
    and truth: "valuation (denote g A)" and implication: "valuation (denote g (PImp A B))"
  shows "valuation (denote g B)"
  using valuation_imp[OF A B sigA sigB env] truth implication by blast

end
end
