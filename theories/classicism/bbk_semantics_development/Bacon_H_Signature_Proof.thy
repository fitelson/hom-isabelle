theory Bacon_H_Signature_Proof
  imports Bacon_BBK_H_Soundness_Quantifiers
begin

section \<open>H proofs in a represented signature\<close>

text \<open>
  Σ; Γ ⊢ₕ A means theoremhood in L(Σ), with Γ recording free-variable types.
  Bacon–Dorr, Figure 2; Theorem 3.2, pp. 44–45.

  Isabelle representation: H_signature_proves mirrors H_proves and guards every
  displayed term, including intermediate formulas. Σ is a family of sets of string
  names.

  Status: Embedding and signature-local soundness are proved; converse conservativity
  for unrestricted proofs is not claimed here.
\<close>

inductive H_signature_proves :: "bbk_signature \<Rightarrow> ctx \<Rightarrow> oterm \<Rightarrow> bool"
  for \<Sigma> :: bbk_signature where
  PC: "prop_tautology \<Gamma> A \<Longrightarrow> bbk_in_signature \<Sigma> A \<Longrightarrow>
    H_signature_proves \<Sigma> \<Gamma> A"
| IndividualExistence:
    "H_signature_proves \<Sigma> \<Gamma> (Exists Ind (Eq Ind (Var 0) (Var 0)))"
| UI: "\<sigma> # \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> T : \<sigma> \<Longrightarrow>
    bbk_in_signature \<Sigma> A \<Longrightarrow> bbk_in_signature \<Sigma> T \<Longrightarrow>
    H_signature_proves \<Sigma> \<Gamma> (Imp (Forall \<sigma> A) (subst0 T A))"
| EG: "\<sigma> # \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> T : \<sigma> \<Longrightarrow>
    bbk_in_signature \<Sigma> A \<Longrightarrow> bbk_in_signature \<Sigma> T \<Longrightarrow>
    H_signature_proves \<Sigma> \<Gamma> (Imp (subst0 T A) (Exists \<sigma> A))"
| Ref: "\<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> bbk_in_signature \<Sigma> M \<Longrightarrow>
    H_signature_proves \<Sigma> \<Gamma> (Eq \<sigma> M M)"
| LL: "\<Gamma> \<turnstile> A : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> B : \<sigma> \<Longrightarrow>
    \<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop \<Longrightarrow>
    bbk_in_signature \<Sigma> A \<Longrightarrow> bbk_in_signature \<Sigma> B \<Longrightarrow>
    bbk_in_signature \<Sigma> F \<Longrightarrow>
    H_signature_proves \<Sigma> \<Gamma>
      (Imp (Eq \<sigma> A B) (Imp (App F A) (App F B)))"
| Beta: "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
    compatible_step beta_contract A B \<Longrightarrow>
    bbk_in_signature \<Sigma> A \<Longrightarrow> bbk_in_signature \<Sigma> B \<Longrightarrow>
    H_signature_proves \<Sigma> \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
| Eta: "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow>
    compatible_step eta_contract A B \<Longrightarrow>
    bbk_in_signature \<Sigma> A \<Longrightarrow> bbk_in_signature \<Sigma> B \<Longrightarrow>
    H_signature_proves \<Sigma> \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
| MP: "H_signature_proves \<Sigma> \<Gamma> A \<Longrightarrow>
    H_signature_proves \<Sigma> \<Gamma> (Imp A B) \<Longrightarrow>
    bbk_in_signature \<Sigma> A \<Longrightarrow> bbk_in_signature \<Sigma> B \<Longrightarrow>
    H_signature_proves \<Sigma> \<Gamma> B"
| Gen: "\<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    bbk_in_signature \<Sigma> P \<Longrightarrow> bbk_in_signature \<Sigma> Q \<Longrightarrow>
    H_signature_proves \<Sigma> (\<sigma> # \<Gamma>) (Imp (shift P) Q) \<Longrightarrow>
    H_signature_proves \<Sigma> \<Gamma> (Imp P (Forall \<sigma> Q))"
| Inst: "\<sigma> # \<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop \<Longrightarrow>
    bbk_in_signature \<Sigma> P \<Longrightarrow> bbk_in_signature \<Sigma> Q \<Longrightarrow>
    H_signature_proves \<Sigma> (\<sigma> # \<Gamma>) (Imp P (shift Q)) \<Longrightarrow>
    H_signature_proves \<Sigma> \<Gamma> (Imp (Exists \<sigma> P) Q)"

subsection \<open>Forgetting the signature and preserving well-formedness\<close>

text \<open>
  Σ; Γ ⊢ₕ A ⇒ Γ ⊢ₕ A, Γ ⊢ A : t, and A ∈ L(Σ). Bacon–Dorr, Figure 2; Theorem 3.2, pp.
  44–45.

  Isabelle representation: The signature-indexed induction erases guards to obtain
  H_proves and separately preserves the language predicate.

  Status: Only the forward embedding is established; no proof-locality converse
  follows automatically.
\<close>

theorem H_signature_proves_imp_H_proves:
  assumes "H_signature_proves \<Sigma> \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>H A"
  using assms
proof (induction rule: H_signature_proves.induct)
  case (PC \<Gamma> A)
  show ?case using PC.hyps(1) by (rule H_proves.PC)
next
  case (IndividualExistence \<Gamma>)
  show ?case by (rule H_proves.IndividualExistence)
next
  case (UI \<sigma> \<Gamma> A T)
  show ?case using UI.hyps(1,2) by (rule H_proves.UI)
next
  case (EG \<sigma> \<Gamma> A T)
  show ?case using EG.hyps(1,2) by (rule H_proves.EG)
next
  case (Ref \<Gamma> M \<sigma>)
  show ?case using Ref.hyps(1) by (rule H_proves.Ref)
next
  case (LL \<Gamma> A \<sigma> B F)
  show ?case using LL.hyps(1,2,3) by (rule H_proves.LL)
next
  case (Beta \<Gamma> A B)
  show ?case using Beta.hyps(1,2,3) by (rule H_proves.Beta)
next
  case (Eta \<Gamma> A B)
  show ?case using Eta.hyps(1,2,3) by (rule H_proves.Eta)
next
  case (MP \<Gamma> A B)
  show ?case using MP.IH by (rule H_proves.MP)
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case using Gen.hyps(1,2) Gen.IH by (rule H_proves.Gen)
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case using Inst.hyps(1,2) Inst.IH by (rule H_proves.Inst)
qed

lemma H_signature_proves_formula:
  assumes "H_signature_proves \<Sigma> \<Gamma> A"
  shows "\<Gamma> \<turnstile> A : Prop"
proof -
  have "\<Gamma> \<turnstile>\<^sub>H A"
    using assms by (rule H_signature_proves_imp_H_proves)
  then show ?thesis by (rule H_proves_formula)
qed

lemma H_signature_proves_in_signature:
  assumes "H_signature_proves \<Sigma> \<Gamma> A"
  shows "bbk_in_signature \<Sigma> A"
  using assms
proof (induction rule: H_signature_proves.induct)
  case (PC \<Gamma> A)
  show ?case by (rule PC.hyps(2))
next
  case (IndividualExistence \<Gamma>)
  show ?case by simp
next
  case (UI \<sigma> \<Gamma> A T)
  have "bbk_in_signature \<Sigma> (subst0 T A)"
    using UI.hyps(3,4) by (rule bbk_signature_subst0)
  then show ?case using UI.hyps(3) by simp
next
  case (EG \<sigma> \<Gamma> A T)
  have "bbk_in_signature \<Sigma> (subst0 T A)"
    using EG.hyps(3,4) by (rule bbk_signature_subst0)
  then show ?case using EG.hyps(3) by simp
next
  case (Ref \<Gamma> M \<sigma>)
  show ?case using Ref.hyps(2) by simp
next
  case (LL \<Gamma> A \<sigma> B F)
  show ?case using LL.hyps(4,5,6) by simp
next
  case (Beta \<Gamma> A B)
  show ?case using Beta.hyps(4,5) by simp
next
  case (Eta \<Gamma> A B)
  show ?case using Eta.hyps(4,5) by simp
next
  case (MP \<Gamma> A B)
  show ?case using MP.hyps by blast
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case using Gen.hyps(3,4) by simp
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case using Inst.hyps(3,4) by simp
qed

section \<open>Soundness for each represented signature\<close>

text \<open>
  Σ; Γ ⊢ₕ A ⇒ 𝔐,g ⊨ A whenever 𝔐 is a model of L(Σ). Bacon–Dorr, Figure 2; Theorem
  3.2, pp. 44–45.

  Isabelle representation: The induction uses the guarded rules from the basic and
  quantifier soundness files and returns bbk_valid_in_context.

  Status: All represented string signatures are covered; arbitrary-cardinality
  signatures belong to the parametric branch.
\<close>

context bbk_model
begin

theorem H_signature_BBK_soundness:
  assumes "H_signature_proves signature \<Gamma> A"
  shows "bbk_valid_in_context \<Gamma> A"
  using assms
proof (induction rule: H_signature_proves.induct)
  case (PC \<Gamma> A)
  show ?case using PC.hyps by (rule bbk_PC_valid)
next
  case (IndividualExistence \<Gamma>)
  show ?case by (rule bbk_IndividualExistence_valid)
next
  case (UI \<sigma> \<Gamma> A T)
  show ?case using UI.hyps by (rule bbk_UI_valid)
next
  case (EG \<sigma> \<Gamma> A T)
  show ?case using EG.hyps by (rule bbk_EG_valid)
next
  case (Ref \<Gamma> M \<sigma>)
  show ?case using Ref.hyps by (rule bbk_Ref_valid)
next
  case (LL \<Gamma> A \<sigma> B F)
  show ?case using LL.hyps by (rule bbk_LL_valid)
next
  case (Beta \<Gamma> A B)
  show ?case using Beta.hyps by (rule bbk_Beta_valid)
next
  case (Eta \<Gamma> A B)
  show ?case using Eta.hyps by (rule bbk_Eta_valid)
next
  case (MP \<Gamma> A B)
  show ?case using MP.IH by (rule bbk_MP_valid)
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case using Gen.hyps(1,2,3,4) Gen.IH by (rule bbk_Gen_valid)
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case using Inst.hyps(1,2,3,4) Inst.IH by (rule bbk_Inst_valid)
qed

corollary H_signature_BBK_satisfies:
  assumes "H_signature_proves signature \<Gamma> A"
    and "bbk_env_typed domain \<Gamma> g"
  shows "bbk_satisfies g A"
proof -
  have "bbk_valid_in_context \<Gamma> A"
    using assms(1) by (rule H_signature_BBK_soundness)
  then show ?thesis using assms(2) by (rule valid_satisfies)
qed

end

end
