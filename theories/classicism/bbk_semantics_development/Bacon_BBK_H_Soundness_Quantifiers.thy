theory Bacon_BBK_H_Soundness_Quantifiers
  imports Bacon_BBK_One_Binder
begin

section \<open>Quantifier axioms and rules\<close>

text \<open>
  ∀x A ⇒ A[T/x]; A[T/x] ⇒ ∃x A. Gen and Inst require x ∉ FV(P) and x ∉ FV(Q),
  respectively. Bacon–Dorr, Figure 2; Theorem 3.2, pp. 44–45.

  Isabelle representation: One-binder substitution proves UI and EG. De Bruijn shift
  expresses the side condition in Gen and Inst, and denote_rename supplies assignment
  coherence.

  Status: All four rule lemmas are proved for in-signature typed inputs; no
  vector-environment assumption is used.
\<close>

context bbk_model
begin

lemma bbk_UI_valid:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and arg: "\<Gamma> \<turnstile> T : \<sigma>"
    and sigA: "bbk_in_signature signature A"
    and sigT: "bbk_in_signature signature T"
  shows "bbk_valid_in_context \<Gamma> (Imp (Forall \<sigma> A) (subst0 T A))"
proof -
  have all_type: "\<Gamma> \<turnstile> Forall \<sigma> A : Prop"
    using body by (rule has_type.Forall)
  have inst_type: "\<Gamma> \<turnstile> subst0 T A : Prop"
    using body arg by (rule subst0_preserves_typing)
  have typed: "\<Gamma> \<turnstile> Imp (Forall \<sigma> A) (subst0 T A) : Prop"
    using all_type inst_type by (rule has_type.Imp)
  have sig_all: "bbk_in_signature signature (Forall \<sigma> A)" using sigA by simp
  have sig_inst: "bbk_in_signature signature (subst0 T A)"
    using sigA sigT by (rule bbk_signature_subst0)
  have sig: "bbk_in_signature signature (Imp (Forall \<sigma> A) (subst0 T A))"
    using sig_all sig_inst by simp
  have truth: "valuation (denote g (Imp (Forall \<sigma> A) (subst0 T A)))"
    if env: "bbk_env_typed domain \<Gamma> g" for g
  proof -
    have denT: "denote g T \<in> domain \<sigma>"
      using arg sigT env by (rule denote_type)
    have substitution: "denote (bbk_extend (denote g T) g) A = denote g (subst0 T A)"
      using body arg sigA sigT env by (rule bbk_one_binder)
    have implication: "valuation (denote g (Forall \<sigma> A)) \<longrightarrow>
        valuation (denote g (subst0 T A))"
    proof
      assume all_true: "valuation (denote g (Forall \<sigma> A))"
      have all_instances: "\<forall>a \<in> domain \<sigma>.
          valuation (denote (bbk_extend a g) A)"
        using all_true by (simp only: valuation_forall[OF body sigA env])
      have instance_true: "valuation (denote (bbk_extend (denote g T) g) A)"
        by (rule bspec[OF all_instances denT])
      show "valuation (denote g (subst0 T A))"
        using instance_true by (simp only: substitution)
    qed
    show ?thesis
      using valuation_imp[OF all_type inst_type sig_all sig_inst env] implication by blast
  qed
  show ?thesis using typed sig truth by (rule bbk_validI)
qed

lemma bbk_EG_valid:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : Prop" and arg: "\<Gamma> \<turnstile> T : \<sigma>"
    and sigA: "bbk_in_signature signature A"
    and sigT: "bbk_in_signature signature T"
  shows "bbk_valid_in_context \<Gamma> (Imp (subst0 T A) (Exists \<sigma> A))"
proof -
  have ex_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using body by (rule has_type.Exists)
  have inst_type: "\<Gamma> \<turnstile> subst0 T A : Prop"
    using body arg by (rule subst0_preserves_typing)
  have typed: "\<Gamma> \<turnstile> Imp (subst0 T A) (Exists \<sigma> A) : Prop"
    using inst_type ex_type by (rule has_type.Imp)
  have sig_ex: "bbk_in_signature signature (Exists \<sigma> A)" using sigA by simp
  have sig_inst: "bbk_in_signature signature (subst0 T A)"
    using sigA sigT by (rule bbk_signature_subst0)
  have sig: "bbk_in_signature signature (Imp (subst0 T A) (Exists \<sigma> A))"
    using sig_inst sig_ex by simp
  have truth: "valuation (denote g (Imp (subst0 T A) (Exists \<sigma> A)))"
    if env: "bbk_env_typed domain \<Gamma> g" for g
  proof -
    have denT: "denote g T \<in> domain \<sigma>"
      using arg sigT env by (rule denote_type)
    have substitution: "denote (bbk_extend (denote g T) g) A = denote g (subst0 T A)"
      using body arg sigA sigT env by (rule bbk_one_binder)
    have implication: "valuation (denote g (subst0 T A)) \<longrightarrow>
        valuation (denote g (Exists \<sigma> A))"
    proof
      assume instance_true: "valuation (denote g (subst0 T A))"
      have witness_true: "valuation (denote (bbk_extend (denote g T) g) A)"
        using instance_true by (simp only: substitution)
      have witness: "\<exists>a \<in> domain \<sigma>.
          valuation (denote (bbk_extend a g) A)"
      proof (rule bexI[where x="denote g T"])
        show "valuation (denote (bbk_extend (denote g T) g) A)"
          by (rule witness_true)
        show "denote g T \<in> domain \<sigma>"
          by (rule denT)
      qed
      show "valuation (denote g (Exists \<sigma> A))"
        using witness by (simp only: valuation_exists[OF body sigA env])
    qed
    show ?thesis
      using valuation_imp[OF inst_type ex_type sig_inst sig_ex env] implication by blast
  qed
  show ?thesis using typed sig truth by (rule bbk_validI)
qed

lemma bbk_Gen_valid:
  assumes P: "\<Gamma> \<turnstile> P : Prop" and Q: "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and sigP: "bbk_in_signature signature P"
    and sigQ: "bbk_in_signature signature Q"
    and premise: "bbk_valid_in_context (\<sigma> # \<Gamma>) (Imp (shift P) Q)"
  shows "bbk_valid_in_context \<Gamma> (Imp P (Forall \<sigma> Q))"
proof -
  have SP: "\<sigma> # \<Gamma> \<turnstile> shift P : Prop"
    using P by (rule weakening_front)
  have allQ: "\<Gamma> \<turnstile> Forall \<sigma> Q : Prop"
    using Q by (rule has_type.Forall)
  have typed: "\<Gamma> \<turnstile> Imp P (Forall \<sigma> Q) : Prop"
    using P allQ by (rule has_type.Imp)
  have sigSP: "bbk_in_signature signature (shift P)"
    using sigP by (simp add: shift_def bbk_signature_rename)
  have sig_allQ: "bbk_in_signature signature (Forall \<sigma> Q)"
    using sigQ by simp
  have sig: "bbk_in_signature signature (Imp P (Forall \<sigma> Q))"
    using sigP sig_allQ by simp
  have truth: "valuation (denote g (Imp P (Forall \<sigma> Q)))"
    if env: "bbk_env_typed domain \<Gamma> g" for g
  proof -
    have implication: "valuation (denote g P) \<longrightarrow>
        valuation (denote g (Forall \<sigma> Q))"
    proof
      assume p: "valuation (denote g P)"
      have q: "valuation (denote (bbk_extend a g) Q)" if a: "a \<in> domain \<sigma>" for a
      proof -
        have extended: "bbk_env_typed domain (\<sigma> # \<Gamma>) (bbk_extend a g)"
          using env a by (rule bbk_env_extend)
        have prem: "valuation (denote (bbk_extend a g) (Imp (shift P) Q))"
          using valid_satisfies[OF premise extended] unfolding bbk_satisfies_def .
        have shifted: "denote (bbk_extend a g) (shift P) = denote g P"
          using P sigP env a by (rule bbk_shift_assignment)
        have shifted_true: "valuation (denote (bbk_extend a g) (shift P))"
          using p by (simp only: shifted)
        have implication: "valuation (denote (bbk_extend a g) (shift P)) \<longrightarrow>
            valuation (denote (bbk_extend a g) Q)"
          using prem by (simp only: valuation_imp[OF SP Q sigSP sigQ extended])
        show ?thesis by (rule mp[OF implication shifted_true])
      qed
      show "valuation (denote g (Forall \<sigma> Q))"
        using q valuation_forall[OF Q sigQ env] by blast
    qed
    show ?thesis
      using implication valuation_imp[OF P allQ sigP sig_allQ env] by blast
  qed
  show ?thesis using typed sig truth by (rule bbk_validI)
qed

lemma bbk_Inst_valid:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> P : Prop" and Q: "\<Gamma> \<turnstile> Q : Prop"
    and sigP: "bbk_in_signature signature P"
    and sigQ: "bbk_in_signature signature Q"
    and premise: "bbk_valid_in_context (\<sigma> # \<Gamma>) (Imp P (shift Q))"
  shows "bbk_valid_in_context \<Gamma> (Imp (Exists \<sigma> P) Q)"
proof -
  have SQ: "\<sigma> # \<Gamma> \<turnstile> shift Q : Prop"
    using Q by (rule weakening_front)
  have exP: "\<Gamma> \<turnstile> Exists \<sigma> P : Prop"
    using P by (rule has_type.Exists)
  have typed: "\<Gamma> \<turnstile> Imp (Exists \<sigma> P) Q : Prop"
    using exP Q by (rule has_type.Imp)
  have sigSQ: "bbk_in_signature signature (shift Q)"
    using sigQ by (simp add: shift_def bbk_signature_rename)
  have sig_exP: "bbk_in_signature signature (Exists \<sigma> P)"
    using sigP by simp
  have sig: "bbk_in_signature signature (Imp (Exists \<sigma> P) Q)"
    using sig_exP sigQ by simp
  have truth: "valuation (denote g (Imp (Exists \<sigma> P) Q))"
    if env: "bbk_env_typed domain \<Gamma> g" for g
  proof -
    have implication: "valuation (denote g (Exists \<sigma> P)) \<longrightarrow>
        valuation (denote g Q)"
    proof
      assume ex: "valuation (denote g (Exists \<sigma> P))"
      obtain a where a: "a \<in> domain \<sigma>"
        and p: "valuation (denote (bbk_extend a g) P)"
        using ex valuation_exists[OF P sigP env] by blast
      have extended: "bbk_env_typed domain (\<sigma> # \<Gamma>) (bbk_extend a g)"
        using env a by (rule bbk_env_extend)
      have prem: "valuation (denote (bbk_extend a g) (Imp P (shift Q)))"
        using valid_satisfies[OF premise extended] unfolding bbk_satisfies_def .
      have shifted: "denote (bbk_extend a g) (shift Q) = denote g Q"
        using Q sigQ env a by (rule bbk_shift_assignment)
      have implication: "valuation (denote (bbk_extend a g) P) \<longrightarrow>
          valuation (denote (bbk_extend a g) (shift Q))"
        using prem by (simp only: valuation_imp[OF P SQ sigP sigSQ extended])
      have shifted_true: "valuation (denote (bbk_extend a g) (shift Q))"
        by (rule mp[OF implication p])
      show "valuation (denote g Q)"
        using shifted_true by (simp only: shifted)
    qed
    show ?thesis
      using implication valuation_imp[OF exP Q sig_exP sigQ env] by blast
  qed
  show ?thesis using typed sig truth by (rule bbk_validI)
qed

section \<open>Full H soundness for the universal represented signature\<close>

text \<open>
  Γ ⊢ₕ A ⇒ 𝔐,g ⊨ A for the universal typed-string signature. Bacon–Dorr, Figure 2;
  Theorem 3.2, pp. 44–45.

  Isabelle representation: The induction follows every H_proves constructor. That
  relation has no signature parameter, so an intermediate MP formula cannot be guarded
  merely from its conclusion.

  Status: Complete H_proves soundness at the universal signature; H_Signature_Proof
  supplies the separate signature-local result.
\<close>

theorem H_BBK_soundness_universal_signature:
  assumes full: "\<And>\<sigma>. signature \<sigma> = UNIV"
    and derivation: "\<Gamma> \<turnstile>\<^sub>H A"
  shows "bbk_valid_in_context \<Gamma> A"
proof -
  have signature_eq: "signature = (\<lambda>_. UNIV)"
    by (rule ext) (rule full)
  have sig: "bbk_in_signature signature M" for M
    by (simp add: signature_eq)
  show ?thesis
    using derivation
  proof (induction rule: H_proves.induct)
    case (PC \<Gamma> A)
    show ?case using PC.hyps sig by (rule bbk_PC_valid)
  next
    case (IndividualExistence \<Gamma>)
    show ?case by (rule bbk_IndividualExistence_valid)
  next
    case (UI \<sigma> \<Gamma> A T)
    show ?case using UI.hyps sig[of A] sig[of T] by (rule bbk_UI_valid)
  next
    case (EG \<sigma> \<Gamma> A T)
    show ?case using EG.hyps sig[of A] sig[of T] by (rule bbk_EG_valid)
  next
    case (Ref \<Gamma> M \<sigma>)
    show ?case using Ref.hyps sig by (rule bbk_Ref_valid)
  next
    case (LL \<Gamma> A \<sigma> B F)
    show ?case using LL.hyps sig[of A] sig[of B] sig[of F] by (rule bbk_LL_valid)
  next
    case (Beta \<Gamma> A B)
    show ?case using Beta.hyps sig[of A] sig[of B] by (rule bbk_Beta_valid)
  next
    case (Eta \<Gamma> A B)
    show ?case using Eta.hyps sig[of A] sig[of B] by (rule bbk_Eta_valid)
  next
    case (MP \<Gamma> A B)
    show ?case using MP.IH by (rule bbk_MP_valid)
  next
    case (Gen \<Gamma> P \<sigma> Q)
    show ?case using Gen.hyps(1,2) sig[of P] sig[of Q] Gen.IH by (rule bbk_Gen_valid)
  next
    case (Inst \<sigma> \<Gamma> P Q)
    show ?case using Inst.hyps(1,2) sig[of P] sig[of Q] Inst.IH by (rule bbk_Inst_valid)
  qed
qed

end

end
