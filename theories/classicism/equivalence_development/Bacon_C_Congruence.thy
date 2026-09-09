theory Bacon_C_Congruence
  imports Bacon_C_Local_Equality
begin

section \<open>Axiom-based congruence and conversion identities\<close>

text \<open>
  From ⊢C M =σ N we derive replacement in a typed term context:
  ⊢C T[M/x] =τ T[N/x].  If M and N differ by β or η conversion, we also
  obtain ⊢C M =τ N.  Sources: Bacon--Dorr Figure 2, p.8, Ref, LL, β, η;
  Appendix A, pp.65–67, where these conversions are used inside identities.

  Isabelle representation.  subst0 performs capture-avoiding replacement
  of the nearest free slot.  compatible_step selects a conversion occurrence
  inside a term; beta_eta_equiv supplies its typed equivalence closure.

  Status.  These are axiom-based C derivations.  They do not infer identity
  from an arbitrary theorem ⊢C P ↔ Q and therefore do not assume A.3.
\<close>

subsection \<open>Leibniz replacement in typed term contexts\<close>

text \<open>
  ⊢C M =σ N and ⊢C P[M/x] give ⊢C P[N/x]; consequently
  ⊢C T[M/x] =τ T[N/x].  Source: Bacon--Dorr Figure 2, p.8, LL and β.

  Isabelle representation.  T has one extra σ-typed parameter slot.
  The application lemmas specialize T to FX or XF.
  Status.  Only replacement of identical arguments is licensed.
\<close>

lemma C_closure_beta_formula:
  assumes "\<sigma> # \<Gamma> \<turnstile> P : Prop" and "\<Gamma> \<turnstile> M : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>C
    (App (Lam \<sigma> P) M \<longleftrightarrow>\<^sub>o subst0 M P)"
proof -
  have app_type: "\<Gamma> \<turnstile> App (Lam \<sigma> P) M : Prop"
    using assms by auto
  have sub_type: "\<Gamma> \<turnstile> subst0 M P : Prop"
    using assms by (rule subst0_preserves_typing)
  have step: "compatible_step beta_contract
    (App (Lam \<sigma> P) M) (subst0 M P)"
    by (intro compatible_step.root beta_contract.beta)
  show ?thesis using app_type sub_type step by (rule C_beta_step)
qed

lemma C_closure_substitution:
  assumes M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and P_type: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and eq: "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> M N"
    and PM: "\<Gamma> \<turnstile>\<^sub>C subst0 M P"
  shows "\<Gamma> \<turnstile>\<^sub>C subst0 N P"
proof -
  let ?F = "Lam \<sigma> P"
  have F_type: "\<Gamma> \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o Prop"
    using P_type by auto
  have FM_type: "\<Gamma> \<turnstile> App ?F M : Prop"
    using F_type M_type by auto
  have FN_type: "\<Gamma> \<turnstile> App ?F N : Prop"
    using F_type N_type by auto
  have PM_type: "\<Gamma> \<turnstile> subst0 M P : Prop"
    using P_type M_type by (rule subst0_preserves_typing)
  have PN_type: "\<Gamma> \<turnstile> subst0 N P : Prop"
    using P_type N_type by (rule subst0_preserves_typing)
  have beta_M: "\<Gamma> \<turnstile>\<^sub>C
    (App ?F M \<longleftrightarrow>\<^sub>o subst0 M P)"
    using P_type M_type by (rule C_closure_beta_formula)
  have beta_N: "\<Gamma> \<turnstile>\<^sub>C
    (App ?F N \<longleftrightarrow>\<^sub>o subst0 N P)"
    using P_type N_type by (rule C_closure_beta_formula)
  have PM_FM: "\<Gamma> \<turnstile>\<^sub>C Imp (subst0 M P) (App ?F M)"
    using FM_type PM_type beta_M by (rule C_closure_beta_right_imp)
  have FM: "\<Gamma> \<turnstile>\<^sub>C App ?F M"
    using PM PM_FM by (rule C_proves.MP)
  have LL: "\<Gamma> \<turnstile>\<^sub>C
    Imp (Eq \<sigma> M N) (Imp (App ?F M) (App ?F N))"
    using M_type N_type F_type by (intro C_proves.H H_proves.LL)
  have FM_FN: "\<Gamma> \<turnstile>\<^sub>C Imp (App ?F M) (App ?F N)"
    using eq LL by (rule C_proves.MP)
  have FN: "\<Gamma> \<turnstile>\<^sub>C App ?F N"
    using FM FM_FN by (rule C_proves.MP)
  have FN_PN: "\<Gamma> \<turnstile>\<^sub>C Imp (App ?F N) (subst0 N P)"
    using FN_type PN_type beta_N by (rule C_closure_beta_left_imp)
  show ?thesis using FN FN_PN by (rule C_proves.MP)
qed

lemma C_closure_congruence:
  assumes M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and T_type: "\<sigma> # \<Gamma> \<turnstile> T : \<tau>"
    and eq: "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> M N"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> (subst0 M T) (subst0 N T)"
proof -
  let ?P = "Eq \<tau> (shift (subst0 M T)) T"
  have MT_type: "\<Gamma> \<turnstile> subst0 M T : \<tau>"
    using T_type M_type by (rule subst0_preserves_typing)
  have shifted_type: "\<sigma> # \<Gamma> \<turnstile> shift (subst0 M T) : \<tau>"
    using MT_type by (rule weakening_front)
  have P_type: "\<sigma> # \<Gamma> \<turnstile> ?P : Prop"
    using shifted_type T_type by auto
  have ref: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> (subst0 M T) (subst0 M T)"
    using MT_type by (intro C_proves.H H_proves.Ref)
  have PM: "\<Gamma> \<turnstile>\<^sub>C subst0 M ?P"
    using ref by (simp add: subst0_def)
  have "\<Gamma> \<turnstile>\<^sub>C subst0 N ?P"
    by (rule C_closure_substitution[OF M_type N_type P_type eq PM])
  then show ?thesis by (simp add: subst0_def)
qed

lemma C_closure_app_congruence_left:
  assumes F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and G_type: "\<Gamma> \<turnstile> G : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and eq: "\<Gamma> \<turnstile>\<^sub>C Eq (\<sigma> \<rightarrow>\<^sub>o \<tau>) F G"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> (App F A) (App G A)"
proof -
  have shifted: "(\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile> shift A : \<sigma>"
    using A_type by (rule weakening_front)
  have body: "(\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile>
    App (Var 0) (shift A) : \<tau>"
    using shifted by auto
  have "\<Gamma> \<turnstile>\<^sub>C Eq \<tau>
    (subst0 F (App (Var 0) (shift A)))
    (subst0 G (App (Var 0) (shift A)))"
    by (rule C_closure_congruence[OF F_type G_type body eq])
  then show ?thesis by (simp add: subst0_def)
qed

lemma C_closure_app_congruence_right:
  assumes A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and B_type: "\<Gamma> \<turnstile> B : \<sigma>"
    and F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and eq: "\<Gamma> \<turnstile>\<^sub>C Eq \<sigma> A B"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> (App F A) (App F B)"
proof -
  have shifted: "\<sigma> # \<Gamma> \<turnstile> shift F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using F_type by (rule weakening_front)
  have body: "\<sigma> # \<Gamma> \<turnstile> App (shift F) (Var 0) : \<tau>"
    using shifted by auto
  have "\<Gamma> \<turnstile>\<^sub>C Eq \<tau>
    (subst0 A (App (shift F) (Var 0)))
    (subst0 B (App (shift F) (Var 0)))"
    by (rule C_closure_congruence[OF A_type B_type body eq])
  then show ?thesis by (simp add: subst0_def)
qed

subsection \<open>Conversion identities without Equivalence\<close>

text \<open>
  β and η license Φ[M] ↔ Φ[N].  Taking Φ[X] to be M =τ X and using
  ⊢C M =τ M gives ⊢C M =τ N.  Source: Bacon--Dorr Figure 2, p.8;
  this is the contextual-conversion reasoning used in Appendix A.2,
  pp.65–66, especially the β and η cases.

  Isabelle representation.  C_closure_beta_identity and
  C_closure_eta_identity concern one compatible step.  The following
  induction extends this to beta_eta_equiv at every displayed result type.

  Status.  No arbitrary biconditional-to-identity rule is used.
\<close>

lemma C_closure_beta_identity:
  assumes M_type: "\<Gamma> \<turnstile> M : \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<tau>"
    and step: "compatible_step beta_contract M N"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> M N"
proof -
  have MM_type: "\<Gamma> \<turnstile> Eq \<tau> M M : Prop"
    using M_type by auto
  have MN_type: "\<Gamma> \<turnstile> Eq \<tau> M N : Prop"
    using M_type N_type by auto
  have eq_step: "compatible_step beta_contract (Eq \<tau> M M) (Eq \<tau> M N)"
    using step by (rule compatible_step.Eq_right)
  have bicond: "\<Gamma> \<turnstile>\<^sub>C
    (Eq \<tau> M M \<longleftrightarrow>\<^sub>o Eq \<tau> M N)"
    using MM_type MN_type eq_step by (rule C_beta_step)
  have imp: "\<Gamma> \<turnstile>\<^sub>C Imp (Eq \<tau> M M) (Eq \<tau> M N)"
    using MM_type MN_type bicond by (rule C_closure_beta_left_imp)
  have ref: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> M M"
    using M_type by (intro C_proves.H H_proves.Ref)
  show ?thesis using ref imp by (rule C_proves.MP)
qed

lemma C_closure_eta_identity:
  assumes M_type: "\<Gamma> \<turnstile> M : \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<tau>"
    and step: "compatible_step eta_contract M N"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> M N"
proof -
  have MM_type: "\<Gamma> \<turnstile> Eq \<tau> M M : Prop"
    using M_type by auto
  have MN_type: "\<Gamma> \<turnstile> Eq \<tau> M N : Prop"
    using M_type N_type by auto
  have eq_step: "compatible_step eta_contract (Eq \<tau> M M) (Eq \<tau> M N)"
    using step by (rule compatible_step.Eq_right)
  have bicond: "\<Gamma> \<turnstile>\<^sub>C
    (Eq \<tau> M M \<longleftrightarrow>\<^sub>o Eq \<tau> M N)"
    using MM_type MN_type eq_step by (rule C_eta_step)
  have imp: "\<Gamma> \<turnstile>\<^sub>C Imp (Eq \<tau> M M) (Eq \<tau> M N)"
    using MM_type MN_type bicond by (rule C_closure_beta_left_imp)
  have ref: "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> M M"
    using M_type by (intro C_proves.H H_proves.Ref)
  show ?thesis using ref imp by (rule C_proves.MP)
qed

lemma C_closure_beta_eta_identity:
  assumes "beta_eta_equiv \<Gamma> \<tau> M N"
  shows "\<Gamma> \<turnstile>\<^sub>C Eq \<tau> M N"
  using assms
proof (induction rule: beta_eta_equiv.induct)
  case (Refl \<Gamma> M \<tau>)
  then show ?case by (intro C_proves.H H_proves.Ref)
next
  case (Beta \<Gamma> M \<tau> N)
  then show ?case by (rule C_closure_beta_identity)
next
  case (Eta \<Gamma> M \<tau> N)
  then show ?case by (rule C_closure_eta_identity)
next
  case (Sym \<Gamma> \<tau> M N)
  have M_type: "\<Gamma> \<turnstile> M : \<tau>"
    using Sym.hyps by (rule beta_eta_equiv_left_type)
  have N_type: "\<Gamma> \<turnstile> N : \<tau>"
    using Sym.hyps by (rule beta_eta_equiv_right_type)
  show ?case by (rule C_closure_eq_sym_from[OF M_type N_type Sym.IH])
next
  case (Trans \<Gamma> \<tau> M N P)
  have M_type: "\<Gamma> \<turnstile> M : \<tau>"
    using Trans.hyps(1) by (rule beta_eta_equiv_left_type)
  have N_type: "\<Gamma> \<turnstile> N : \<tau>"
    using Trans.hyps(1) by (rule beta_eta_equiv_right_type)
  have P_type: "\<Gamma> \<turnstile> P : \<tau>"
    using Trans.hyps(2) by (rule beta_eta_equiv_right_type)
  show ?case
    by (rule C_closure_eq_trans_from[OF M_type N_type P_type Trans.IH(1) Trans.IH(2)])
qed

end
