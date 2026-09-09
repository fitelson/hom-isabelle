theory Bacon_BBK_One_Binder
  imports Bacon_BBK_H_Soundness_Basic
begin

section \<open>One binder: beta reduction and the context-insertion boundary\<close>

text \<open>
  ⟦A⟧g[x↦⟦T⟧g] = ⟦A[T/x]⟧g. Bacon–Dorr, Definition 3.1, pp. 43–44.

  Isabelle representation: bbk_extend inserts de Bruijn slot zero. The proof compares
  applications of the shifted λ-abstraction, uses β conversion, and discharges context
  insertion with denote_rename.

  Status: The final theorem covers open bodies and every object type; it assumes
  neither Functionality nor the vector-environment target.
\<close>

lemma bbk_lift_signature:
  assumes "\<And>n. bbk_in_signature \<Sigma> (s n)"
  shows "bbk_in_signature \<Sigma> (lift_subst s n)"
  using assms by (cases n) (simp_all add: bbk_signature_rename)

lemma bbk_signature_subst:
  assumes "bbk_in_signature \<Sigma> M"
    and "\<And>n. bbk_in_signature \<Sigma> (s n)"
  shows "bbk_in_signature \<Sigma> (subst s M)"
  using assms
proof (induction M arbitrary: s)
  case (Lam \<sigma> M)
  have "bbk_in_signature \<Sigma> (subst (lift_subst s) M)"
    using Lam.prems by (intro Lam.IH bbk_lift_signature) simp_all
  then show ?case by simp
next
  case (Forall \<sigma> M)
  have "bbk_in_signature \<Sigma> (subst (lift_subst s) M)"
    using Forall.prems by (intro Forall.IH bbk_lift_signature) simp_all
  then show ?case by simp
next
  case (Exists \<sigma> M)
  have "bbk_in_signature \<Sigma> (subst (lift_subst s) M)"
    using Exists.prems by (intro Exists.IH bbk_lift_signature) simp_all
  then show ?case by simp
qed simp_all

lemma bbk_signature_subst0:
  assumes "bbk_in_signature \<Sigma> A" and "bbk_in_signature \<Sigma> T"
  shows "bbk_in_signature \<Sigma> (subst0 T A)"
  unfolding subst0_def
  by (rule bbk_signature_subst[OF assms(1)]) (case_tac n; simp add: assms(2))

lemma bbk_subst_rename_inverse:
  assumes "\<And>n. s (r n) = Var n"
  shows "subst s (rename r M) = M"
  using assms
proof (induction M arbitrary: s r)
  case (Lam \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren r) M) = M"
    by (rule Lam.IH) (case_tac n; simp add: Lam.prems)
  then show ?case by simp
next
  case (Forall \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren r) M) = M"
    by (rule Forall.IH) (case_tac n; simp add: Forall.prems)
  then show ?case by simp
next
  case (Exists \<sigma> M)
  have "subst (lift_subst s) (rename (lift_ren r) M) = M"
    by (rule Exists.IH) (case_tac n; simp add: Exists.prems)
  then show ?case by simp
qed (simp_all add: assms)

lemma bbk_beta_slot_restore:
  "subst0 (Var 0) (rename (lift_ren Suc) A) = A"
  unfolding subst0_def
  by (rule bbk_subst_rename_inverse) (case_tac n; simp)

lemma bbk_rename_fixes:
  assumes "\<And>n. n \<in> bbk_fv M \<Longrightarrow> r n = n"
  shows "rename r M = M"
  using assms
proof (induction M arbitrary: r)
  case (Lam \<sigma> M)
  have "rename (lift_ren r) M = M"
    by (rule Lam.IH) (case_tac n; simp add: Lam.prems)
  then show ?case by simp
next
  case (Forall \<sigma> M)
  have "rename (lift_ren r) M = M"
    by (rule Forall.IH) (case_tac n; simp add: Forall.prems)
  then show ?case by simp
next
  case (Exists \<sigma> M)
  have "rename (lift_ren r) M = M"
    by (rule Exists.IH) (case_tac n; simp add: Exists.prems)
  then show ?case by simp
qed simp_all

lemma bbk_shift_closed:
  assumes "bbk_fv M = {}"
  shows "shift M = M"
  unfolding shift_def by (rule bbk_rename_fixes) (simp add: assms)

context bbk_model
begin

lemma bbk_closed_shift_assignment:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and sig: "bbk_in_signature signature M"
    and closed: "bbk_fv M = {}"
    and env: "bbk_env_typed domain \<Gamma> g"
    and a: "a \<in> domain \<sigma>"
  shows "denote (bbk_extend a g) (shift M) = denote g M"
proof -
  have shift_eq: "shift M = M" using closed by (rule bbk_shift_closed)
  have shifted_type: "\<sigma> # \<Gamma> \<turnstile> shift M : \<tau>"
    using typed by (rule weakening_front)
  have extended_type: "\<sigma> # \<Gamma> \<turnstile> M : \<tau>"
    using shifted_type shift_eq by simp
  have extended: "bbk_env_typed domain (\<sigma> # \<Gamma>) (bbk_extend a g)"
    using env a by (rule bbk_env_extend)
  have "denote (bbk_extend a g) M = denote g M"
    using extended_type typed sig extended env closed
    by (rule closed_denotation_independent)
  then show ?thesis using shift_eq by simp
qed

lemma bbk_one_binder_from_lambda_shift:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : \<tau>" and arg: "\<Gamma> \<turnstile> T : \<sigma>"
    and sigA: "bbk_in_signature signature A"
    and sigT: "bbk_in_signature signature T"
    and env: "bbk_env_typed domain \<Gamma> g"
    and lambda_shift:
      "denote (bbk_extend (denote g T) g) (shift (Lam \<sigma> A)) =
       denote g (Lam \<sigma> A)"
  shows "denote (bbk_extend (denote g T) g) A = denote g (subst0 T A)"
proof -
  let ?h = "bbk_extend (denote g T) g"
  let ?L = "Lam \<sigma> A"
  have L: "\<Gamma> \<turnstile> ?L : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using body by (rule has_type.Lam)
  have sigL: "bbk_in_signature signature ?L" using sigA by simp
  have Tden: "denote g T \<in> domain \<sigma>"
    using arg sigT env by (rule denote_type)
  have extended: "bbk_env_typed domain (\<sigma> # \<Gamma>) ?h"
    using env Tden by (rule bbk_env_extend)
  have SL: "\<sigma> # \<Gamma> \<turnstile> shift ?L : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using L by (rule weakening_front)
  have zero: "\<sigma> # \<Gamma> \<turnstile> Var 0 : \<sigma>" by simp
  have redex: "\<sigma> # \<Gamma> \<turnstile> App (shift ?L) (Var 0) : \<tau>"
    using SL zero by (rule has_type.App)
  have step: "compatible_step beta_contract (App (shift ?L) (Var 0)) A"
  proof -
    have "compatible_step beta_contract
      (App (Lam \<sigma> (rename (lift_ren Suc) A)) (Var 0))
      (subst0 (Var 0) (rename (lift_ren Suc) A))"
      by (intro compatible_step.root beta_contract.beta)
    then show ?thesis by (simp add: shift_def bbk_beta_slot_restore)
  qed
  have conv: "beta_eta_equiv (\<sigma> # \<Gamma>) \<tau> (App (shift ?L) (Var 0)) A"
    using redex body step by (rule beta_eta_equiv.Beta)
  have sigleft: "bbk_in_signature signature (App (shift ?L) (Var 0))"
    using sigL by (simp add: shift_def bbk_signature_rename)
  have sigright: "bbk_in_signature signature (App ?L T)"
    using sigL sigT by simp
  have beta_left: "denote ?h (App (shift ?L) (Var 0)) = denote ?h A"
    using conv sigleft sigA extended by (rule denote_beta_eta)
  have same_arg: "denote ?h (Var 0) = denote g T"
  proof -
    have "denote ?h (Var 0) = ?h 0"
      by (rule denote_var[OF lookup_Cons_0 extended])
    then show ?thesis by simp
  qed
  have same_app: "denote ?h (App (shift ?L) (Var 0)) = denote g (App ?L T)"
    using SL zero L arg sigleft sigright extended env lambda_shift same_arg
    by (rule denote_application_cong)
  have sigcontract: "bbk_in_signature signature (subst0 T A)"
    using sigA sigT by (rule bbk_signature_subst0)
  have beta_right: "denote g (App ?L T) = denote g (subst0 T A)"
    using body arg sigright sigcontract env by (rule bbk_denote_beta)
  show ?thesis using beta_left same_app beta_right by simp
qed

lemma bbk_one_binder_closed_abstraction:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : \<tau>" and arg: "\<Gamma> \<turnstile> T : \<sigma>"
    and sigA: "bbk_in_signature signature A"
    and sigT: "bbk_in_signature signature T"
    and env: "bbk_env_typed domain \<Gamma> g"
    and closed: "bbk_fv (Lam \<sigma> A) = {}"
  shows "denote (bbk_extend (denote g T) g) A = denote g (subst0 T A)"
proof -
  have L: "\<Gamma> \<turnstile> Lam \<sigma> A : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using body by (rule has_type.Lam)
  have sigL: "bbk_in_signature signature (Lam \<sigma> A)" using sigA by simp
  have Tden: "denote g T \<in> domain \<sigma>"
    using arg sigT env by (rule denote_type)
  have shifted: "denote (bbk_extend (denote g T) g) (shift (Lam \<sigma> A)) =
      denote g (Lam \<sigma> A)"
    using L sigL closed env Tden by (rule bbk_closed_shift_assignment)
  show ?thesis
    using body arg sigA sigT env shifted by (rule bbk_one_binder_from_lambda_shift)
qed

lemma bbk_shift_assignment:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and sig: "bbk_in_signature signature M"
    and env: "bbk_env_typed domain \<Gamma> g"
    and a: "a \<in> domain \<sigma>"
  shows "denote (bbk_extend a g) (shift M) = denote g M"
proof -
  have extended: "bbk_env_typed domain (\<sigma> # \<Gamma>) (bbk_extend a g)"
    using env a by (rule bbk_env_extend)
  have injection: "inj Suc" by simp
  have ren: "lookup (\<sigma> # \<Gamma>) (Suc n) = Some \<rho>"
    if "lookup \<Gamma> n = Some \<rho>" for n \<rho>
    using that by simp
  have "denote (bbk_extend a g) (rename Suc M) =
      denote (\<lambda>n. bbk_extend a g (Suc n)) M"
    using typed sig injection extended ren by (rule denote_rename)
  then show ?thesis by (simp add: shift_def)
qed

lemma bbk_one_binder:
  assumes body: "\<sigma> # \<Gamma> \<turnstile> A : \<tau>" and arg: "\<Gamma> \<turnstile> T : \<sigma>"
    and sigA: "bbk_in_signature signature A"
    and sigT: "bbk_in_signature signature T"
    and env: "bbk_env_typed domain \<Gamma> g"
  shows "denote (bbk_extend (denote g T) g) A = denote g (subst0 T A)"
proof -
  have L: "\<Gamma> \<turnstile> Lam \<sigma> A : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using body by (rule has_type.Lam)
  have sigL: "bbk_in_signature signature (Lam \<sigma> A)" using sigA by simp
  have Tden: "denote g T \<in> domain \<sigma>"
    using arg sigT env by (rule denote_type)
  have shifted: "denote (bbk_extend (denote g T) g) (shift (Lam \<sigma> A)) =
      denote g (Lam \<sigma> A)"
    using L sigL env Tden by (rule bbk_shift_assignment)
  show ?thesis
    using body arg sigA sigT env shifted by (rule bbk_one_binder_from_lambda_shift)
qed

text \<open>
  The one-binder theorem now covers open as well as closed bodies.  Its
  dependence on denote_rename is representation coherence, explicitly
  recorded in the model interface, not an invocation of the unproved
  vector-environment property.  UI and EG may use this theorem; the
  model-existence and source-translation obligations remain separate.
\<close>

end

end
