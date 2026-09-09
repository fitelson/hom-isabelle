theory Bacon_Semantics
  imports Bacon_S4
begin

section \<open>Abstract applicative semantics\<close>

text \<open>
  This theory begins the semantic layer without committing to a concrete
  set-theoretic construction of higher-order domains.  A model supplies one
  semantic universe, type-indexed domains inside it, application and abstraction
  operations, denotations for constants, truth values, and a type-indexed
  interpretation of object-language identity.

  Standardly, \<open>D \<sigma>\<close> is \<open>D\<^sub>\<sigma>\<close>, \<open>eval \<rho> M\<close> is
  \<open>\<lbrakk>M\<rbrakk>\<^sub>\<rho>\<close>, and \<open>valid_in_context \<Gamma> A\<close> means that every
  type-correct assignment for \<open>\<Gamma>\<close> makes \<open>A\<close> true.

  This is a sufficient interface for the soundness proofs below, not Bacon and
  Dorr's BBK or action-model semantics.  Compound formulas are collapsed to
  designated \<open>truth_den\<close> values, abstraction is available for every HOL
  function respecting the domains, and stronger locales add pointwise
  extensionality.  The source semantics permits hyperintensional proposition
  denotations and validates Equivalence through categories or actions.  Every
  theorem below must therefore be read relative to its displayed locale
  assumptions.
\<close>

type_synonym 'v env = "nat \<Rightarrow> 'v"

fun extend_env :: "'v \<Rightarrow> 'v env \<Rightarrow> 'v env" where
  "extend_env x \<rho> 0 = x"
| "extend_env x \<rho> (Suc n) = \<rho> n"

fun extend_envs :: "'v list \<Rightarrow> 'v env \<Rightarrow> 'v env" where
  "extend_envs [] \<rho> = \<rho>"
| "extend_envs (x # xs) \<rho> = extend_env x (extend_envs xs \<rho>)"

lemma extend_envs_nth_less:
  assumes "i < length xs"
  shows "extend_envs xs \<rho> i = xs ! i"
  using assms
proof (induction xs arbitrary: i)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then show ?case
    by (cases i) simp_all
qed

lemma extend_envs_after:
  "extend_envs xs \<rho> (length xs + n) = \<rho> n"
  by (induction xs) simp_all

fun app_den_vec :: "('v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> 'v list \<Rightarrow> 'v" where
  "app_den_vec ap f [] = f"
| "app_den_vec ap f (x # xs) = app_den_vec ap (ap f x) xs"

locale applicative_structure =
  fixes D :: "otype \<Rightarrow> 'v set"
    and const_den :: "string \<Rightarrow> otype \<Rightarrow> 'v"
    and app_den :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"
    and lam_den :: "otype \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> 'v"
    and truth_den :: "bool \<Rightarrow> 'v"
    and holds :: "'v \<Rightarrow> bool"
    and eq_den :: "otype \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool"
  assumes const_den_type: "const_den c \<sigma> \<in> D \<sigma>"
    and app_den_type: "f \<in> D (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<Longrightarrow> x \<in> D \<sigma> \<Longrightarrow>
      app_den f x \<in> D \<tau>"
    and lam_den_type: "(\<And>x. x \<in> D \<sigma> \<Longrightarrow> F x \<in> D \<tau>) \<Longrightarrow>
      lam_den \<sigma> F \<in> D (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and truth_den_type: "truth_den b \<in> D Prop"
    and truth_den_holds[simp]: "holds (truth_den b) = b"
    and lam_den_cong: "(\<And>x. x \<in> D \<sigma> \<Longrightarrow> F x = G x) \<Longrightarrow>
      lam_den \<sigma> F = lam_den \<sigma> G"
    and beta_den: "x \<in> D \<sigma> \<Longrightarrow> app_den (lam_den \<sigma> F) x = F x"
    and eta_den: "f \<in> D (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<Longrightarrow>
      lam_den \<sigma> (\<lambda>x. app_den f x) = f"
    and eq_den_refl: "x \<in> D \<sigma> \<Longrightarrow> eq_den \<sigma> x x"
    and eq_den_subst: "eq_den \<sigma> x y \<Longrightarrow> f \<in> D (\<sigma> \<rightarrow>\<^sub>o Prop) \<Longrightarrow>
      x \<in> D \<sigma> \<Longrightarrow> y \<in> D \<sigma> \<Longrightarrow> holds (app_den f x) \<Longrightarrow>
      holds (app_den f y)"
begin

definition env_typed :: "ctx \<Rightarrow> 'v env \<Rightarrow> bool" where
  "env_typed \<Gamma> \<rho> \<longleftrightarrow> (\<forall>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<longrightarrow> \<rho> n \<in> D \<sigma>)"

lemma env_typed_lookup:
  assumes "env_typed \<Gamma> \<rho>"
    and "lookup \<Gamma> n = Some \<sigma>"
  shows "\<rho> n \<in> D \<sigma>"
  using assms unfolding env_typed_def by blast

lemma env_typed_extend:
  assumes "env_typed \<Gamma> \<rho>"
    and "x \<in> D \<sigma>"
  shows "env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
proof (unfold env_typed_def, intro allI impI)
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "extend_env x \<rho> n \<in> D \<tau>"
  proof (cases n)
    case 0
    then have "\<tau> = \<sigma>"
      using lookup by simp
    then show ?thesis
      using 0 assms(2) by simp
  next
    case (Suc m)
    then have "lookup \<Gamma> m = Some \<tau>"
      using lookup by simp
    then have "\<rho> m \<in> D \<tau>"
      using assms(1) unfolding env_typed_def by blast
    then show ?thesis
      using Suc by simp
  qed
qed

lemma env_typed_extends:
  assumes "env_typed \<Gamma> \<rho>"
    and "list_all2 (\<lambda>x \<sigma>. x \<in> D \<sigma>) xs \<sigma>s"
  shows "env_typed (\<sigma>s @ \<Gamma>) (extend_envs xs \<rho>)"
  using assms
proof (induction xs arbitrary: \<sigma>s \<Gamma> \<rho>)
  case Nil
  then show ?case
    by (cases \<sigma>s) auto
next
  case (Cons x xs)
  then obtain \<sigma> \<sigma>s' where \<sigma>s_def: "\<sigma>s = \<sigma> # \<sigma>s'"
    and x_type: "x \<in> D \<sigma>"
    and xs_type: "list_all2 (\<lambda>x \<sigma>. x \<in> D \<sigma>) xs \<sigma>s'"
    by (cases \<sigma>s) auto
  have env_tail: "env_typed (\<sigma>s' @ \<Gamma>) (extend_envs xs \<rho>)"
    using Cons.IH[OF Cons.prems(1) xs_type] .
  have "env_typed (\<sigma> # \<sigma>s' @ \<Gamma>) (extend_env x (extend_envs xs \<rho>))"
    using env_tail x_type by (rule env_typed_extend)
  then show ?case
    by (simp add: \<sigma>s_def)
qed

fun eval :: "'v env \<Rightarrow> oterm \<Rightarrow> 'v" where
  "eval \<rho> (Var n) = \<rho> n"
| "eval \<rho> (Const c \<sigma>) = const_den c \<sigma>"
| "eval \<rho> (App M N) = app_den (eval \<rho> M) (eval \<rho> N)"
| "eval \<rho> (Lam \<sigma> M) = lam_den \<sigma> (\<lambda>x. eval (extend_env x \<rho>) M)"
| "eval \<rho> (Eq \<sigma> M N) = truth_den (eq_den \<sigma> (eval \<rho> M) (eval \<rho> N))"
| "eval \<rho> (Neg A) = truth_den (\<not> holds (eval \<rho> A))"
| "eval \<rho> (Conj A B) = truth_den (holds (eval \<rho> A) \<and> holds (eval \<rho> B))"
| "eval \<rho> (Disj A B) = truth_den (holds (eval \<rho> A) \<or> holds (eval \<rho> B))"
| "eval \<rho> (Imp A B) = truth_den (holds (eval \<rho> A) \<longrightarrow> holds (eval \<rho> B))"
| "eval \<rho> (Forall \<sigma> A) =
    truth_den (\<forall>x \<in> D \<sigma>. holds (eval (extend_env x \<rho>) A))"
| "eval \<rho> (Exists \<sigma> A) =
    truth_den (\<exists>x \<in> D \<sigma>. holds (eval (extend_env x \<rho>) A))"

lemma eval_type:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
    and "env_typed \<Gamma> \<rho>"
  shows "eval \<rho> M \<in> D \<tau>"
  using assms
proof (induction arbitrary: \<rho> rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  have "\<rho> n \<in> D \<tau>"
    using Var.prems Var.hyps
    by (rule env_typed_lookup)
  then show ?case
    by simp
next
  case (Const \<Gamma> c \<tau>)
  show ?case
    by (simp add: const_den_type)
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have "eval \<rho> M \<in> D (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    using App.IH(1) App.prems by blast
  moreover have "eval \<rho> N \<in> D \<sigma>"
    using App.IH(2) App.prems by blast
  ultimately show ?case
    by (simp add: app_den_type)
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have "\<And>x. x \<in> D \<sigma> \<Longrightarrow> eval (extend_env x \<rho>) M \<in> D \<tau>"
    using Lam.IH Lam.prems by (simp add: env_typed_extend)
  then show ?case
    by (simp add: lam_den_type)
next
  case (Eq \<Gamma> M \<sigma> N)
  then show ?case
    by (simp add: truth_den_type)
next
  case (Neg \<Gamma> A)
  then show ?case
    by (simp add: truth_den_type)
next
  case (Conj \<Gamma> A B)
  then show ?case
    by (simp add: truth_den_type)
next
  case (Disj \<Gamma> A B)
  then show ?case
    by (simp add: truth_den_type)
next
  case (Imp \<Gamma> A B)
  then show ?case
    by (simp add: truth_den_type)
next
  case (Forall \<sigma> \<Gamma> A)
  then show ?case
    by (simp add: truth_den_type)
next
  case (Exists \<sigma> \<Gamma> A)
  then show ?case
    by (simp add: truth_den_type)
qed

lemma holds_eval_prop_eval:
  "holds (eval \<rho> A) = prop_eval (\<lambda>B. holds (eval \<rho> B)) A"
  by (induction A arbitrary: \<rho>) simp_all

lemma prop_tautology_sound:
  assumes "prop_tautology \<Gamma> A"
    and "env_typed \<Gamma> \<rho>"
  shows "holds (eval \<rho> A)"
proof -
  have "\<forall>v. prop_eval v A"
    using assms(1) unfolding prop_tautology_def by blast
  then have "prop_eval (\<lambda>B. holds (eval \<rho> B)) A"
    by blast
  moreover have "holds (eval \<rho> A) = prop_eval (\<lambda>B. holds (eval \<rho> B)) A"
    by (rule holds_eval_prop_eval)
  then show ?thesis
    using calculation by blast
qed

definition valid_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "valid_in_context \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and> (\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow> holds (eval \<rho> A))"

lemma prop_tautology_valid:
  assumes "prop_tautology \<Gamma> A"
  shows "valid_in_context \<Gamma> A"
proof -
  have "\<Gamma> \<turnstile> A : Prop"
    using assms unfolding prop_tautology_def by blast
  moreover have "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow> holds (eval \<rho> A)"
    using prop_tautology_sound[OF assms] by blast
  ultimately show ?thesis
    unfolding valid_in_context_def by blast
qed

subsection \<open>Semantic substitution and conversion\<close>

lemma eval_rename:
  "eval \<rho> (rename r M) = eval (\<lambda>n. \<rho> (r n)) M"
proof (induction M arbitrary: \<rho> r)
  case (Lam \<sigma> M)
  show ?case
  proof (simp, rule lam_den_cong)
    fix x
    assume "x \<in> D \<sigma>"
    have env_eq: "(\<lambda>n. extend_env x \<rho> (lift_ren r n)) =
        extend_env x (\<lambda>n. \<rho> (r n))"
      by (rule ext) (case_tac n; simp)
    have "eval (extend_env x \<rho>) (rename (lift_ren r) M) =
        eval (\<lambda>n. extend_env x \<rho> (lift_ren r n)) M"
      by (rule Lam.IH)
    then show "eval (extend_env x \<rho>) (rename (lift_ren r) M) =
        eval (extend_env x (\<lambda>n. \<rho> (r n))) M"
      by (simp add: env_eq)
  qed
next
  case (Forall \<sigma> M)
  have pred_eq: "\<And>x. x \<in> D \<sigma> \<Longrightarrow>
      holds (eval (extend_env x \<rho>) (rename (lift_ren r) M)) =
      holds (eval (extend_env x (\<lambda>n. \<rho> (r n))) M)"
  proof -
    fix x
    assume "x \<in> D \<sigma>"
    have env_eq: "(\<lambda>n. extend_env x \<rho> (lift_ren r n)) =
        extend_env x (\<lambda>n. \<rho> (r n))"
      by (rule ext) (case_tac n; simp)
    show "holds (eval (extend_env x \<rho>) (rename (lift_ren r) M)) =
        holds (eval (extend_env x (\<lambda>n. \<rho> (r n))) M)"
      using Forall.IH[of "extend_env x \<rho>" "lift_ren r"]
      by (simp add: env_eq)
  qed
  have "(\<forall>x\<in>D \<sigma>. holds (eval (extend_env x \<rho>) (rename (lift_ren r) M))) =
      (\<forall>x\<in>D \<sigma>. holds (eval (extend_env x (\<lambda>n. \<rho> (r n))) M))"
    using pred_eq by blast
  then show ?case
    by simp
next
  case (Exists \<sigma> M)
  have pred_eq: "\<And>x. x \<in> D \<sigma> \<Longrightarrow>
      holds (eval (extend_env x \<rho>) (rename (lift_ren r) M)) =
      holds (eval (extend_env x (\<lambda>n. \<rho> (r n))) M)"
  proof -
    fix x
    assume "x \<in> D \<sigma>"
    have env_eq: "(\<lambda>n. extend_env x \<rho> (lift_ren r n)) =
        extend_env x (\<lambda>n. \<rho> (r n))"
      by (rule ext) (case_tac n; simp)
    show "holds (eval (extend_env x \<rho>) (rename (lift_ren r) M)) =
        holds (eval (extend_env x (\<lambda>n. \<rho> (r n))) M)"
      using Exists.IH[of "extend_env x \<rho>" "lift_ren r"]
      by (simp add: env_eq)
  qed
  have "(\<exists>x\<in>D \<sigma>. holds (eval (extend_env x \<rho>) (rename (lift_ren r) M))) =
      (\<exists>x\<in>D \<sigma>. holds (eval (extend_env x (\<lambda>n. \<rho> (r n))) M))"
    using pred_eq by blast
  then show ?case
    by simp
qed simp_all

lemma eval_shift:
  "eval (extend_env x \<rho>) (shift M) = eval \<rho> M"
  unfolding shift_def
  using eval_rename[of "extend_env x \<rho>" Suc M]
  by simp

lemma eval_rename_Suc_extend:
  "eval (extend_env x \<rho>) (rename Suc M) = eval \<rho> M"
  using eval_shift[of x \<rho> M]
  unfolding shift_def
  by simp

lemma eval_shift_by_extend_envs:
  "eval (extend_envs xs \<rho>) (shift_by (length xs) M) = eval \<rho> M"
proof -
  have env_eq: "(\<lambda>n. extend_envs xs \<rho> (shift_ren (length xs) 0 n)) = \<rho>"
  proof (rule ext)
    fix n
    have "extend_envs xs \<rho> (shift_ren (length xs) 0 n) =
        extend_envs xs \<rho> (length xs + n)"
      by (simp add: shift_ren_def add.commute)
    also have "... = \<rho> n"
      by (rule extend_envs_after)
    finally show "extend_envs xs \<rho> (shift_ren (length xs) 0 n) = \<rho> n" .
  qed
  show ?thesis
    unfolding shift_by_def
    using eval_rename[of "extend_envs xs \<rho>" "shift_ren (length xs) 0" M]
    by (simp add: env_eq)
qed

lemma eval_subst:
  "eval \<rho> (subst s M) = eval (\<lambda>n. eval \<rho> (s n)) M"
proof (induction M arbitrary: \<rho> s)
  case (Lam \<sigma> M)
  show ?case
  proof (simp, rule lam_den_cong)
    fix x
    assume "x \<in> D \<sigma>"
    have env_eq: "(\<lambda>n. eval (extend_env x \<rho>) (lift_subst s n)) =
        extend_env x (\<lambda>n. eval \<rho> (s n))"
    proof (rule ext)
      fix n
      show "eval (extend_env x \<rho>) (lift_subst s n) =
          extend_env x (\<lambda>n. eval \<rho> (s n)) n"
        by (cases n) (simp_all add: eval_rename_Suc_extend)
    qed
    have "eval (extend_env x \<rho>) (subst (lift_subst s) M) =
        eval (\<lambda>n. eval (extend_env x \<rho>) (lift_subst s n)) M"
      by (rule Lam.IH)
    then show "eval (extend_env x \<rho>) (subst (lift_subst s) M) =
        eval (extend_env x (\<lambda>n. eval \<rho> (s n))) M"
      by (simp add: env_eq)
  qed
next
  case (Forall \<sigma> M)
  have pred_eq: "\<And>x. x \<in> D \<sigma> \<Longrightarrow>
      holds (eval (extend_env x \<rho>) (subst (lift_subst s) M)) =
      holds (eval (extend_env x (\<lambda>n. eval \<rho> (s n))) M)"
  proof -
    fix x
    assume "x \<in> D \<sigma>"
    have env_eq: "(\<lambda>n. eval (extend_env x \<rho>) (lift_subst s n)) =
        extend_env x (\<lambda>n. eval \<rho> (s n))"
      by (rule ext) (case_tac n; simp add: eval_rename_Suc_extend)
    show "holds (eval (extend_env x \<rho>) (subst (lift_subst s) M)) =
        holds (eval (extend_env x (\<lambda>n. eval \<rho> (s n))) M)"
      using Forall.IH[of "extend_env x \<rho>" "lift_subst s"]
      by (simp add: env_eq)
  qed
  have "(\<forall>x\<in>D \<sigma>. holds (eval (extend_env x \<rho>) (subst (lift_subst s) M))) =
      (\<forall>x\<in>D \<sigma>. holds (eval (extend_env x (\<lambda>n. eval \<rho> (s n))) M))"
    using pred_eq by blast
  then show ?case
    by simp
next
  case (Exists \<sigma> M)
  have pred_eq: "\<And>x. x \<in> D \<sigma> \<Longrightarrow>
      holds (eval (extend_env x \<rho>) (subst (lift_subst s) M)) =
      holds (eval (extend_env x (\<lambda>n. eval \<rho> (s n))) M)"
  proof -
    fix x
    assume "x \<in> D \<sigma>"
    have env_eq: "(\<lambda>n. eval (extend_env x \<rho>) (lift_subst s n)) =
        extend_env x (\<lambda>n. eval \<rho> (s n))"
      by (rule ext) (case_tac n; simp add: eval_rename_Suc_extend)
    show "holds (eval (extend_env x \<rho>) (subst (lift_subst s) M)) =
        holds (eval (extend_env x (\<lambda>n. eval \<rho> (s n))) M)"
      using Exists.IH[of "extend_env x \<rho>" "lift_subst s"]
      by (simp add: env_eq)
  qed
  have "(\<exists>x\<in>D \<sigma>. holds (eval (extend_env x \<rho>) (subst (lift_subst s) M))) =
      (\<exists>x\<in>D \<sigma>. holds (eval (extend_env x (\<lambda>n. eval \<rho> (s n))) M))"
    using pred_eq by blast
  then show ?case
    by simp
qed simp_all

lemma eval_subst0:
  "eval \<rho> (subst0 T M) = eval (extend_env (eval \<rho> T) \<rho>) M"
proof -
  have env_eq: "(\<lambda>n. eval \<rho> (case_nat T Var n)) =
      extend_env (eval \<rho> T) \<rho>"
    by (rule ext) (case_tac n; simp)
  show ?thesis
    unfolding subst0_def
    using eval_subst[of \<rho> "case_nat T Var" M]
    by (simp add: env_eq)
qed

lemma eval_app_vec:
  "eval \<rho> (app_vec F As) =
    app_den_vec app_den (eval \<rho> F) (map (eval \<rho>) As)"
  by (induction As arbitrary: F) simp_all

lemma map_eval_fresh_vars_extend_envs:
  "map (eval (extend_envs xs \<rho>)) (fresh_vars (length xs)) = xs"
  unfolding fresh_vars_def
  by (rule nth_equalityI) (simp_all add: extend_envs_nth_less)

definition eval_preserving_step :: "(oterm \<Rightarrow> oterm \<Rightarrow> bool) \<Rightarrow> bool" where
  "eval_preserving_step R \<longleftrightarrow>
    (\<forall>\<Gamma> M N \<tau> \<rho>. R M N \<longrightarrow> \<Gamma> \<turnstile> M : \<tau> \<longrightarrow> \<Gamma> \<turnstile> N : \<tau> \<longrightarrow>
      env_typed \<Gamma> \<rho> \<longrightarrow> eval \<rho> M = eval \<rho> N)"

lemma beta_contract_eval_preserving:
  "eval_preserving_step beta_contract"
  unfolding eval_preserving_step_def
proof (intro allI impI)
  fix \<Gamma> M N \<tau> \<rho>
  assume beta: "beta_contract M N"
    and M_type: "\<Gamma> \<turnstile> M : \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<tau>"
    and env: "env_typed \<Gamma> \<rho>"
  show "eval \<rho> M = eval \<rho> N"
    using beta
  proof cases
    case (beta \<sigma> P Q)
    then have app_type: "\<Gamma> \<turnstile> App (Lam \<sigma> P) Q : \<tau>"
      using M_type by simp
    then obtain \<mu> where lam_type: "\<Gamma> \<turnstile> Lam \<sigma> P : \<mu> \<rightarrow>\<^sub>o \<tau>"
      and Q_type: "\<Gamma> \<turnstile> Q : \<mu>"
      by (auto elim: has_type.cases)
    then have "\<mu> = \<sigma>" and body_type: "\<sigma> # \<Gamma> \<turnstile> P : \<tau>"
      by (auto elim: has_type.cases dest: typing_unique)
    then have Q_sigma: "\<Gamma> \<turnstile> Q : \<sigma>"
      using Q_type by simp
    have Q_den: "eval \<rho> Q \<in> D \<sigma>"
      using Q_sigma env by (rule eval_type)
    have "eval \<rho> (App (Lam \<sigma> P) Q) =
        eval (extend_env (eval \<rho> Q) \<rho>) P"
      using beta_den[OF Q_den] by simp
    also have "... = eval \<rho> (subst0 Q P)"
      using eval_subst0[of \<rho> Q P] by simp
    finally show ?thesis
      using beta by simp
  qed
qed

lemma eta_contract_eval_preserving:
  "eval_preserving_step eta_contract"
  unfolding eval_preserving_step_def
proof (intro allI impI)
  fix \<Gamma> M N \<tau> \<rho>
  assume eta: "eta_contract M N"
    and M_type: "\<Gamma> \<turnstile> M : \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<tau>"
    and env: "env_typed \<Gamma> \<rho>"
  obtain \<sigma> F where M_def: "M = Lam \<sigma> (App (shift F) (Var 0))"
    and N_def: "N = F"
    using eta by cases auto
  then have lam_type: "\<Gamma> \<turnstile> Lam \<sigma> (App (shift F) (Var 0)) : \<tau>"
    using M_type by simp
  then obtain \<mu> where tau_def: "\<tau> = \<sigma> \<rightarrow>\<^sub>o \<mu>"
    by (auto elim: has_type.cases)
  have F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<mu>"
    using N_type N_def tau_def by simp
  have F_den: "eval \<rho> F \<in> D (\<sigma> \<rightarrow>\<^sub>o \<mu>)"
    using F_type env by (rule eval_type)
  have "eval \<rho> (Lam \<sigma> (App (shift F) (Var 0))) =
      lam_den \<sigma> (\<lambda>x. app_den (eval \<rho> F) x)"
  proof (simp, rule lam_den_cong)
    fix x
    assume "x \<in> D \<sigma>"
    show "app_den (eval (extend_env x \<rho>) (shift F)) x =
        app_den (eval \<rho> F) x"
      by (simp add: eval_shift)
  qed
  also have "... = eval \<rho> F"
    using eta_den[OF F_den] by simp
  finally show "eval \<rho> M = eval \<rho> N"
    using M_def N_def by simp
qed

lemma compatible_step_eval:
  assumes step: "compatible_step R M N"
    and preserving: "eval_preserving_step R"
    and M_type: "\<Gamma> \<turnstile> M : \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<tau>"
    and env: "env_typed \<Gamma> \<rho>"
  shows "eval \<rho> M = eval \<rho> N"
  using step M_type N_type env
proof (induction arbitrary: \<Gamma> \<tau> \<rho> rule: compatible_step.induct)
  case (root M N)
  then show ?case
    using preserving unfolding eval_preserving_step_def by blast
next
  case (App_left M M' N)
  then obtain \<sigma> where M_type: "\<Gamma> \<turnstile> M : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    by (auto elim: has_type.cases)
  moreover obtain \<sigma>' where M'_type: "\<Gamma> \<turnstile> M' : \<sigma>' \<rightarrow>\<^sub>o \<tau>"
    and N_type': "\<Gamma> \<turnstile> N : \<sigma>'"
    using App_left.prems(2) by (auto elim: has_type.cases)
  ultimately have "\<sigma>' = \<sigma>"
    using typing_unique by blast
  then have "eval \<rho> M = eval \<rho> M'"
    using App_left.IH[OF M_type _ App_left.prems(3)] M'_type by simp
  then show ?case
    by simp
next
  case (App_right N N' M)
  then obtain \<sigma> where M_type: "\<Gamma> \<turnstile> M : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    by (auto elim: has_type.cases)
  moreover obtain \<sigma>' where M_type': "\<Gamma> \<turnstile> M : \<sigma>' \<rightarrow>\<^sub>o \<tau>"
    and N'_type: "\<Gamma> \<turnstile> N' : \<sigma>'"
    using App_right.prems(2) by (auto elim: has_type.cases)
  ultimately have "\<sigma>' = \<sigma>"
    using typing_unique by blast
  then have "eval \<rho> N = eval \<rho> N'"
    using App_right.IH[OF N_type _ App_right.prems(3)] N'_type by simp
  then show ?case
    by simp
next
  case (Lam_body M M' \<sigma>)
  then obtain \<mu> where tau_def: "\<tau> = \<sigma> \<rightarrow>\<^sub>o \<mu>"
    and M_type: "\<sigma> # \<Gamma> \<turnstile> M : \<mu>"
    by (auto elim: has_type.cases)
  moreover obtain \<mu>' where tau_def': "\<tau> = \<sigma> \<rightarrow>\<^sub>o \<mu>'"
    and M'_type: "\<sigma> # \<Gamma> \<turnstile> M' : \<mu>'"
    using Lam_body.prems(2) by (auto elim: has_type.cases)
  ultimately have "\<mu>' = \<mu>"
    by simp
  show ?case
  proof (simp, rule lam_den_cong)
    fix x
    assume x_type: "x \<in> D \<sigma>"
    have env_ext: "env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
      using Lam_body.prems(3) x_type by (rule env_typed_extend)
    show "eval (extend_env x \<rho>) M = eval (extend_env x \<rho>) M'"
      using Lam_body.IH[OF M_type _ env_ext] M'_type \<open>\<mu>' = \<mu>\<close> by simp
  qed
next
  case (Eq_left M M' \<sigma> N)
  then have M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and M'_type: "\<Gamma> \<turnstile> M' : \<sigma>"
    by (auto elim: has_type.cases)
  have "eval \<rho> M = eval \<rho> M'"
    using Eq_left.IH[OF M_type M'_type Eq_left.prems(3)] .
  then show ?case
    by simp
next
  case (Eq_right N N' \<sigma> M)
  then have N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and N'_type: "\<Gamma> \<turnstile> N' : \<sigma>"
    by (auto elim: has_type.cases)
  have "eval \<rho> N = eval \<rho> N'"
    using Eq_right.IH[OF N_type N'_type Eq_right.prems(3)] .
  then show ?case
    by simp
next
  case (Neg_body A A')
  then have A_type: "\<Gamma> \<turnstile> A : Prop"
    and A'_type: "\<Gamma> \<turnstile> A' : Prop"
    by (auto elim: has_type.cases)
  have "eval \<rho> A = eval \<rho> A'"
    using Neg_body.IH[OF A_type A'_type Neg_body.prems(3)] .
  then show ?case
    by simp
next
  case (Conj_left A A' B)
  then have A_type: "\<Gamma> \<turnstile> A : Prop"
    and A'_type: "\<Gamma> \<turnstile> A' : Prop"
    by (auto elim: has_type.cases)
  have "eval \<rho> A = eval \<rho> A'"
    using Conj_left.IH[OF A_type A'_type Conj_left.prems(3)] .
  then show ?case
    by simp
next
  case (Conj_right B B' A)
  then have B_type: "\<Gamma> \<turnstile> B : Prop"
    and B'_type: "\<Gamma> \<turnstile> B' : Prop"
    by (auto elim: has_type.cases)
  have "eval \<rho> B = eval \<rho> B'"
    using Conj_right.IH[OF B_type B'_type Conj_right.prems(3)] .
  then show ?case
    by simp
next
  case (Disj_left A A' B)
  then have A_type: "\<Gamma> \<turnstile> A : Prop"
    and A'_type: "\<Gamma> \<turnstile> A' : Prop"
    by (auto elim: has_type.cases)
  have "eval \<rho> A = eval \<rho> A'"
    using Disj_left.IH[OF A_type A'_type Disj_left.prems(3)] .
  then show ?case
    by simp
next
  case (Disj_right B B' A)
  then have B_type: "\<Gamma> \<turnstile> B : Prop"
    and B'_type: "\<Gamma> \<turnstile> B' : Prop"
    by (auto elim: has_type.cases)
  have "eval \<rho> B = eval \<rho> B'"
    using Disj_right.IH[OF B_type B'_type Disj_right.prems(3)] .
  then show ?case
    by simp
next
  case (Imp_left A A' B)
  then have A_type: "\<Gamma> \<turnstile> A : Prop"
    and A'_type: "\<Gamma> \<turnstile> A' : Prop"
    by (auto elim: has_type.cases)
  have "eval \<rho> A = eval \<rho> A'"
    using Imp_left.IH[OF A_type A'_type Imp_left.prems(3)] .
  then show ?case
    by simp
next
  case (Imp_right B B' A)
  then have B_type: "\<Gamma> \<turnstile> B : Prop"
    and B'_type: "\<Gamma> \<turnstile> B' : Prop"
    by (auto elim: has_type.cases)
  have "eval \<rho> B = eval \<rho> B'"
    using Imp_right.IH[OF B_type B'_type Imp_right.prems(3)] .
  then show ?case
    by simp
next
  case (Forall_body A A' \<sigma>)
  then have A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and A'_type: "\<sigma> # \<Gamma> \<turnstile> A' : Prop"
    by (auto elim: has_type.cases)
  have pred_eq: "\<And>x. x \<in> D \<sigma> \<Longrightarrow>
      holds (eval (extend_env x \<rho>) A) =
      holds (eval (extend_env x \<rho>) A')"
  proof -
    fix x
    assume x_type: "x \<in> D \<sigma>"
    have env_ext: "env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
      using Forall_body.prems(3) x_type by (rule env_typed_extend)
    show "holds (eval (extend_env x \<rho>) A) =
        holds (eval (extend_env x \<rho>) A')"
      using Forall_body.IH[OF A_type A'_type env_ext] by simp
  qed
  have "(\<forall>x\<in>D \<sigma>. holds (eval (extend_env x \<rho>) A)) =
      (\<forall>x\<in>D \<sigma>. holds (eval (extend_env x \<rho>) A'))"
    using pred_eq by blast
  then show ?case
    by simp
next
  case (Exists_body A A' \<sigma>)
  then have A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and A'_type: "\<sigma> # \<Gamma> \<turnstile> A' : Prop"
    by (auto elim: has_type.cases)
  have pred_eq: "\<And>x. x \<in> D \<sigma> \<Longrightarrow>
      holds (eval (extend_env x \<rho>) A) =
      holds (eval (extend_env x \<rho>) A')"
  proof -
    fix x
    assume x_type: "x \<in> D \<sigma>"
    have env_ext: "env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
      using Exists_body.prems(3) x_type by (rule env_typed_extend)
    show "holds (eval (extend_env x \<rho>) A) =
        holds (eval (extend_env x \<rho>) A')"
      using Exists_body.IH[OF A_type A'_type env_ext] by simp
  qed
  have "(\<exists>x\<in>D \<sigma>. holds (eval (extend_env x \<rho>) A)) =
      (\<exists>x\<in>D \<sigma>. holds (eval (extend_env x \<rho>) A'))"
    using pred_eq by blast
  then show ?case
    by simp
qed

lemma beta_compatible_eval:
  assumes "compatible_step beta_contract M N"
    and "\<Gamma> \<turnstile> M : \<tau>"
    and "\<Gamma> \<turnstile> N : \<tau>"
    and "env_typed \<Gamma> \<rho>"
  shows "eval \<rho> M = eval \<rho> N"
  by (rule compatible_step_eval
      [OF assms(1) beta_contract_eval_preserving assms(2) assms(3) assms(4)])

lemma eta_compatible_eval:
  assumes "compatible_step eta_contract M N"
    and "\<Gamma> \<turnstile> M : \<tau>"
    and "\<Gamma> \<turnstile> N : \<tau>"
    and "env_typed \<Gamma> \<rho>"
  shows "eval \<rho> M = eval \<rho> N"
  by (rule compatible_step_eval
      [OF assms(1) eta_contract_eval_preserving assms(2) assms(3) assms(4)])

subsection \<open>Soundness for H\<close>

lemma valid_formula:
  assumes "valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms unfolding valid_in_context_def by blast

lemma valid_holds:
  assumes "valid_in_context \<Gamma> A"
    and "env_typed \<Gamma> \<rho>"
  shows "holds (eval \<rho> A)"
  using assms unfolding valid_in_context_def by blast

lemma valid_MP:
  assumes "valid_in_context \<Gamma> A"
    and "valid_in_context \<Gamma> (Imp A B)"
  shows "valid_in_context \<Gamma> B"
proof -
  have imp_type: "\<Gamma> \<turnstile> Imp A B : Prop"
    using assms(2) by (rule valid_formula)
  then have B_type: "\<Gamma> \<turnstile> B : Prop"
    by (auto elim: has_type.cases)
  have "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow> holds (eval \<rho> B)"
  proof (intro allI impI)
    fix \<rho>
    assume env: "env_typed \<Gamma> \<rho>"
    have A_holds: "holds (eval \<rho> A)"
      using assms(1) env by (rule valid_holds)
    have imp_holds: "holds (eval \<rho> (Imp A B))"
      using assms(2) env by (rule valid_holds)
    show "holds (eval \<rho> B)"
      using A_holds imp_holds by simp
  qed
  then show ?thesis
    unfolding valid_in_context_def using B_type by blast
qed

lemma H_UI_valid:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> T : \<sigma>"
  shows "valid_in_context \<Gamma> (Imp (Forall \<sigma> A) (subst0 T A))"
proof -
  have forall_type: "\<Gamma> \<turnstile> Forall \<sigma> A : Prop"
    using assms(1) by auto
  have subst_type: "\<Gamma> \<turnstile> subst0 T A : Prop"
    using assms by (rule subst0_preserves_typing)
  have "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow>
      holds (eval \<rho> (Imp (Forall \<sigma> A) (subst0 T A)))"
  proof (intro allI impI)
    fix \<rho>
    assume env: "env_typed \<Gamma> \<rho>"
    have T_den: "eval \<rho> T \<in> D \<sigma>"
      using assms(2) env by (rule eval_type)
    have subst_eval: "eval \<rho> (subst0 T A) =
        eval (extend_env (eval \<rho> T) \<rho>) A"
      by (rule eval_subst0)
    show "holds (eval \<rho> (Imp (Forall \<sigma> A) (subst0 T A)))"
      using T_den subst_eval by simp
  qed
  then show ?thesis
    unfolding valid_in_context_def
    using forall_type subst_type by blast
qed

lemma H_EG_valid:
  assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> T : \<sigma>"
  shows "valid_in_context \<Gamma> (Imp (subst0 T A) (Exists \<sigma> A))"
proof -
  have subst_type: "\<Gamma> \<turnstile> subst0 T A : Prop"
    using assms by (rule subst0_preserves_typing)
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using assms(1) by auto
  have "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow>
      holds (eval \<rho> (Imp (subst0 T A) (Exists \<sigma> A)))"
  proof (intro allI impI)
    fix \<rho>
	    assume env: "env_typed \<Gamma> \<rho>"
	    have T_den: "eval \<rho> T \<in> D \<sigma>"
	      using assms(2) env by (rule eval_type)
	    have subst_eval: "eval \<rho> (subst0 T A) =
	        eval (extend_env (eval \<rho> T) \<rho>) A"
	      by (rule eval_subst0)
	    show "holds (eval \<rho> (Imp (subst0 T A) (Exists \<sigma> A)))"
	    proof (simp, intro impI)
	      assume "holds (eval \<rho> (subst0 T A))"
	      then have "holds (eval (extend_env (eval \<rho> T) \<rho>) A)"
	        using subst_eval by simp
	      then show "\<exists>x\<in>D \<sigma>. holds (eval (extend_env x \<rho>) A)"
	        using T_den by blast
	    qed
  qed
  then show ?thesis
    unfolding valid_in_context_def
    using subst_type exists_type by blast
qed

lemma H_Ref_valid:
  assumes "\<Gamma> \<turnstile> M : \<sigma>"
  shows "valid_in_context \<Gamma> (Eq \<sigma> M M)"
proof -
  have formula_type: "\<Gamma> \<turnstile> Eq \<sigma> M M : Prop"
    using assms by auto
  have "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow> holds (eval \<rho> (Eq \<sigma> M M))"
  proof (intro allI impI)
    fix \<rho>
    assume env: "env_typed \<Gamma> \<rho>"
    have "eval \<rho> M \<in> D \<sigma>"
      using assms env by (rule eval_type)
    then show "holds (eval \<rho> (Eq \<sigma> M M))"
      by (simp add: eq_den_refl)
  qed
  then show ?thesis
    unfolding valid_in_context_def using formula_type by blast
qed

lemma H_LL_valid:
  assumes "\<Gamma> \<turnstile> A : \<sigma>"
    and "\<Gamma> \<turnstile> B : \<sigma>"
    and "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "valid_in_context \<Gamma> (Imp (Eq \<sigma> A B) (Imp (App F A) (App F B)))"
proof -
  have formula_type: "\<Gamma> \<turnstile> Imp (Eq \<sigma> A B) (Imp (App F A) (App F B)) : Prop"
    using assms by auto
  have "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow>
      holds (eval \<rho> (Imp (Eq \<sigma> A B) (Imp (App F A) (App F B))))"
  proof (intro allI impI)
    fix \<rho>
    assume env: "env_typed \<Gamma> \<rho>"
    have A_den: "eval \<rho> A \<in> D \<sigma>"
      using assms(1) env by (rule eval_type)
    have B_den: "eval \<rho> B \<in> D \<sigma>"
      using assms(2) env by (rule eval_type)
    have F_den: "eval \<rho> F \<in> D (\<sigma> \<rightarrow>\<^sub>o Prop)"
      using assms(3) env by (rule eval_type)
    show "holds (eval \<rho> (Imp (Eq \<sigma> A B) (Imp (App F A) (App F B))))"
      using eq_den_subst[OF _ F_den A_den B_den] by simp
  qed
  then show ?thesis
    unfolding valid_in_context_def using formula_type by blast
qed

lemma H_Beta_valid:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step beta_contract A B"
  shows "valid_in_context \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have formula_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using assms(1,2) by auto
  have "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow> holds (eval \<rho> (A \<longleftrightarrow>\<^sub>o B))"
	  proof (intro allI impI)
	    fix \<rho>
	    assume env: "env_typed \<Gamma> \<rho>"
	    have "eval \<rho> A = eval \<rho> B"
	      by (rule beta_compatible_eval[OF assms(3) assms(1) assms(2) env])
	    then show "holds (eval \<rho> (A \<longleftrightarrow>\<^sub>o B))"
	      by simp
	  qed
  then show ?thesis
    unfolding valid_in_context_def using formula_type by blast
qed

lemma H_Eta_valid:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step eta_contract A B"
  shows "valid_in_context \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have formula_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using assms(1,2) by auto
  have "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow> holds (eval \<rho> (A \<longleftrightarrow>\<^sub>o B))"
	  proof (intro allI impI)
	    fix \<rho>
	    assume env: "env_typed \<Gamma> \<rho>"
	    have "eval \<rho> A = eval \<rho> B"
	      by (rule eta_compatible_eval[OF assms(3) assms(1) assms(2) env])
	    then show "holds (eval \<rho> (A \<longleftrightarrow>\<^sub>o B))"
	      by simp
	  qed
  then show ?thesis
    unfolding valid_in_context_def using formula_type by blast
qed

lemma H_Gen_valid:
  assumes "\<Gamma> \<turnstile> P : Prop"
    and "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and "valid_in_context (\<sigma> # \<Gamma>) (Imp (shift P) Q)"
  shows "valid_in_context \<Gamma> (Imp P (Forall \<sigma> Q))"
proof -
  have formula_type: "\<Gamma> \<turnstile> Imp P (Forall \<sigma> Q) : Prop"
    using assms(1,2) by auto
  have "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow> holds (eval \<rho> (Imp P (Forall \<sigma> Q)))"
  proof (intro allI impI)
    fix \<rho>
    assume env: "env_typed \<Gamma> \<rho>"
    show "holds (eval \<rho> (Imp P (Forall \<sigma> Q)))"
    proof (simp, intro impI ballI)
      assume P_holds: "holds (eval \<rho> P)"
      fix x
      assume x_type: "x \<in> D \<sigma>"
      have env_ext: "env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
        using env x_type by (rule env_typed_extend)
      have imp_holds: "holds (eval (extend_env x \<rho>) (Imp (shift P) Q))"
        using assms(3) env_ext by (rule valid_holds)
      have shift_holds: "holds (eval (extend_env x \<rho>) (shift P))"
        using P_holds by (simp add: eval_shift)
      show "holds (eval (extend_env x \<rho>) Q)"
        using imp_holds shift_holds by simp
    qed
  qed
  then show ?thesis
    unfolding valid_in_context_def using formula_type by blast
qed

lemma H_Inst_valid:
  assumes "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and "\<Gamma> \<turnstile> Q : Prop"
    and "valid_in_context (\<sigma> # \<Gamma>) (Imp P (shift Q))"
  shows "valid_in_context \<Gamma> (Imp (Exists \<sigma> P) Q)"
proof -
  have formula_type: "\<Gamma> \<turnstile> Imp (Exists \<sigma> P) Q : Prop"
    using assms(1,2) by auto
  have "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow> holds (eval \<rho> (Imp (Exists \<sigma> P) Q))"
  proof (intro allI impI)
    fix \<rho>
    assume env: "env_typed \<Gamma> \<rho>"
    show "holds (eval \<rho> (Imp (Exists \<sigma> P) Q))"
    proof (simp, intro impI)
      assume "\<exists>x\<in>D \<sigma>. holds (eval (extend_env x \<rho>) P)"
      then obtain x where x_type: "x \<in> D \<sigma>"
        and P_holds: "holds (eval (extend_env x \<rho>) P)"
        by blast
      have env_ext: "env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
        using env x_type by (rule env_typed_extend)
      have imp_holds: "holds (eval (extend_env x \<rho>) (Imp P (shift Q)))"
        using assms(3) env_ext by (rule valid_holds)
      have shift_Q: "holds (eval (extend_env x \<rho>) (shift Q)) = holds (eval \<rho> Q)"
        by (simp add: eval_shift)
      show "holds (eval \<rho> Q)"
        using imp_holds P_holds shift_Q by simp
    qed
  qed
  then show ?thesis
    unfolding valid_in_context_def using formula_type by blast
qed

theorem H_soundness:
  assumes "\<Gamma> \<turnstile>\<^sub>H A"
  shows "valid_in_context \<Gamma> A"
  using assms
proof (induction rule: H_proves.induct)
  case (PC \<Gamma> A)
  then show ?case
    by (rule prop_tautology_valid)
next
  case (IndividualExistence \<Gamma>)
  show ?case
  proof (unfold valid_in_context_def, intro conjI)
    show "\<Gamma> \<turnstile> Exists Ind (Eq Ind (Var 0) (Var 0)) : Prop"
      by (rule has_type.Exists, rule has_type.Eq; simp)
    show "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow>
        holds (eval \<rho> (Exists Ind (Eq Ind (Var 0) (Var 0))))"
    proof (intro allI impI)
      fix \<rho>
      assume "env_typed \<Gamma> \<rho>"
      have witness: "const_den ''existence-witness'' Ind \<in> D Ind"
        by (rule const_den_type)
      have reflexive:
          "eq_den Ind (const_den ''existence-witness'' Ind)
            (const_den ''existence-witness'' Ind)"
        by (rule eq_den_refl[OF witness])
      show "holds (eval \<rho>
          (Exists Ind (Eq Ind (Var 0) (Var 0))))"
        using witness reflexive by (simp; blast)
    qed
  qed
next
  case (UI \<sigma> \<Gamma> A T)
  then show ?case
    by (rule H_UI_valid)
next
  case (EG \<sigma> \<Gamma> A T)
  then show ?case
    by (rule H_EG_valid)
next
  case (Ref \<Gamma> M \<sigma>)
  then show ?case
    by (rule H_Ref_valid)
next
  case (LL \<Gamma> A \<sigma> B F)
  then show ?case
    by (rule H_LL_valid)
next
  case (Beta \<Gamma> A B)
  then show ?case
    by (rule H_Beta_valid)
next
  case (Eta \<Gamma> A B)
  then show ?case
    by (rule H_Eta_valid)
next
  case (MP \<Gamma> A B)
  show ?case
    by (rule valid_MP[OF MP.IH(1) MP.IH(2)])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case
    by (rule H_Gen_valid[OF Gen.hyps(1) Gen.hyps(2) Gen.IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case
    by (rule H_Inst_valid[OF Inst.hyps(1) Inst.hyps(2) Inst.IH])
qed

end

locale classicist_structure = applicative_structure +
  assumes boolean_identity_valid:
      "A \<in> set all_boolean_identities \<Longrightarrow> valid_in_context \<Gamma> A"
    and classic_identity_identity_valid:
      "valid_in_context \<Gamma> (classic_identity_identity \<sigma>)"
    and classic_absorb_disj_forall_valid:
      "valid_in_context \<Gamma> (classic_absorb_disj_forall \<sigma>)"
    and classic_dist_disj_forall_valid:
      "valid_in_context \<Gamma> (classic_dist_disj_forall \<sigma>)"
    and classic_absorb_conj_exists_valid:
      "valid_in_context \<Gamma> (classic_absorb_conj_exists \<sigma>)"
    and classic_dist_conj_exists_valid:
      "valid_in_context \<Gamma> (classic_dist_conj_exists \<sigma>)"
begin

theorem C_soundness:
  assumes "\<Gamma> \<turnstile>\<^sub>C A"
  shows "valid_in_context \<Gamma> A"
  using assms
proof (induction rule: C_proves.induct)
  case (H \<Gamma> A)
  then show ?case
    by (rule H_soundness)
next
  case (BooleanIdentity A \<Gamma>)
  then show ?case
    by (rule boolean_identity_valid)
next
  case (IdentityIdentity \<Gamma> \<sigma>)
  show ?case
    by (rule classic_identity_identity_valid)
next
  case (AbsorbDisjForall \<Gamma> \<sigma>)
  show ?case
    by (rule classic_absorb_disj_forall_valid)
next
  case (DistDisjForall \<Gamma> \<sigma>)
  show ?case
    by (rule classic_dist_disj_forall_valid)
next
  case (AbsorbConjExists \<Gamma> \<sigma>)
  show ?case
    by (rule classic_absorb_conj_exists_valid)
next
  case (DistConjExists \<Gamma> \<sigma>)
  show ?case
    by (rule classic_dist_conj_exists_valid)
next
  case (MP \<Gamma> A B)
  show ?case
    by (rule valid_MP[OF MP.IH(1) MP.IH(2)])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case
    by (rule H_Gen_valid[OF Gen.hyps(1) Gen.hyps(2) Gen.IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case
    by (rule H_Inst_valid[OF Inst.hyps(1) Inst.hyps(2) Inst.IH])
qed

end

locale propositional_equivalence_structure = classicist_structure +
  assumes prop_extensionality:
    "x \<in> D Prop \<Longrightarrow> y \<in> D Prop \<Longrightarrow> holds x = holds y \<Longrightarrow>
      eq_den Prop x y"
begin

lemma CE_PropEquivalence_valid:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "valid_in_context \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
  shows "valid_in_context \<Gamma> (Eq Prop A B)"
proof -
  have formula_type: "\<Gamma> \<turnstile> Eq Prop A B : Prop"
    using assms(1,2) by auto
  have "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow> holds (eval \<rho> (Eq Prop A B))"
  proof (intro allI impI)
    fix \<rho>
    assume env: "env_typed \<Gamma> \<rho>"
    have A_den: "eval \<rho> A \<in> D Prop"
      using assms(1) env by (rule eval_type)
    have B_den: "eval \<rho> B \<in> D Prop"
      using assms(2) env by (rule eval_type)
    have iff_holds: "holds (eval \<rho> (A \<longleftrightarrow>\<^sub>o B))"
      using assms(3) env by (rule valid_holds)
    have same_truth: "holds (eval \<rho> A) = holds (eval \<rho> B)"
      using iff_holds by auto
    have "eq_den Prop (eval \<rho> A) (eval \<rho> B)"
      using A_den B_den same_truth by (rule prop_extensionality)
    then show "holds (eval \<rho> (Eq Prop A B))"
      by simp
  qed
  then show ?thesis
    unfolding valid_in_context_def using formula_type by blast
qed

theorem CE_soundness:
  assumes "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "valid_in_context \<Gamma> A"
  using assms
proof (induction rule: CE_proves.induct)
  case (C \<Gamma> A)
  then show ?case
    by (rule C_soundness)
next
  case (PropEquivalence \<Gamma> A B)
  show ?case
    by (rule CE_PropEquivalence_valid
        [OF PropEquivalence.hyps(1) PropEquivalence.hyps(2) PropEquivalence.IH])
next
  case (MP \<Gamma> A B)
  show ?case
    by (rule valid_MP[OF MP.IH(1) MP.IH(2)])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case
    by (rule H_Gen_valid[OF Gen.hyps(1) Gen.hyps(2) Gen.IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case
    by (rule H_Inst_valid[OF Inst.hyps(1) Inst.hyps(2) Inst.IH])
qed

end

locale vector_equivalence_structure = propositional_equivalence_structure +
  assumes vector_extensionality:
    "f \<in> D (arrow_type \<sigma>s Prop) \<Longrightarrow>
      g \<in> D (arrow_type \<sigma>s Prop) \<Longrightarrow>
      (\<And>xs. list_all2 (\<lambda>x \<sigma>. x \<in> D \<sigma>) xs \<sigma>s \<Longrightarrow>
        holds (app_den_vec app_den f xs) = holds (app_den_vec app_den g xs)) \<Longrightarrow>
      eq_den (arrow_type \<sigma>s Prop) f g"
begin

lemma CEV_VectorEquivalence_valid:
  assumes "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop"
    and "\<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop"
    and "valid_in_context (\<sigma>s @ \<Gamma>) (zeta_body \<sigma>s F G)"
  shows "valid_in_context \<Gamma> (Eq (arrow_type \<sigma>s Prop) F G)"
proof -
  have formula_type: "\<Gamma> \<turnstile> Eq (arrow_type \<sigma>s Prop) F G : Prop"
    using assms(1,2) by auto
  have "\<forall>\<rho>. env_typed \<Gamma> \<rho> \<longrightarrow>
      holds (eval \<rho> (Eq (arrow_type \<sigma>s Prop) F G))"
  proof (intro allI impI)
    fix \<rho>
    assume env: "env_typed \<Gamma> \<rho>"
    have F_den: "eval \<rho> F \<in> D (arrow_type \<sigma>s Prop)"
      using assms(1) env by (rule eval_type)
    have G_den: "eval \<rho> G \<in> D (arrow_type \<sigma>s Prop)"
      using assms(2) env by (rule eval_type)
    have agreement: "\<And>xs. list_all2 (\<lambda>x \<sigma>. x \<in> D \<sigma>) xs \<sigma>s \<Longrightarrow>
        holds (app_den_vec app_den (eval \<rho> F) xs) =
        holds (app_den_vec app_den (eval \<rho> G) xs)"
    proof -
      fix xs
      assume xs_type: "list_all2 (\<lambda>x \<sigma>. x \<in> D \<sigma>) xs \<sigma>s"
      have len: "length xs = length \<sigma>s"
        using xs_type by (rule list_all2_lengthD)
      have env_ext: "env_typed (\<sigma>s @ \<Gamma>) (extend_envs xs \<rho>)"
        using env xs_type by (rule env_typed_extends)
      have zeta_holds: "holds (eval (extend_envs xs \<rho>) (zeta_body \<sigma>s F G))"
        using assms(3) env_ext by (rule valid_holds)
      have shift_F:
          "eval (extend_envs xs \<rho>) (shift_by (length \<sigma>s) F) = eval \<rho> F"
        using eval_shift_by_extend_envs[of xs \<rho> F] len by simp
      have shift_G:
          "eval (extend_envs xs \<rho>) (shift_by (length \<sigma>s) G) = eval \<rho> G"
        using eval_shift_by_extend_envs[of xs \<rho> G] len by simp
      have fresh_eval:
          "map (eval (extend_envs xs \<rho>)) (fresh_vars (length \<sigma>s)) = xs"
        using map_eval_fresh_vars_extend_envs[of xs \<rho>] len by simp
      have iff_holds:
          "(holds (app_den_vec app_den (eval \<rho> F) xs) \<longrightarrow>
              holds (app_den_vec app_den (eval \<rho> G) xs)) \<and>
           (holds (app_den_vec app_den (eval \<rho> G) xs) \<longrightarrow>
              holds (app_den_vec app_den (eval \<rho> F) xs))"
        using zeta_holds
        by (simp add: zeta_body_def eval_app_vec shift_F shift_G fresh_eval)
      show "holds (app_den_vec app_den (eval \<rho> F) xs) =
          holds (app_den_vec app_den (eval \<rho> G) xs)"
        using iff_holds by blast
    qed
    have "eq_den (arrow_type \<sigma>s Prop) (eval \<rho> F) (eval \<rho> G)"
      using F_den G_den agreement by (rule vector_extensionality)
    then show "holds (eval \<rho> (Eq (arrow_type \<sigma>s Prop) F G))"
      by simp
  qed
  then show ?thesis
    unfolding valid_in_context_def using formula_type by blast
qed

theorem CEV_soundness:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "valid_in_context \<Gamma> A"
  using assms
proof (induction rule: CEV_proves.induct)
  case (CE \<Gamma> A)
  then show ?case
    by (rule CE_soundness)
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G)
  show ?case
    by (rule CEV_VectorEquivalence_valid
        [OF VectorEquivalence.hyps(1) VectorEquivalence.hyps(2) VectorEquivalence.IH])
next
  case (MP \<Gamma> A B)
  show ?case
    by (rule valid_MP[OF MP.IH(1) MP.IH(2)])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case
    by (rule H_Gen_valid[OF Gen.hyps(1) Gen.hyps(2) Gen.IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case
    by (rule H_Inst_valid[OF Inst.hyps(1) Inst.hyps(2) Inst.IH])
qed

end

end
