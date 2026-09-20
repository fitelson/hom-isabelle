theory Bacon_PP_ZF_Exact_CEV_Soundness
  imports 
    "Goodman_Exact_Legacy_06.Bacon_PP_ZF_Exact_10_1"
begin

section \<open>Structural lemmas for CEV soundness in Bacon's exact appendix model\<close>

abbreviation pp_e_unary_type :: otype where
  "pp_e_unary_type \<equiv> Prop \<rightarrow>\<^sub>o Prop"

fun pp_e_app_values :: "ZF \<Rightarrow> ZF list \<Rightarrow> ZF" where
  "pp_e_app_values f [] = f"
| "pp_e_app_values f (x # xs) =
    pp_e_app_values (f \<acute> x) xs"

lemma pp_e_app_values_closed:
  assumes f:
      "Elem f (pp_e_domain (arrow_type \<sigma>s \<tau>))"
    and xs:
      "list_all2
        (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>)) xs \<sigma>s"
  shows "Elem (pp_e_app_values f xs) (pp_e_domain \<tau>)"
  using f xs
proof (induction \<sigma>s arbitrary: f xs)
  case Nil
  then show ?case by (cases xs) simp_all
next
  case (Cons \<sigma> \<sigma>s)
  then obtain x xs' where
      xs_def: "xs = x # xs'"
    and x: "Elem x (pp_e_domain \<sigma>)"
    and xs':
      "list_all2
        (\<lambda>y \<tau>. Elem y (pp_e_domain \<tau>)) xs' \<sigma>s"
    by (cases xs) auto
  have fx:
      "Elem (f \<acute> x)
        (pp_e_domain (arrow_type \<sigma>s \<tau>))"
  proof -
    have f_arr:
        "Elem f
          (pp_e_domain
            (\<sigma> \<rightarrow>\<^sub>o arrow_type \<sigma>s \<tau>))"
      using Cons.prems(1) by simp
    show ?thesis
      using pp_e_app_closed[OF f_arr x] .
  qed
  show ?case
    unfolding xs_def
    using Cons.IH[OF fx xs'] by simp
qed

lemma pp_e_vector_extensionality:
  assumes f:
      "Elem f (pp_e_domain (arrow_type \<sigma>s Prop))"
    and g:
      "Elem g (pp_e_domain (arrow_type \<sigma>s Prop))"
    and agree:
      "\<And>v xs. prefix w v \<Longrightarrow>
        list_all2
          (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>)) xs \<sigma>s
        \<Longrightarrow>
        pp_e_holds (pp_e_app_values f xs) v =
        pp_e_holds (pp_e_app_values g xs) v"
  shows "pp_e_eqv (arrow_type \<sigma>s Prop) w f g"
  using f g agree
proof (induction \<sigma>s arbitrary: w f g)
  case Nil
  show ?case
    unfolding arrow_type.simps pp_e_eqv.simps
    using Nil.prems(3) by simp
next
  case (Cons \<sigma> \<sigma>s)
  show ?case
    unfolding arrow_type.simps pp_e_eqv.simps
  proof (intro allI impI)
    fix v x y
    assume wv: "prefix w v"
      and x: "Elem x (pp_e_domain \<sigma>)"
      and y: "Elem y (pp_e_domain \<sigma>)"
      and xy: "pp_e_eqv \<sigma> v x y"
    have fx:
        "Elem (f \<acute> x)
          (pp_e_domain (arrow_type \<sigma>s Prop))"
    proof -
      have f_arr:
          "Elem f
            (pp_e_domain
              (\<sigma> \<rightarrow>\<^sub>o arrow_type \<sigma>s Prop))"
        using Cons.prems(1) by simp
      show ?thesis using pp_e_app_closed[OF f_arr x] .
    qed
    have gx:
        "Elem (g \<acute> x)
          (pp_e_domain (arrow_type \<sigma>s Prop))"
    proof -
      have g_arr:
          "Elem g
            (pp_e_domain
              (\<sigma> \<rightarrow>\<^sub>o arrow_type \<sigma>s Prop))"
        using Cons.prems(2) by simp
      show ?thesis using pp_e_app_closed[OF g_arr x] .
    qed
    have gy:
        "Elem (g \<acute> y)
          (pp_e_domain (arrow_type \<sigma>s Prop))"
    proof -
      have g_arr:
          "Elem g
            (pp_e_domain
              (\<sigma> \<rightarrow>\<^sub>o arrow_type \<sigma>s Prop))"
        using Cons.prems(2) by simp
      show ?thesis using pp_e_app_closed[OF g_arr y] .
    qed
    have same_x:
        "pp_e_eqv (arrow_type \<sigma>s Prop) v
          (f \<acute> x) (g \<acute> x)"
    proof (rule Cons.IH[OF fx gx])
      fix u zs
      assume vu: "prefix v u"
        and zs:
          "list_all2
            (\<lambda>a \<alpha>. Elem a (pp_e_domain \<alpha>))
            zs \<sigma>s"
      have wu: "prefix w u"
        using wv vu by (rule prefix_order.trans)
      show "pp_e_holds
          (pp_e_app_values (f \<acute> x) zs) u =
        pp_e_holds
          (pp_e_app_values (g \<acute> x) zs) u"
        using Cons.prems(3)[OF wu, of "x # zs"] x zs
        by simp
    qed
    have gxy:
        "pp_e_eqv (arrow_type \<sigma>s Prop) v
          (g \<acute> x) (g \<acute> y)"
    proof -
      have g_arr:
          "Elem g
            (pp_e_domain
              (\<sigma> \<rightarrow>\<^sub>o arrow_type \<sigma>s Prop))"
        using Cons.prems(2) by simp
      show ?thesis
        using pp_e_app_respects[
          OF pp_e_eqv_reflexive[OF g_arr] x y xy] .
    qed
    show "pp_e_eqv (arrow_type \<sigma>s Prop) v
        (f \<acute> x) (g \<acute> y)"
      using pp_e_eqv_transitive[
        OF fx gx gy same_x gxy] .
  qed
qed

lemma pp_e_eval_shift_by_extend_envs:
  "pp_e_eval C (extend_envs xs \<rho>)
      (shift_by (length xs) M) =
    pp_e_eval C \<rho> M"
proof -
  have env_eq:
      "(\<lambda>n.
        extend_envs xs \<rho>
          (shift_ren (length xs) 0 n)) = \<rho>"
  proof (rule ext)
    fix n
    have "extend_envs xs \<rho>
        (shift_ren (length xs) 0 n) =
        extend_envs xs \<rho> (length xs + n)"
      by (simp add: shift_ren_def add.commute)
    also have "... = \<rho> n"
      by (rule extend_envs_after)
    finally show "extend_envs xs \<rho>
        (shift_ren (length xs) 0 n) = \<rho> n" .
  qed
  show ?thesis
    unfolding shift_by_def
    using pp_e_eval_rename[
      of C "extend_envs xs \<rho>"
        "shift_ren (length xs) 0" M]
    by (simp add: env_eq)
qed

lemma pp_e_eval_rename_Suc_extend:
  "pp_e_eval C (extend_env x \<rho>) (rename Suc M) =
    pp_e_eval C \<rho> M"
  using pp_e_eval_shift[of C x \<rho> M]
  unfolding shift_def by simp

lemma pp_e_eval_subst:
  "pp_e_eval C \<rho> (subst s M) =
    pp_e_eval C (\<lambda>n. pp_e_eval C \<rho> (s n)) M"
proof (induction M arbitrary: \<rho> s)
  case (Lam \<sigma> M)
  have env_eq:
      "(\<lambda>n.
        pp_e_eval C (extend_env x \<rho>) (lift_subst s n)) =
        extend_env x
          (\<lambda>n. pp_e_eval C \<rho> (s n))" for x
    by (rule ext)
      (case_tac n;
       simp add: pp_e_eval_rename_Suc_extend)
  show ?case
    using Lam.IH[
      of "extend_env x \<rho>" "lift_subst s" for x]
    by (simp add: env_eq)
next
  case (Forall \<sigma> M)
  have env_eq:
      "(\<lambda>n.
        pp_e_eval C (extend_env x \<rho>) (lift_subst s n)) =
        extend_env x
          (\<lambda>n. pp_e_eval C \<rho> (s n))" for x
    by (rule ext)
      (case_tac n;
       simp add: pp_e_eval_rename_Suc_extend)
  show ?case
    using Forall.IH[
      of "extend_env x \<rho>" "lift_subst s" for x]
    by (simp add: env_eq)
next
  case (Exists \<sigma> M)
  have env_eq:
      "(\<lambda>n.
        pp_e_eval C (extend_env x \<rho>) (lift_subst s n)) =
        extend_env x
          (\<lambda>n. pp_e_eval C \<rho> (s n))" for x
    by (rule ext)
      (case_tac n;
       simp add: pp_e_eval_rename_Suc_extend)
  show ?case
    using Exists.IH[
      of "extend_env x \<rho>" "lift_subst s" for x]
    by (simp add: env_eq)
qed (simp_all add: fun_eq_iff)

lemma pp_e_eval_subst0:
  "pp_e_eval C \<rho> (subst0 T M) =
    pp_e_eval C (extend_env (pp_e_eval C \<rho> T) \<rho>) M"
proof -
  have env_eq:
      "(\<lambda>n.
        pp_e_eval C \<rho> (case_nat T Var n)) =
        extend_env (pp_e_eval C \<rho> T) \<rho>"
    by (rule ext) (case_tac n; simp)
  show ?thesis
    unfolding subst0_def
    using pp_e_eval_subst[
      of C \<rho> "case_nat T Var" M]
    by (simp add: env_eq)
qed

lemma pp_e_eta:
  assumes f:
      "Elem f (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "Lambda (pp_e_domain \<sigma>) (\<lambda>x. f \<acute> x) = f"
proof -
  have f_typed:
      "Elem f (Fun (pp_e_domain \<sigma>) (pp_e_domain \<tau>))"
    using f by (simp add: Sep)
  obtain F where f_rep:
      "f = Lambda (pp_e_domain \<sigma>) F"
    using Elem_Fun_Lambda[OF f_typed] by auto
  show ?thesis
    unfolding f_rep
    by (simp add: Lambda_ext Lambda_app)
qed

context pp_e_constants
begin

definition pp_e_eval_preserving_step ::
    "(oterm \<Rightarrow> oterm \<Rightarrow> bool) \<Rightarrow> bool"
where
  "pp_e_eval_preserving_step R \<longleftrightarrow>
    (\<forall>\<Gamma> M N \<tau> \<rho>.
      R M N \<longrightarrow>
      \<Gamma> \<turnstile> M : \<tau> \<longrightarrow>
      \<Gamma> \<turnstile> N : \<tau> \<longrightarrow>
      pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
      pp_e_eval C \<rho> M = pp_e_eval C \<rho> N)"

lemma pp_e_beta_contract_eval_preserving:
  "pp_e_eval_preserving_step beta_contract"
  unfolding pp_e_eval_preserving_step_def
proof (intro allI impI)
  fix \<Gamma> M N \<tau> \<rho>
  assume beta: "beta_contract M N"
    and M_type: "\<Gamma> \<turnstile> M : \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<tau>"
    and env: "pp_e_env_typed \<Gamma> \<rho>"
  show "pp_e_eval C \<rho> M = pp_e_eval C \<rho> N"
    using beta
  proof cases
    case (beta \<sigma> P Q)
    then have app_type:
        "\<Gamma> \<turnstile> App (Lam \<sigma> P) Q : \<tau>"
      using M_type by simp
    then obtain \<mu> where
        lam_type:
          "\<Gamma> \<turnstile> Lam \<sigma> P : \<mu> \<rightarrow>\<^sub>o \<tau>"
      and Q_type: "\<Gamma> \<turnstile> Q : \<mu>"
      by (auto elim: has_type.cases)
    then have mu: "\<mu> = \<sigma>"
      and body_type: "\<sigma> # \<Gamma> \<turnstile> P : \<tau>"
      by (auto elim: has_type.cases dest: typing_unique)
    then have Q_sigma: "\<Gamma> \<turnstile> Q : \<sigma>"
      using Q_type by simp
    have Q_den:
        "Elem (pp_e_eval C \<rho> Q) (pp_e_domain \<sigma>)"
      using pp_e_eval_type[OF Q_sigma env]
      by (simp add: pp_e_dom_def)
    have "pp_e_eval C \<rho> (App (Lam \<sigma> P) Q) =
        pp_e_eval C
          (extend_env (pp_e_eval C \<rho> Q) \<rho>) P"
      using Q_den by (simp add: Lambda_app)
    also have "... = pp_e_eval C \<rho> (subst0 Q P)"
      using pp_e_eval_subst0[of C \<rho> Q P] by simp
    finally show ?thesis
      using beta by simp
  qed
qed

lemma pp_e_eta_contract_eval_preserving:
  "pp_e_eval_preserving_step eta_contract"
  unfolding pp_e_eval_preserving_step_def
proof (intro allI impI)
  fix \<Gamma> M N \<tau> \<rho>
  assume eta: "eta_contract M N"
    and M_type: "\<Gamma> \<turnstile> M : \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<tau>"
    and env: "pp_e_env_typed \<Gamma> \<rho>"
  obtain \<sigma> F where
      M_def:
        "M = Lam \<sigma> (App (shift F) (Var 0))"
    and N_def: "N = F"
    using eta by cases auto
  then have lam_type:
      "\<Gamma> \<turnstile>
        Lam \<sigma> (App (shift F) (Var 0)) : \<tau>"
    using M_type by simp
  then obtain \<mu> where
      tau: "\<tau> = \<sigma> \<rightarrow>\<^sub>o \<mu>"
    by (auto elim: has_type.cases)
  have F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<mu>"
    using N_type N_def tau by simp
  have F_den:
      "Elem (pp_e_eval C \<rho> F)
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<mu>))"
    using pp_e_eval_type[OF F_type env]
    by (simp add: pp_e_dom_def)
  have "pp_e_eval C \<rho>
      (Lam \<sigma> (App (shift F) (Var 0))) =
      Lambda (pp_e_domain \<sigma>)
        (\<lambda>x. pp_e_eval C \<rho> F \<acute> x)"
    by (simp add: pp_e_eval_shift)
  also have "... = pp_e_eval C \<rho> F"
    using pp_e_eta[OF F_den] .
  finally show "pp_e_eval C \<rho> M = pp_e_eval C \<rho> N"
    using M_def N_def by simp
qed

end

lemma pp_e_eval_app_vec:
  "pp_e_eval C \<rho> (app_vec F As) =
    pp_e_app_values (pp_e_eval C \<rho> F)
      (map (pp_e_eval C \<rho>) As)"
  by (induction As arbitrary: F) simp_all

lemma pp_e_map_eval_fresh_vars_extend_envs:
  "map (pp_e_eval C (extend_envs xs \<rho>))
      (fresh_vars (length xs)) = xs"
  unfolding fresh_vars_def
  by (rule nth_equalityI)
    (simp_all add: extend_envs_nth_less)

lemma pp_e_list_env_append:
  "pp_e_list_env (xs @ env) =
    extend_envs xs (pp_e_list_env env)"
  by (induction xs)
    (simp_all add: pp_e_list_env_Cons)

lemma pp_e_env_typed_extends:
  assumes env: "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>)) xs \<sigma>s"
  shows "pp_e_env_typed (\<sigma>s @ \<Gamma>)
    (extend_envs xs \<rho>)"
  using env xs
proof (induction xs arbitrary: \<sigma>s \<Gamma> \<rho>)
  case Nil
  then show ?case by (cases \<sigma>s) auto
next
  case (Cons x xs)
  then obtain \<sigma> \<sigma>s' where
      sigma: "\<sigma>s = \<sigma> # \<sigma>s'"
    and x: "Elem x (pp_e_domain \<sigma>)"
    and xs:
      "list_all2
        (\<lambda>y \<tau>. Elem y (pp_e_domain \<tau>)) xs \<sigma>s'"
    by (cases \<sigma>s) auto
  have tail:
      "pp_e_env_typed (\<sigma>s' @ \<Gamma>)
        (extend_envs xs \<rho>)"
    using Cons.IH[OF Cons.prems(1) xs] .
  have "pp_e_env_typed
      (\<sigma> # \<sigma>s' @ \<Gamma>)
      (extend_env x (extend_envs xs \<rho>))"
    using pp_e_env_typed_extend[OF tail x] .
  then show ?case
    by (simp add: sigma)
qed

context pp_e_constants
begin

lemma pp_e_compatible_step_eval:
  assumes step: "compatible_step R M N"
    and preserving: "pp_e_eval_preserving_step R"
    and M_type: "\<Gamma> \<turnstile> M : \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<tau>"
    and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_eval C \<rho> M = pp_e_eval C \<rho> N"
  using step M_type N_type env
proof (induction arbitrary: \<Gamma> \<tau> \<rho>
    rule: compatible_step.induct)
  case (root M N)
  then show ?case
    using preserving
    unfolding pp_e_eval_preserving_step_def by blast
next
  case (App_left M M' N)
  then obtain \<sigma> where
      M_type: "\<Gamma> \<turnstile> M : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    by (auto elim: has_type.cases)
  moreover obtain \<sigma>' where
      M'_type: "\<Gamma> \<turnstile> M' : \<sigma>' \<rightarrow>\<^sub>o \<tau>"
    and N_type': "\<Gamma> \<turnstile> N : \<sigma>'"
    using App_left.prems(2)
    by (auto elim: has_type.cases)
  ultimately have "\<sigma>' = \<sigma>"
    using typing_unique by blast
  then have "pp_e_eval C \<rho> M = pp_e_eval C \<rho> M'"
    using App_left.IH[
      OF M_type _ App_left.prems(3)] M'_type by simp
  then show ?case by simp
next
  case (App_right N N' M)
  then obtain \<sigma> where
      M_type: "\<Gamma> \<turnstile> M : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    by (auto elim: has_type.cases)
  moreover obtain \<sigma>' where
      M_type': "\<Gamma> \<turnstile> M : \<sigma>' \<rightarrow>\<^sub>o \<tau>"
    and N'_type: "\<Gamma> \<turnstile> N' : \<sigma>'"
    using App_right.prems(2)
    by (auto elim: has_type.cases)
  ultimately have "\<sigma>' = \<sigma>"
    using typing_unique by blast
  then have "pp_e_eval C \<rho> N = pp_e_eval C \<rho> N'"
    using App_right.IH[
      OF N_type _ App_right.prems(3)] N'_type by simp
  then show ?case by simp
next
  case (Lam_body M M' \<sigma>)
  then obtain \<mu> where
      tau: "\<tau> = \<sigma> \<rightarrow>\<^sub>o \<mu>"
    and M_type: "\<sigma> # \<Gamma> \<turnstile> M : \<mu>"
    by (auto elim: has_type.cases)
  moreover obtain \<mu>' where
      tau': "\<tau> = \<sigma> \<rightarrow>\<^sub>o \<mu>'"
    and M'_type: "\<sigma> # \<Gamma> \<turnstile> M' : \<mu>'"
    using Lam_body.prems(2)
    by (auto elim: has_type.cases)
  ultimately have "\<mu>' = \<mu>" by simp
  show ?case
    unfolding pp_e_eval.simps Lambda_ext
  proof (intro conjI allI impI)
    show "pp_e_domain \<sigma> = pp_e_domain \<sigma>" by simp
  next
    fix x
    assume x: "Elem x (pp_e_domain \<sigma>)"
    have extended:
        "pp_e_env_typed (\<sigma> # \<Gamma>)
          (extend_env x \<rho>)"
      using pp_e_env_typed_extend[
        OF Lam_body.prems(3) x] .
    show "pp_e_eval C (extend_env x \<rho>) M =
        pp_e_eval C (extend_env x \<rho>) M'"
      using Lam_body.IH[
        OF M_type _ extended] M'_type \<open>\<mu>' = \<mu>\<close>
      by simp
  qed
next
  case (Eq_left M M' \<sigma> N)
  then have M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and M'_type: "\<Gamma> \<turnstile> M' : \<sigma>"
    by (auto elim: has_type.cases)
  have "pp_e_eval C \<rho> M = pp_e_eval C \<rho> M'"
    using Eq_left.IH[
      OF M_type M'_type Eq_left.prems(3)] .
  then show ?case by simp
next
  case (Eq_right N N' \<sigma> M)
  then have N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and N'_type: "\<Gamma> \<turnstile> N' : \<sigma>"
    by (auto elim: has_type.cases)
  have "pp_e_eval C \<rho> N = pp_e_eval C \<rho> N'"
    using Eq_right.IH[
      OF N_type N'_type Eq_right.prems(3)] .
  then show ?case by simp
next
  case (Neg_body A A')
  then have A_type: "\<Gamma> \<turnstile> A : Prop"
    and A'_type: "\<Gamma> \<turnstile> A' : Prop"
    by (auto elim: has_type.cases)
  have "pp_e_eval C \<rho> A = pp_e_eval C \<rho> A'"
    using Neg_body.IH[
      OF A_type A'_type Neg_body.prems(3)] .
  then show ?case by simp
next
  case (Conj_left A A' B)
  then have A_type: "\<Gamma> \<turnstile> A : Prop"
    and A'_type: "\<Gamma> \<turnstile> A' : Prop"
    by (auto elim: has_type.cases)
  have "pp_e_eval C \<rho> A = pp_e_eval C \<rho> A'"
    using Conj_left.IH[
      OF A_type A'_type Conj_left.prems(3)] .
  then show ?case by simp
next
  case (Conj_right B B' A)
  then have B_type: "\<Gamma> \<turnstile> B : Prop"
    and B'_type: "\<Gamma> \<turnstile> B' : Prop"
    by (auto elim: has_type.cases)
  have "pp_e_eval C \<rho> B = pp_e_eval C \<rho> B'"
    using Conj_right.IH[
      OF B_type B'_type Conj_right.prems(3)] .
  then show ?case by simp
next
  case (Disj_left A A' B)
  then have A_type: "\<Gamma> \<turnstile> A : Prop"
    and A'_type: "\<Gamma> \<turnstile> A' : Prop"
    by (auto elim: has_type.cases)
  have "pp_e_eval C \<rho> A = pp_e_eval C \<rho> A'"
    using Disj_left.IH[
      OF A_type A'_type Disj_left.prems(3)] .
  then show ?case by simp
next
  case (Disj_right B B' A)
  then have B_type: "\<Gamma> \<turnstile> B : Prop"
    and B'_type: "\<Gamma> \<turnstile> B' : Prop"
    by (auto elim: has_type.cases)
  have "pp_e_eval C \<rho> B = pp_e_eval C \<rho> B'"
    using Disj_right.IH[
      OF B_type B'_type Disj_right.prems(3)] .
  then show ?case by simp
next
  case (Imp_left A A' B)
  then have A_type: "\<Gamma> \<turnstile> A : Prop"
    and A'_type: "\<Gamma> \<turnstile> A' : Prop"
    by (auto elim: has_type.cases)
  have "pp_e_eval C \<rho> A = pp_e_eval C \<rho> A'"
    using Imp_left.IH[
      OF A_type A'_type Imp_left.prems(3)] .
  then show ?case by simp
next
  case (Imp_right B B' A)
  then have B_type: "\<Gamma> \<turnstile> B : Prop"
    and B'_type: "\<Gamma> \<turnstile> B' : Prop"
    by (auto elim: has_type.cases)
  have "pp_e_eval C \<rho> B = pp_e_eval C \<rho> B'"
    using Imp_right.IH[
      OF B_type B'_type Imp_right.prems(3)] .
  then show ?case by simp
next
  case (Forall_body A A' \<sigma>)
  then have A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and A'_type: "\<sigma> # \<Gamma> \<turnstile> A' : Prop"
    by (auto elim: has_type.cases)
  have body:
      "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
        pp_e_eval C (extend_env x \<rho>) A =
        pp_e_eval C (extend_env x \<rho>) A'"
  proof -
    fix x
    assume x: "Elem x (pp_e_domain \<sigma>)"
    have extended:
        "pp_e_env_typed (\<sigma> # \<Gamma>)
          (extend_env x \<rho>)"
      using pp_e_env_typed_extend[
        OF Forall_body.prems(3) x] .
    show "pp_e_eval C (extend_env x \<rho>) A =
        pp_e_eval C (extend_env x \<rho>) A'"
      using Forall_body.IH[
        OF A_type A'_type extended] .
  qed
  show ?case
    using body by (simp add: fun_eq_iff)
next
  case (Exists_body A A' \<sigma>)
  then have A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and A'_type: "\<sigma> # \<Gamma> \<turnstile> A' : Prop"
    by (auto elim: has_type.cases)
  have body:
      "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
        pp_e_eval C (extend_env x \<rho>) A =
        pp_e_eval C (extend_env x \<rho>) A'"
  proof -
    fix x
    assume x: "Elem x (pp_e_domain \<sigma>)"
    have extended:
        "pp_e_env_typed (\<sigma> # \<Gamma>)
          (extend_env x \<rho>)"
      using pp_e_env_typed_extend[
        OF Exists_body.prems(3) x] .
    show "pp_e_eval C (extend_env x \<rho>) A =
        pp_e_eval C (extend_env x \<rho>) A'"
      using Exists_body.IH[
        OF A_type A'_type extended] .
  qed
  have pred_eq:
      "(\<lambda>w. \<exists>x.
          Elem x (pp_e_domain \<sigma>) \<and>
          pp_e_holds
            (pp_e_eval C (extend_env x \<rho>) A) w) =
       (\<lambda>w. \<exists>x.
          Elem x (pp_e_domain \<sigma>) \<and>
          pp_e_holds
            (pp_e_eval C (extend_env x \<rho>) A') w)"
    using body by (auto simp: fun_eq_iff)
  show ?case using pred_eq by simp
qed

lemma pp_e_beta_compatible_eval:
  assumes "compatible_step beta_contract M N"
    and "\<Gamma> \<turnstile> M : \<tau>"
    and "\<Gamma> \<turnstile> N : \<tau>"
    and "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_eval C \<rho> M = pp_e_eval C \<rho> N"
  by (rule pp_e_compatible_step_eval[
      OF assms(1) pp_e_beta_contract_eval_preserving
        assms(2) assms(3) assms(4)])

lemma pp_e_eta_compatible_eval:
  assumes "compatible_step eta_contract M N"
    and "\<Gamma> \<turnstile> M : \<tau>"
    and "\<Gamma> \<turnstile> N : \<tau>"
    and "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_eval C \<rho> M = pp_e_eval C \<rho> N"
  by (rule pp_e_compatible_step_eval[
      OF assms(1) pp_e_eta_contract_eval_preserving
        assms(2) assms(3) assms(4)])

definition pp_e_valid :: "ctx \<Rightarrow> oterm \<Rightarrow> bool"
where
  "pp_e_valid \<Gamma> A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
      pp_e_holds (pp_e_eval C \<rho> A) w)"

lemma pp_e_valid_formula:
  "pp_e_valid \<Gamma> A \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  unfolding pp_e_valid_def by blast

lemma pp_e_valid_holds:
  assumes "pp_e_valid \<Gamma> A"
    and "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval C \<rho> A) w"
  using assms unfolding pp_e_valid_def by blast

lemma pp_e_valid_implies_gvalid:
  assumes "pp_e_valid \<Gamma> A"
  shows "ExactBaconHenkin.gvalid \<Gamma> A"
proof (rule ExactBaconHenkin.gvalidI)
  fix env w
  assume ok: "env_ok (map pp_e_dom \<Gamma>) env"
  have typed:
      "pp_e_env_typed \<Gamma> (pp_e_list_env env)"
    using env_ok_implies_pp_e_env_typed[OF ok] .
  show "pp_e_holds (pp_e_den A env) w"
    unfolding pp_e_den_def
    using pp_e_valid_holds[OF assms typed] .
qed

lemma pp_e_holds_prop_eval:
  "pp_e_holds (pp_e_eval C \<rho> A) w =
    prop_eval
      (\<lambda>B. pp_e_holds (pp_e_eval C \<rho> B) w) A"
  by (induction A arbitrary: \<rho>) simp_all

lemma pp_e_prop_tautology_valid:
  assumes taut: "prop_tautology \<Gamma> A"
  shows "pp_e_valid \<Gamma> A"
proof -
  have typed: "\<Gamma> \<turnstile> A : Prop"
    using taut unfolding prop_tautology_def by blast
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds (pp_e_eval C \<rho> A) w"
  proof -
    fix \<rho> w
    assume "pp_e_env_typed \<Gamma> \<rho>"
    have "\<forall>v. prop_eval v A"
      using taut unfolding prop_tautology_def by blast
    then have "prop_eval
        (\<lambda>B. pp_e_holds (pp_e_eval C \<rho> B) w) A"
      by blast
    then show "pp_e_holds (pp_e_eval C \<rho> A) w"
      using pp_e_holds_prop_eval[of \<rho> A w] by simp
  qed
  show ?thesis
    unfolding pp_e_valid_def using typed holds by blast
qed

lemma pp_e_valid_MP:
  assumes A: "pp_e_valid \<Gamma> A"
    and imp: "pp_e_valid \<Gamma> (Imp A B)"
  shows "pp_e_valid \<Gamma> B"
proof -
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using pp_e_valid_formula[OF imp]
    by (auto elim: has_type.cases)
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds (pp_e_eval C \<rho> B) w"
  proof -
    fix \<rho> w
    assume env: "pp_e_env_typed \<Gamma> \<rho>"
    have Ah: "pp_e_holds (pp_e_eval C \<rho> A) w"
      using pp_e_valid_holds[OF A env] .
    have Ih:
        "pp_e_holds (pp_e_eval C \<rho> (Imp A B)) w"
      using pp_e_valid_holds[OF imp env] .
    show "pp_e_holds (pp_e_eval C \<rho> B) w"
      using Ah Ih by simp
  qed
  show ?thesis
    unfolding pp_e_valid_def using B_type holds by blast
qed

lemma pp_e_H_UI_valid:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and T: "\<Gamma> \<turnstile> T : \<sigma>"
  shows "pp_e_valid \<Gamma>
    (Imp (Forall \<sigma> A) (subst0 T A))"
proof -
  have typed:
      "\<Gamma> \<turnstile>
        Imp (Forall \<sigma> A) (subst0 T A) : Prop"
    using A T subst0_preserves_typing by auto
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds
          (pp_e_eval C \<rho>
            (Imp (Forall \<sigma> A) (subst0 T A))) w"
  proof -
    fix \<rho> w
    assume env: "pp_e_env_typed \<Gamma> \<rho>"
    have T_den:
        "Elem (pp_e_eval C \<rho> T) (pp_e_domain \<sigma>)"
      using pp_e_eval_type[OF T env]
      by (simp add: pp_e_dom_def)
    show "pp_e_holds
        (pp_e_eval C \<rho>
          (Imp (Forall \<sigma> A) (subst0 T A))) w"
      using T_den pp_e_eval_subst0[of C \<rho> T A]
      by simp
  qed
  show ?thesis
    unfolding pp_e_valid_def using typed holds by blast
qed

lemma pp_e_H_EG_valid:
  assumes A: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and T: "\<Gamma> \<turnstile> T : \<sigma>"
  shows "pp_e_valid \<Gamma>
    (Imp (subst0 T A) (Exists \<sigma> A))"
proof -
  have typed:
      "\<Gamma> \<turnstile>
        Imp (subst0 T A) (Exists \<sigma> A) : Prop"
    using A T subst0_preserves_typing by auto
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds
          (pp_e_eval C \<rho>
            (Imp (subst0 T A) (Exists \<sigma> A))) w"
  proof -
    fix \<rho> w
    assume env: "pp_e_env_typed \<Gamma> \<rho>"
    have T_den:
        "Elem (pp_e_eval C \<rho> T) (pp_e_domain \<sigma>)"
      using pp_e_eval_type[OF T env]
      by (simp add: pp_e_dom_def)
    have subst:
        "pp_e_eval C \<rho> (subst0 T A) =
          pp_e_eval C
            (extend_env (pp_e_eval C \<rho> T) \<rho>) A"
      using pp_e_eval_subst0[of C \<rho> T A] .
    show "pp_e_holds
        (pp_e_eval C \<rho>
          (Imp (subst0 T A) (Exists \<sigma> A))) w"
      using T_den subst by simp blast
  qed
  show ?thesis
    unfolding pp_e_valid_def using typed holds by blast
qed

lemma pp_e_H_Ref_valid:
  assumes M: "\<Gamma> \<turnstile> M : \<sigma>"
  shows "pp_e_valid \<Gamma> (Eq \<sigma> M M)"
proof -
  have typed: "\<Gamma> \<turnstile> Eq \<sigma> M M : Prop"
    using M by auto
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds (pp_e_eval C \<rho> (Eq \<sigma> M M)) w"
  proof -
    fix \<rho> w
    assume env: "pp_e_env_typed \<Gamma> \<rho>"
    have den:
        "Elem (pp_e_eval C \<rho> M) (pp_e_domain \<sigma>)"
      using pp_e_eval_type[OF M env]
      by (simp add: pp_e_dom_def)
    show "pp_e_holds
        (pp_e_eval C \<rho> (Eq \<sigma> M M)) w"
      using pp_e_eqv_reflexive[OF den] by simp
  qed
  show ?thesis
    unfolding pp_e_valid_def using typed holds by blast
qed

lemma pp_e_H_LL_valid:
  assumes A: "\<Gamma> \<turnstile> A : \<sigma>"
    and B: "\<Gamma> \<turnstile> B : \<sigma>"
    and F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop"
  shows "pp_e_valid \<Gamma>
    (Imp (Eq \<sigma> A B) (Imp (App F A) (App F B)))"
proof -
  have typed:
      "\<Gamma> \<turnstile>
        Imp (Eq \<sigma> A B) (Imp (App F A) (App F B)) :
        Prop"
    using A B F by auto
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds
          (pp_e_eval C \<rho>
            (Imp (Eq \<sigma> A B)
              (Imp (App F A) (App F B)))) w"
  proof -
    fix \<rho> w
    assume env: "pp_e_env_typed \<Gamma> \<rho>"
    have Ad:
        "Elem (pp_e_eval C \<rho> A) (pp_e_domain \<sigma>)"
      using pp_e_eval_type[OF A env]
      by (simp add: pp_e_dom_def)
    have Bd:
        "Elem (pp_e_eval C \<rho> B) (pp_e_domain \<sigma>)"
      using pp_e_eval_type[OF B env]
      by (simp add: pp_e_dom_def)
    have Fd:
        "Elem (pp_e_eval C \<rho> F)
          (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      using pp_e_eval_type[OF F env]
      by (simp add: pp_e_dom_def)
    show "pp_e_holds
        (pp_e_eval C \<rho>
          (Imp (Eq \<sigma> A B)
            (Imp (App F A) (App F B)))) w"
      using pp_e_app_respects[
        OF pp_e_eqv_reflexive[OF Fd] Ad Bd]
      by simp
  qed
  show ?thesis
    unfolding pp_e_valid_def using typed holds by blast
qed

lemma pp_e_H_Beta_valid:
  assumes A: "\<Gamma> \<turnstile> A : Prop"
    and B: "\<Gamma> \<turnstile> B : Prop"
    and step: "compatible_step beta_contract A B"
  shows "pp_e_valid \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have typed: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using A B by auto
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds
          (pp_e_eval C \<rho> (A \<longleftrightarrow>\<^sub>o B)) w"
  proof -
    fix \<rho> w
    assume env: "pp_e_env_typed \<Gamma> \<rho>"
    have "pp_e_eval C \<rho> A = pp_e_eval C \<rho> B"
      using pp_e_beta_compatible_eval[
        OF step A B env] .
    then show "pp_e_holds
        (pp_e_eval C \<rho> (A \<longleftrightarrow>\<^sub>o B)) w"
      by simp
  qed
  show ?thesis
    unfolding pp_e_valid_def using typed holds by blast
qed

lemma pp_e_H_Eta_valid:
  assumes A: "\<Gamma> \<turnstile> A : Prop"
    and B: "\<Gamma> \<turnstile> B : Prop"
    and step: "compatible_step eta_contract A B"
  shows "pp_e_valid \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have typed: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using A B by auto
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds
          (pp_e_eval C \<rho> (A \<longleftrightarrow>\<^sub>o B)) w"
  proof -
    fix \<rho> w
    assume env: "pp_e_env_typed \<Gamma> \<rho>"
    have "pp_e_eval C \<rho> A = pp_e_eval C \<rho> B"
      using pp_e_eta_compatible_eval[
        OF step A B env] .
    then show "pp_e_holds
        (pp_e_eval C \<rho> (A \<longleftrightarrow>\<^sub>o B)) w"
      by simp
  qed
  show ?thesis
    unfolding pp_e_valid_def using typed holds by blast
qed

lemma pp_e_H_Gen_valid:
  assumes P: "\<Gamma> \<turnstile> P : Prop"
    and Q: "\<sigma> # \<Gamma> \<turnstile> Q : Prop"
    and premise:
      "pp_e_valid (\<sigma> # \<Gamma>) (Imp (shift P) Q)"
  shows "pp_e_valid \<Gamma> (Imp P (Forall \<sigma> Q))"
proof -
  have typed: "\<Gamma> \<turnstile> Imp P (Forall \<sigma> Q) : Prop"
    using P Q by auto
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds
          (pp_e_eval C \<rho> (Imp P (Forall \<sigma> Q))) w"
  proof -
    fix \<rho> w
    assume env: "pp_e_env_typed \<Gamma> \<rho>"
    show "pp_e_holds
        (pp_e_eval C \<rho> (Imp P (Forall \<sigma> Q))) w"
    proof (simp, intro impI allI impI)
      assume Ph: "pp_e_holds (pp_e_eval C \<rho> P) w"
      fix x
      assume x: "Elem x (pp_e_domain \<sigma>)"
      have ext:
          "pp_e_env_typed (\<sigma> # \<Gamma>)
            (extend_env x \<rho>)"
        using pp_e_env_typed_extend[OF env x] .
      have ih:
          "pp_e_holds
            (pp_e_eval C (extend_env x \<rho>)
              (Imp (shift P) Q)) w"
        using pp_e_valid_holds[OF premise ext] .
      show "pp_e_holds
          (pp_e_eval C (extend_env x \<rho>) Q) w"
        using ih Ph by (simp add: pp_e_eval_shift)
    qed
  qed
  show ?thesis
    unfolding pp_e_valid_def using typed holds by blast
qed

lemma pp_e_H_Inst_valid:
  assumes P: "\<sigma> # \<Gamma> \<turnstile> P : Prop"
    and Q: "\<Gamma> \<turnstile> Q : Prop"
    and premise:
      "pp_e_valid (\<sigma> # \<Gamma>) (Imp P (shift Q))"
  shows "pp_e_valid \<Gamma> (Imp (Exists \<sigma> P) Q)"
proof -
  have typed: "\<Gamma> \<turnstile> Imp (Exists \<sigma> P) Q : Prop"
    using P Q by auto
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds
          (pp_e_eval C \<rho> (Imp (Exists \<sigma> P) Q)) w"
  proof -
    fix \<rho> w
    assume env: "pp_e_env_typed \<Gamma> \<rho>"
    show "pp_e_holds
        (pp_e_eval C \<rho> (Imp (Exists \<sigma> P) Q)) w"
    proof (simp, intro impI)
      assume "\<exists>x.
        Elem x (pp_e_domain \<sigma>) \<and>
        pp_e_holds (pp_e_eval C (extend_env x \<rho>) P) w"
      then obtain x where x: "Elem x (pp_e_domain \<sigma>)"
        and Ph:
          "pp_e_holds
            (pp_e_eval C (extend_env x \<rho>) P) w"
        by blast
      have ext:
          "pp_e_env_typed (\<sigma> # \<Gamma>)
            (extend_env x \<rho>)"
        using pp_e_env_typed_extend[OF env x] .
      have ih:
          "pp_e_holds
            (pp_e_eval C (extend_env x \<rho>)
              (Imp P (shift Q))) w"
        using pp_e_valid_holds[OF premise ext] .
      show "pp_e_holds (pp_e_eval C \<rho> Q) w"
        using ih Ph by (simp add: pp_e_eval_shift)
    qed
  qed
  show ?thesis
    unfolding pp_e_valid_def using typed holds by blast
qed

lemma pp_e_H_IndividualExistence_valid:
  "pp_e_valid \<Gamma> (Exists Ind (Eq Ind (Var 0) (Var 0)))"
proof -
  have typed:
      "\<Gamma> \<turnstile> Exists Ind (Eq Ind (Var 0) (Var 0)) : Prop"
    by (rule has_type.Exists, rule has_type.Eq; simp)
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds
          (pp_e_eval C \<rho>
            (Exists Ind (Eq Ind (Var 0) (Var 0)))) w"
  proof -
    fix \<rho> w
    assume "pp_e_env_typed \<Gamma> \<rho>"
    have empty: "Elem Empty (pp_e_domain Ind)"
      by (simp add: Singleton)
    show "pp_e_holds
        (pp_e_eval C \<rho>
          (Exists Ind (Eq Ind (Var 0) (Var 0)))) w"
      using empty by (simp; blast)
  qed
  show ?thesis
    unfolding pp_e_valid_def using typed holds by blast
qed

theorem pp_e_H_sound:
  assumes "\<Gamma> \<turnstile>\<^sub>H A"
  shows "pp_e_valid \<Gamma> A"
  using assms
proof (induction rule: H_proves.induct)
  case (PC \<Gamma> A)
  then show ?case by (rule pp_e_prop_tautology_valid)
next
  case (IndividualExistence \<Gamma>)
  show ?case by (rule pp_e_H_IndividualExistence_valid)
next
  case (UI \<sigma> \<Gamma> A T)
  then show ?case by (rule pp_e_H_UI_valid)
next
  case (EG \<sigma> \<Gamma> A T)
  then show ?case by (rule pp_e_H_EG_valid)
next
  case (Ref \<Gamma> M \<sigma>)
  then show ?case by (rule pp_e_H_Ref_valid)
next
  case (LL \<Gamma> A \<sigma> B F)
  then show ?case by (rule pp_e_H_LL_valid)
next
  case (Beta \<Gamma> A B)
  then show ?case by (rule pp_e_H_Beta_valid)
next
  case (Eta \<Gamma> A B)
  then show ?case by (rule pp_e_H_Eta_valid)
next
  case (MP \<Gamma> A B)
  show ?case by (rule pp_e_valid_MP[OF MP.IH(1) MP.IH(2)])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case
    by (rule pp_e_H_Gen_valid[
      OF Gen.hyps(1) Gen.hyps(2) Gen.IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case
    by (rule pp_e_H_Inst_valid[
      OF Inst.hyps(1) Inst.hyps(2) Inst.IH])
qed

lemma pp_e_vector_equation_valid:
  assumes F_type:
      "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop"
    and G_type:
      "\<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop"
    and agree:
      "\<And>\<rho> v xs.
        pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        list_all2
          (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>))
          xs \<sigma>s \<Longrightarrow>
        pp_e_holds
          (pp_e_app_values (pp_e_eval C \<rho> F) xs) v =
        pp_e_holds
          (pp_e_app_values (pp_e_eval C \<rho> G) xs) v"
  shows "pp_e_valid \<Gamma>
    (Eq (arrow_type \<sigma>s Prop) F G)"
proof -
  have typed:
      "\<Gamma> \<turnstile> Eq (arrow_type \<sigma>s Prop) F G : Prop"
    using F_type G_type by auto
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds
          (pp_e_eval C \<rho>
            (Eq (arrow_type \<sigma>s Prop) F G)) w"
  proof -
    fix \<rho> w
    assume env: "pp_e_env_typed \<Gamma> \<rho>"
    have F_den:
        "Elem (pp_e_eval C \<rho> F)
          (pp_e_domain (arrow_type \<sigma>s Prop))"
      using pp_e_eval_type[OF F_type env]
      by (simp add: pp_e_dom_def)
    have G_den:
        "Elem (pp_e_eval C \<rho> G)
          (pp_e_domain (arrow_type \<sigma>s Prop))"
      using pp_e_eval_type[OF G_type env]
      by (simp add: pp_e_dom_def)
    have relation:
        "pp_e_eqv (arrow_type \<sigma>s Prop) w
          (pp_e_eval C \<rho> F) (pp_e_eval C \<rho> G)"
      by (rule pp_e_vector_extensionality[OF F_den G_den])
        (use env agree in blast)
    show "pp_e_holds
        (pp_e_eval C \<rho>
          (Eq (arrow_type \<sigma>s Prop) F G)) w"
      using relation by simp
  qed
  show ?thesis
    unfolding pp_e_valid_def using typed holds by blast
qed

lemma pp_e_bool_comm_conj_valid:
  "pp_e_valid \<Gamma> bool_comm_conj"
  unfolding bool_comm_conj_def prop_bin_ty_def
proof (rule pp_e_vector_equation_valid[
    where \<sigma>s="[Prop, Prop]", simplified])
  fix \<rho> v xs
  assume "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>))
        xs [Prop, Prop]"
  then obtain x y where "xs = [x, y]"
    and x: "Elem x (pp_e_domain Prop)"
    and y: "Elem y (pp_e_domain Prop)"
    by (auto simp: list_all2_Cons2)
  then show "pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop (Conj (Var 1) (Var 0)))))
        xs) v =
    pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop (Conj (Var 0) (Var 1)))))
        xs) v"
    using x y by (simp add: Lambda_app; blast)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop (Conj (Var 1) (Var 0))) :
      Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop (Conj (Var 0) (Var 1))) :
      Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
qed

lemma pp_e_bool_comm_disj_valid:
  "pp_e_valid \<Gamma> bool_comm_disj"
  unfolding bool_comm_disj_def prop_bin_ty_def
proof (rule pp_e_vector_equation_valid[
    where \<sigma>s="[Prop, Prop]", simplified])
  fix \<rho> v xs
  assume "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>))
        xs [Prop, Prop]"
  then obtain x y where "xs = [x, y]"
    and x: "Elem x (pp_e_domain Prop)"
    and y: "Elem y (pp_e_domain Prop)"
    by (auto simp: list_all2_Cons2)
  then show "pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop (Disj (Var 1) (Var 0)))))
        xs) v =
    pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop (Disj (Var 0) (Var 1)))))
        xs) v"
    using x y by (simp add: Lambda_app; blast)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop (Disj (Var 1) (Var 0))) :
      Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop (Disj (Var 0) (Var 1))) :
      Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
qed

lemma pp_e_bool_dist_conj_disj_valid:
  "pp_e_valid \<Gamma> bool_dist_conj_disj"
  unfolding bool_dist_conj_disj_def
proof (rule pp_e_vector_equation_valid[
    where \<sigma>s="[Prop, Prop, Prop]", simplified])
  fix \<rho> v xs
  assume "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>))
        xs [Prop, Prop, Prop]"
  then obtain x y z where "xs = [x, y, z]"
    and x: "Elem x (pp_e_domain Prop)"
    and y: "Elem y (pp_e_domain Prop)"
    and z: "Elem z (pp_e_domain Prop)"
    by (auto simp: list_all2_Cons2)
  then show "pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop (Lam Prop
            (Conj (Var 2) (Disj (Var 1) (Var 0)))))))
        xs) v =
    pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop (Lam Prop
            (Disj (Conj (Var 2) (Var 1))
              (Conj (Var 2) (Var 0)))))))
        xs) v"
    using x y z by (simp add: Lambda_app; blast)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop (Lam Prop
        (Conj (Var 2) (Disj (Var 1) (Var 0))))) :
      Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop (Lam Prop
        (Disj (Conj (Var 2) (Var 1))
          (Conj (Var 2) (Var 0))))) :
      Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
qed

lemma pp_e_bool_dist_disj_conj_valid:
  "pp_e_valid \<Gamma> bool_dist_disj_conj"
  unfolding bool_dist_disj_conj_def
proof (rule pp_e_vector_equation_valid[
    where \<sigma>s="[Prop, Prop, Prop]", simplified])
  fix \<rho> v xs
  assume "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>))
        xs [Prop, Prop, Prop]"
  then obtain x y z where "xs = [x, y, z]"
    and x: "Elem x (pp_e_domain Prop)"
    and y: "Elem y (pp_e_domain Prop)"
    and z: "Elem z (pp_e_domain Prop)"
    by (auto simp: list_all2_Cons2)
  then show "pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop (Lam Prop
            (Disj (Var 2) (Conj (Var 1) (Var 0)))))))
        xs) v =
    pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop (Lam Prop
            (Conj (Disj (Var 2) (Var 1))
              (Disj (Var 2) (Var 0)))))))
        xs) v"
    using x y z by (simp add: Lambda_app; blast)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop (Lam Prop
        (Disj (Var 2) (Conj (Var 1) (Var 0))))) :
      Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop (Lam Prop
        (Conj (Disj (Var 2) (Var 1))
          (Disj (Var 2) (Var 0))))) :
      Prop \<rightarrow>\<^sub>o Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
qed

lemma pp_e_bool_dissolve_conj_disj_valid:
  "pp_e_valid \<Gamma> bool_dissolve_conj_disj"
  unfolding bool_dissolve_conj_disj_def prop_bin_ty_def
proof (rule pp_e_vector_equation_valid[
    where \<sigma>s="[Prop, Prop]", simplified])
  fix \<rho> v xs
  assume "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>))
        xs [Prop, Prop]"
  then obtain x y where "xs = [x, y]"
    and x: "Elem x (pp_e_domain Prop)"
    and y: "Elem y (pp_e_domain Prop)"
    by (auto simp: list_all2_Cons2)
  then show "pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop
            (Conj (Var 1)
              (Disj (Var 0) (Neg (Var 0)))))))
        xs) v =
    pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop (Var 1)))) xs) v"
    using x y by (simp add: Lambda_app; blast)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop
        (Conj (Var 1) (Disj (Var 0) (Neg (Var 0))))) :
      Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop (Var 1)) :
      Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
qed

lemma pp_e_bool_dissolve_disj_conj_valid:
  "pp_e_valid \<Gamma> bool_dissolve_disj_conj"
  unfolding bool_dissolve_disj_conj_def prop_bin_ty_def
proof (rule pp_e_vector_equation_valid[
    where \<sigma>s="[Prop, Prop]", simplified])
  fix \<rho> v xs
  assume "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>))
        xs [Prop, Prop]"
  then obtain x y where "xs = [x, y]"
    and x: "Elem x (pp_e_domain Prop)"
    and y: "Elem y (pp_e_domain Prop)"
    by (auto simp: list_all2_Cons2)
  then show "pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop
            (Disj (Var 1)
              (Conj (Var 0) (Neg (Var 0)))))))
        xs) v =
    pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop (Var 1)))) xs) v"
    using x y by (simp add: Lambda_app; blast)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop
        (Disj (Var 1) (Conj (Var 0) (Neg (Var 0))))) :
      Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop (Var 1)) :
      Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
qed

lemma pp_e_bool_material_imp_valid:
  "pp_e_valid \<Gamma> bool_material_imp"
  unfolding bool_material_imp_def prop_bin_ty_def
proof (rule pp_e_vector_equation_valid[
    where \<sigma>s="[Prop, Prop]", simplified])
  fix \<rho> v xs
  assume "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>))
        xs [Prop, Prop]"
  then obtain x y where "xs = [x, y]"
    and x: "Elem x (pp_e_domain Prop)"
    and y: "Elem y (pp_e_domain Prop)"
    by (auto simp: list_all2_Cons2)
  then show "pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop (Imp (Var 1) (Var 0)))))
        xs) v =
    pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam Prop (Lam Prop (Disj (Neg (Var 1)) (Var 0)))))
        xs) v"
    using x y by (simp add: Lambda_app)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop (Imp (Var 1) (Var 0))) :
      Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
next
  show "\<Gamma> \<turnstile>
      Lam Prop (Lam Prop (Disj (Neg (Var 1)) (Var 0))) :
      Prop \<rightarrow>\<^sub>o pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
qed

lemma pp_e_boolean_identity_valid:
  assumes "A \<in> set all_boolean_identities"
  shows "pp_e_valid \<Gamma> A"
  using assms
  unfolding all_boolean_identities_def
  using pp_e_bool_comm_conj_valid
    pp_e_bool_comm_disj_valid
    pp_e_bool_dist_conj_disj_valid
    pp_e_bool_dist_disj_conj_valid
    pp_e_bool_dissolve_conj_disj_valid
    pp_e_bool_dissolve_disj_conj_valid
    pp_e_bool_material_imp_valid
  by auto

lemma pp_e_classic_absorb_disj_forall_valid:
  "pp_e_valid \<Gamma> (classic_absorb_disj_forall \<sigma>)"
  unfolding classic_absorb_disj_forall_def pred_ty_def
proof (rule pp_e_vector_equation_valid[
    where \<sigma>s="[\<sigma> \<rightarrow>\<^sub>o Prop, \<sigma>]",
    simplified])
  fix \<rho> v xs
  assume "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<tau>. Elem x (pp_e_domain \<tau>))
        xs [\<sigma> \<rightarrow>\<^sub>o Prop, \<sigma>]"
  then obtain p x where "xs = [p, x]"
    and p:
      "Elem p (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    and x: "Elem x (pp_e_domain \<sigma>)"
    by (auto simp: list_all2_Cons2)
  then show "pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
            (Disj (App (Var 1) (Var 0))
              (Forall \<sigma> (App (Var 2) (Var 0)))))))
        xs) v =
    pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
            (App (Var 1) (Var 0))))) xs) v"
    using p x by (simp add: Lambda_app; blast)
next
  show "\<Gamma> \<turnstile>
      Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
        (Disj (App (Var 1) (Var 0))
          (Forall \<sigma> (App (Var 2) (Var 0))))) :
      (\<sigma> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o
        \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
next
  show "\<Gamma> \<turnstile>
      Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
        (App (Var 1) (Var 0))) :
      (\<sigma> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o
        \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
qed

lemma pp_e_classic_dist_disj_forall_valid:
  "pp_e_valid \<Gamma> (classic_dist_disj_forall \<sigma>)"
  unfolding classic_dist_disj_forall_def pred_ty_def
proof (rule pp_e_vector_equation_valid[
    where \<sigma>s="[\<sigma> \<rightarrow>\<^sub>o Prop, Prop]",
    simplified])
  fix \<rho> v xs
  assume "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<tau>. Elem x (pp_e_domain \<tau>))
        xs [\<sigma> \<rightarrow>\<^sub>o Prop, Prop]"
  then obtain p q where "xs = [p, q]"
    and p:
      "Elem p (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    and q: "Elem q (pp_e_domain Prop)"
    by (auto simp: list_all2_Cons2)
  obtain a where a: "Elem a (pp_e_domain \<sigma>)"
    using pp_e_domain_nonempty by blast
  show "pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam Prop
            (Disj (Var 0)
              (Forall \<sigma> (App (Var 2) (Var 0)))))))
        xs) v =
    pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam Prop
            (Forall \<sigma>
              (Disj (Var 1) (App (Var 2) (Var 0)))))))
        xs) v"
    using p q a \<open>xs = [p, q]\<close>
    by (simp add: Lambda_app; blast)
next
  show "\<Gamma> \<turnstile>
      Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam Prop
        (Disj (Var 0)
          (Forall \<sigma> (App (Var 2) (Var 0))))) :
      (\<sigma> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o
        pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
next
  show "\<Gamma> \<turnstile>
      Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam Prop
        (Forall \<sigma>
          (Disj (Var 1) (App (Var 2) (Var 0))))) :
      (\<sigma> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o
        pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
qed

lemma pp_e_classic_absorb_conj_exists_valid:
  "pp_e_valid \<Gamma> (classic_absorb_conj_exists \<sigma>)"
  unfolding classic_absorb_conj_exists_def pred_ty_def
proof (rule pp_e_vector_equation_valid[
    where \<sigma>s="[\<sigma> \<rightarrow>\<^sub>o Prop, \<sigma>]",
    simplified])
  fix \<rho> v xs
  assume "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<tau>. Elem x (pp_e_domain \<tau>))
        xs [\<sigma> \<rightarrow>\<^sub>o Prop, \<sigma>]"
  then obtain p x where "xs = [p, x]"
    and p:
      "Elem p (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    and x: "Elem x (pp_e_domain \<sigma>)"
    by (auto simp: list_all2_Cons2)
  then show "pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
            (Conj (App (Var 1) (Var 0))
              (Exists \<sigma> (App (Var 2) (Var 0)))))))
        xs) v =
    pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
            (App (Var 1) (Var 0))))) xs) v"
    using p x by (simp add: Lambda_app; blast)
next
  show "\<Gamma> \<turnstile>
      Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
        (Conj (App (Var 1) (Var 0))
          (Exists \<sigma> (App (Var 2) (Var 0))))) :
      (\<sigma> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o
        \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
next
  show "\<Gamma> \<turnstile>
      Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam \<sigma>
        (App (Var 1) (Var 0))) :
      (\<sigma> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o
        \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
qed

lemma pp_e_classic_dist_conj_exists_valid:
  "pp_e_valid \<Gamma> (classic_dist_conj_exists \<sigma>)"
  unfolding classic_dist_conj_exists_def pred_ty_def
proof (rule pp_e_vector_equation_valid[
    where \<sigma>s="[\<sigma> \<rightarrow>\<^sub>o Prop, Prop]",
    simplified])
  fix \<rho> v xs
  assume "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<tau>. Elem x (pp_e_domain \<tau>))
        xs [\<sigma> \<rightarrow>\<^sub>o Prop, Prop]"
  then obtain p q where "xs = [p, q]"
    and p:
      "Elem p (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    and q: "Elem q (pp_e_domain Prop)"
    by (auto simp: list_all2_Cons2)
  then show "pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam Prop
            (Conj (Var 0)
              (Exists \<sigma> (App (Var 2) (Var 0)))))))
        xs) v =
    pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam Prop
            (Exists \<sigma>
              (Conj (Var 1) (App (Var 2) (Var 0)))))))
        xs) v"
    using p q by (simp add: Lambda_app; blast)
next
  show "\<Gamma> \<turnstile>
      Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam Prop
        (Conj (Var 0)
          (Exists \<sigma> (App (Var 2) (Var 0))))) :
      (\<sigma> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o
        pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
next
  show "\<Gamma> \<turnstile>
      Lam (\<sigma> \<rightarrow>\<^sub>o Prop) (Lam Prop
        (Exists \<sigma>
          (Conj (Var 1) (App (Var 2) (Var 0))))) :
      (\<sigma> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o
        pp_e_unary_type"
    by (rule infer_type_sound) (simp add: lookup_def)
qed

lemma pp_e_classic_identity_identity_valid:
  "pp_e_valid \<Gamma> (classic_identity_identity \<sigma>)"
  unfolding classic_identity_identity_def
    identity_ty_def pred_ty_def
proof (rule pp_e_vector_equation_valid[
    where \<sigma>s="[\<sigma>, \<sigma>]", simplified])
  fix \<rho> v xs
  assume "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<tau>. Elem x (pp_e_domain \<tau>))
        xs [\<sigma>, \<sigma>]"
  then obtain x y where xs_def: "xs = [x, y]"
    and x: "Elem x (pp_e_domain \<sigma>)"
    and y: "Elem y (pp_e_domain \<sigma>)"
    by (auto simp: list_all2_Cons2)
  have characterization:
      "pp_e_eqv \<sigma> v x y =
        (\<forall>p.
          Elem p
            (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))
          \<longrightarrow>
          ((pp_e_holds (p \<acute> x) v
              \<longrightarrow> pp_e_holds (p \<acute> y) v)
           \<and>
           (pp_e_holds (p \<acute> y) v
              \<longrightarrow> pp_e_holds (p \<acute> x) v)))"
  proof
    assume xy: "pp_e_eqv \<sigma> v x y"
    show "\<forall>p.
        Elem p
          (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))
        \<longrightarrow>
        ((pp_e_holds (p \<acute> x) v
            \<longrightarrow> pp_e_holds (p \<acute> y) v)
         \<and>
         (pp_e_holds (p \<acute> y) v
            \<longrightarrow> pp_e_holds (p \<acute> x) v))"
    proof (intro allI impI)
      fix p
      assume p:
          "Elem p
            (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      have pxy:
          "pp_e_eqv Prop v (p \<acute> x) (p \<acute> y)"
        using pp_e_app_respects[
          OF pp_e_eqv_reflexive[OF p] x y xy] .
      have yx: "pp_e_eqv \<sigma> v y x"
        using pp_e_eqv_symmetric[OF x y xy] .
      have pyx:
          "pp_e_eqv Prop v (p \<acute> y) (p \<acute> x)"
        using pp_e_app_respects[
          OF pp_e_eqv_reflexive[OF p] y x yx] .
      have forward:
          "pp_e_holds (p \<acute> x) v =
            pp_e_holds (p \<acute> y) v"
        using pp_e_prop_eqv_at[
          OF pxy, of v] by simp
      have backward:
          "pp_e_holds (p \<acute> y) v =
            pp_e_holds (p \<acute> x) v"
        using pp_e_prop_eqv_at[
          OF pyx, of v] by simp
      show "(pp_e_holds (p \<acute> x) v
              \<longrightarrow> pp_e_holds (p \<acute> y) v)
          \<and>
          (pp_e_holds (p \<acute> y) v
              \<longrightarrow> pp_e_holds (p \<acute> x) v)"
        using forward backward by blast
    qed
  next
    assume all_predicates:
        "\<forall>p.
          Elem p
            (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))
          \<longrightarrow>
          ((pp_e_holds (p \<acute> x) v
              \<longrightarrow> pp_e_holds (p \<acute> y) v)
           \<and>
           (pp_e_holds (p \<acute> y) v
              \<longrightarrow> pp_e_holds (p \<acute> x) v))"
    let ?P =
      "Lambda (pp_e_domain \<sigma>)
        (\<lambda>z. pp_e_prop
          (\<lambda>u. pp_e_eqv \<sigma> u x z))"
    have predicate_term_type:
        "[\<sigma>] \<turnstile>
          Lam \<sigma> (Eq \<sigma> (Var 1) (Var 0)) :
          \<sigma> \<rightarrow>\<^sub>o Prop"
      by (rule infer_type_sound) (simp add: lookup_def)
    have env_x:
        "pp_e_env_typed [\<sigma>] (extend_env x \<rho>)"
      using pp_e_env_typed_extend[
        OF pp_e_empty_env_typed x] .
    have P_typed:
        "Elem ?P
          (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
      using pp_e_eval_type[
        OF predicate_term_type env_x]
      by (simp add: pp_e_dom_def)
    have Pxx: "pp_e_holds (?P \<acute> x) v"
      using x pp_e_eqv_reflexive[OF x, of v]
      by (simp add: Lambda_app)
    have Pxy:
        "pp_e_holds (?P \<acute> x) v
          \<longrightarrow> pp_e_holds (?P \<acute> y) v"
      using all_predicates P_typed by blast
    have Py: "pp_e_holds (?P \<acute> y) v"
      using Pxx Pxy by blast
    show "pp_e_eqv \<sigma> v x y"
      using y Py by (simp add: Lambda_app)
  qed
  show "pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam \<sigma> (Lam \<sigma>
            (Eq \<sigma> (Var 1) (Var 0)))))
        xs) v =
    pp_e_holds
      (pp_e_app_values
        (pp_e_eval C \<rho>
          (Lam \<sigma> (Lam \<sigma>
            (Forall (\<sigma> \<rightarrow>\<^sub>o Prop)
              ((App (Var 0) (Var 2))
                \<longleftrightarrow>\<^sub>o
              (App (Var 0) (Var 1)))))))
        xs) v"
    using characterization x y
    unfolding xs_def
    by (simp add: Lambda_app)
next
  show "\<Gamma> \<turnstile>
      Lam \<sigma> (Lam \<sigma>
        (Eq \<sigma> (Var 1) (Var 0))) :
      \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
next
  show "\<Gamma> \<turnstile>
      Lam \<sigma> (Lam \<sigma>
        (Forall (\<sigma> \<rightarrow>\<^sub>o Prop)
          ((App (Var 0) (Var 2))
            \<longleftrightarrow>\<^sub>o
           (App (Var 0) (Var 1))))) :
      \<sigma> \<rightarrow>\<^sub>o \<sigma> \<rightarrow>\<^sub>o Prop"
    by (rule infer_type_sound) (simp add: lookup_def)
qed

theorem pp_e_C_sound:
  assumes "\<Gamma> \<turnstile>\<^sub>C A"
  shows "pp_e_valid \<Gamma> A"
  using assms
proof (induction rule: C_proves.induct)
  case (H \<Gamma> A)
  then show ?case by (rule pp_e_H_sound)
next
  case (BooleanIdentity A \<Gamma>)
  then show ?case by (rule pp_e_boolean_identity_valid)
next
  case (IdentityIdentity \<Gamma> \<sigma>)
  show ?case by (rule pp_e_classic_identity_identity_valid)
next
  case (AbsorbDisjForall \<Gamma> \<sigma>)
  show ?case by (rule pp_e_classic_absorb_disj_forall_valid)
next
  case (DistDisjForall \<Gamma> \<sigma>)
  show ?case by (rule pp_e_classic_dist_disj_forall_valid)
next
  case (AbsorbConjExists \<Gamma> \<sigma>)
  show ?case by (rule pp_e_classic_absorb_conj_exists_valid)
next
  case (DistConjExists \<Gamma> \<sigma>)
  show ?case by (rule pp_e_classic_dist_conj_exists_valid)
next
  case (MP \<Gamma> A B)
  show ?case by (rule pp_e_valid_MP[OF MP.IH(1) MP.IH(2)])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case
    by (rule pp_e_H_Gen_valid[
      OF Gen.hyps(1) Gen.hyps(2) Gen.IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case
    by (rule pp_e_H_Inst_valid[
      OF Inst.hyps(1) Inst.hyps(2) Inst.IH])
qed

lemma pp_e_CE_PropEquivalence_valid:
  assumes A: "\<Gamma> \<turnstile> A : Prop"
    and B: "\<Gamma> \<turnstile> B : Prop"
    and premise:
      "pp_e_valid \<Gamma> (A \<longleftrightarrow>\<^sub>o B)"
  shows "pp_e_valid \<Gamma> (Eq Prop A B)"
proof -
  have typed: "\<Gamma> \<turnstile> Eq Prop A B : Prop"
    using A B by auto
  have holds:
      "\<And>\<rho> w. pp_e_env_typed \<Gamma> \<rho> \<Longrightarrow>
        pp_e_holds
          (pp_e_eval C \<rho> (Eq Prop A B)) w"
  proof -
    fix \<rho> w
    assume env: "pp_e_env_typed \<Gamma> \<rho>"
    have relation:
        "pp_e_eqv Prop w
          (pp_e_eval C \<rho> A) (pp_e_eval C \<rho> B)"
    proof (simp, intro allI impI)
      fix v
      assume "prefix w v"
      have iff:
          "pp_e_holds
            (pp_e_eval C \<rho>
              (A \<longleftrightarrow>\<^sub>o B)) v"
        using pp_e_valid_holds[OF premise env] .
      show "pp_e_holds (pp_e_eval C \<rho> A) v =
          pp_e_holds (pp_e_eval C \<rho> B) v"
        using iff by auto
    qed
    show "pp_e_holds
        (pp_e_eval C \<rho> (Eq Prop A B)) w"
      using relation by simp
  qed
  show ?thesis
    unfolding pp_e_valid_def using typed holds by blast
qed

theorem pp_e_CE_sound:
  assumes "\<Gamma> \<turnstile>\<^sub>CE A"
  shows "pp_e_valid \<Gamma> A"
  using assms
proof (induction rule: CE_proves.induct)
  case (C \<Gamma> A)
  then show ?case by (rule pp_e_C_sound)
next
  case (PropEquivalence \<Gamma> A B)
  show ?case
    by (rule pp_e_CE_PropEquivalence_valid[
      OF PropEquivalence.hyps(1)
        PropEquivalence.hyps(2) PropEquivalence.IH])
next
  case (MP \<Gamma> A B)
  show ?case by (rule pp_e_valid_MP[OF MP.IH(1) MP.IH(2)])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case
    by (rule pp_e_H_Gen_valid[
      OF Gen.hyps(1) Gen.hyps(2) Gen.IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case
    by (rule pp_e_H_Inst_valid[
      OF Inst.hyps(1) Inst.hyps(2) Inst.IH])
qed

lemma pp_e_zeta_valid:
  assumes F_type:
      "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop"
    and G_type:
      "\<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop"
    and zeta:
      "pp_e_valid (\<sigma>s @ \<Gamma>)
        (zeta_body \<sigma>s F G)"
  shows "pp_e_valid \<Gamma>
    (Eq (arrow_type \<sigma>s Prop) F G)"
proof (rule pp_e_vector_equation_valid[
    OF F_type G_type])
  fix \<rho> v xs
  assume env: "pp_e_env_typed \<Gamma> \<rho>"
    and xs:
      "list_all2
        (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>))
        xs \<sigma>s"
  have len: "length xs = length \<sigma>s"
    using list_all2_lengthD[OF xs] .
  have extended:
      "pp_e_env_typed (\<sigma>s @ \<Gamma>)
        (extend_envs xs \<rho>)"
    using pp_e_env_typed_extends[OF env xs] .
  have zeta_holds:
      "pp_e_holds
        (pp_e_eval C (extend_envs xs \<rho>)
          (zeta_body \<sigma>s F G)) v"
    using pp_e_valid_holds[OF zeta extended] .
  have shift_F:
      "pp_e_eval C (extend_envs xs \<rho>)
        (shift_by (length \<sigma>s) F) =
      pp_e_eval C \<rho> F"
    using pp_e_eval_shift_by_extend_envs[
      of C xs \<rho> F] len by simp
  have shift_G:
      "pp_e_eval C (extend_envs xs \<rho>)
        (shift_by (length \<sigma>s) G) =
      pp_e_eval C \<rho> G"
    using pp_e_eval_shift_by_extend_envs[
      of C xs \<rho> G] len by simp
  have fresh:
      "map (pp_e_eval C (extend_envs xs \<rho>))
        (fresh_vars (length \<sigma>s)) = xs"
    using pp_e_map_eval_fresh_vars_extend_envs[
      of C xs \<rho>] len by simp
  have iff:
      "(pp_e_holds
          (pp_e_app_values (pp_e_eval C \<rho> F) xs) v
          \<longrightarrow>
        pp_e_holds
          (pp_e_app_values (pp_e_eval C \<rho> G) xs) v)
      \<and>
      (pp_e_holds
          (pp_e_app_values (pp_e_eval C \<rho> G) xs) v
          \<longrightarrow>
        pp_e_holds
          (pp_e_app_values (pp_e_eval C \<rho> F) xs) v)"
    using zeta_holds
    by (simp add: zeta_body_def pp_e_eval_app_vec
        shift_F shift_G fresh)
  show "pp_e_holds
      (pp_e_app_values (pp_e_eval C \<rho> F) xs) v =
    pp_e_holds
      (pp_e_app_values (pp_e_eval C \<rho> G) xs) v"
    using iff by blast
qed

theorem pp_e_CEV_valid:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "pp_e_valid \<Gamma> A"
  using assms
proof (induction rule: CEV_proves.induct)
  case (CE \<Gamma> A)
  then show ?case by (rule pp_e_CE_sound)
next
  case (VectorEquivalence \<Gamma> F \<sigma>s G)
  show ?case
    by (rule pp_e_zeta_valid[
      OF VectorEquivalence.hyps(1)
        VectorEquivalence.hyps(2)
        VectorEquivalence.IH])
next
  case (MP \<Gamma> A B)
  show ?case by (rule pp_e_valid_MP[OF MP.IH(1) MP.IH(2)])
next
  case (Gen \<Gamma> P \<sigma> Q)
  show ?case
    by (rule pp_e_H_Gen_valid[
      OF Gen.hyps(1) Gen.hyps(2) Gen.IH])
next
  case (Inst \<sigma> \<Gamma> P Q)
  show ?case
    by (rule pp_e_H_Inst_valid[
      OF Inst.hyps(1) Inst.hyps(2) Inst.IH])
qed

theorem pp_e_base_sound:
  assumes "\<Gamma> \<turnstile>\<^sub>CEV A"
  shows "ExactBaconHenkin.gvalid \<Gamma> A"
  using pp_e_CEV_valid[OF assms]
  by (rule pp_e_valid_implies_gvalid)

lemma pp_e_closed_gvalid_all_contexts:
  assumes typed: "[] \<turnstile> A : Prop"
    and empty: "ExactBaconHenkin.gvalid [] A"
  shows "ExactBaconHenkin.gvalid \<Gamma> A"
proof (rule ExactBaconHenkin.gvalidI)
  fix env w
  assume env_ok: "env_ok (map pp_e_dom \<Gamma>) env"
  let ?rho = "pp_e_list_env env"
  let ?eta = "pp_e_list_env []"
  have empty_ok: "env_ok (map pp_e_dom []) []"
    by simp
  have empty_holds:
      "pp_e_holds (pp_e_den A []) w"
    using ExactBaconHenkin.gvalidD[OF empty empty_ok] .
  have related:
      "pp_e_eqv Prop w
        (pp_e_eval C ?rho A) (pp_e_eval C ?eta A)"
    using pp_e_eval_respects[
      OF typed pp_e_empty_env_eqv] .
  have transfer:
      "pp_e_holds (pp_e_eval C ?rho A) w =
        pp_e_holds (pp_e_eval C ?eta A) w"
    using pp_e_prop_eqv_at[OF related, of w] by simp
  show "pp_e_holds (pp_e_den A env) w"
    using empty_holds transfer
    unfolding pp_e_den_def by simp
qed

lemma pp_e_closed_not_gvalid_iff_counterworld:
  "\<not> ExactBaconHenkin.gvalid [] A
    \<longleftrightarrow>
    (\<exists>w. \<not> pp_e_holds (pp_e_den A []) w)"
  unfolding ExactBaconHenkin.gvalid_def env_ok_def
  by auto

theorem pp_e_zeta_sound:
  assumes F_type:
      "\<Gamma> \<turnstile> F : arrow_type \<sigma>s Prop"
    and G_type:
      "\<Gamma> \<turnstile> G : arrow_type \<sigma>s Prop"
    and zeta:
      "ExactBaconHenkin.gvalid (\<sigma>s @ \<Gamma>)
        (zeta_body \<sigma>s F G)"
  shows "ExactBaconHenkin.gvalid \<Gamma>
    (Eq (arrow_type \<sigma>s Prop) F G)"
proof (rule ExactBaconHenkin.gvalidI)
  fix env w
  assume env_ok: "env_ok (map pp_e_dom \<Gamma>) env"
  let ?rho = "pp_e_list_env env"
  have rho: "pp_e_env_typed \<Gamma> ?rho"
    using env_ok_implies_pp_e_env_typed[OF env_ok] .
  have F:
      "Elem (pp_e_eval C ?rho F)
        (pp_e_domain (arrow_type \<sigma>s Prop))"
    using pp_e_eval_type[OF F_type rho]
    by (simp add: pp_e_dom_def)
  have G:
      "Elem (pp_e_eval C ?rho G)
        (pp_e_domain (arrow_type \<sigma>s Prop))"
    using pp_e_eval_type[OF G_type rho]
    by (simp add: pp_e_dom_def)
  have relation:
      "pp_e_eqv (arrow_type \<sigma>s Prop) w
        (pp_e_eval C ?rho F) (pp_e_eval C ?rho G)"
  proof (rule pp_e_vector_extensionality[OF F G])
    fix v xs
    assume wv: "prefix w v"
      and xs:
        "list_all2
          (\<lambda>x \<sigma>. Elem x (pp_e_domain \<sigma>)) xs \<sigma>s"
    have extended:
        "pp_e_env_typed (\<sigma>s @ \<Gamma>)
          (extend_envs xs ?rho)"
      using pp_e_env_typed_extends[OF rho xs] .
    have xs_length: "length xs = length \<sigma>s"
      using list_all2_lengthD[OF xs] .
    have zeta_holds:
        "pp_e_holds
          (pp_e_eval C (extend_envs xs ?rho)
            (zeta_body \<sigma>s F G)) v"
    proof -
      have list_env:
          "\<exists>zs.
            env_ok (map pp_e_dom (\<sigma>s @ \<Gamma>)) zs
            \<and>
            pp_e_list_env zs = extend_envs xs ?rho"
      proof -
        let ?zs = "xs @ env"
        have ok:
            "env_ok (map pp_e_dom (\<sigma>s @ \<Gamma>)) ?zs"
          using xs env_ok
          by (auto simp: env_ok_def pp_e_dom_def
              list_all2_conv_all_nth nth_append)
        have list_env_eq:
            "pp_e_list_env ?zs = extend_envs xs ?rho"
          using pp_e_list_env_append[of xs env] by simp
        show ?thesis using ok list_env_eq by blast
      qed
      then obtain zs where zs_ok:
          "env_ok (map pp_e_dom (\<sigma>s @ \<Gamma>)) zs"
        and zs_env:
          "pp_e_list_env zs = extend_envs xs ?rho"
        by blast
      have holds_den:
          "pp_e_holds
            (pp_e_den
              (zeta_body \<sigma>s F G) zs) v"
        using ExactBaconHenkin.gvalidD[OF zeta zs_ok] .
      show ?thesis
        using holds_den
        unfolding pp_e_den_def zs_env .
    qed
    have shift_F:
        "pp_e_eval C (extend_envs xs ?rho)
          (shift_by (length \<sigma>s) F) =
        pp_e_eval C ?rho F"
      using pp_e_eval_shift_by_extend_envs[
        of C xs ?rho F] xs_length by simp
    have shift_G:
        "pp_e_eval C (extend_envs xs ?rho)
          (shift_by (length \<sigma>s) G) =
        pp_e_eval C ?rho G"
      using pp_e_eval_shift_by_extend_envs[
        of C xs ?rho G] xs_length by simp
    have fresh:
        "map (pp_e_eval C (extend_envs xs ?rho))
          (fresh_vars (length \<sigma>s)) = xs"
      using pp_e_map_eval_fresh_vars_extend_envs[
        of C xs ?rho] xs_length by simp
    show "pp_e_holds
        (pp_e_app_values (pp_e_eval C ?rho F) xs) v =
      pp_e_holds
        (pp_e_app_values (pp_e_eval C ?rho G) xs) v"
    proof -
      have iff:
          "(pp_e_holds
              (pp_e_app_values (pp_e_eval C ?rho F) xs) v
              \<longrightarrow>
            pp_e_holds
              (pp_e_app_values (pp_e_eval C ?rho G) xs) v)
          \<and>
          (pp_e_holds
              (pp_e_app_values (pp_e_eval C ?rho G) xs) v
              \<longrightarrow>
            pp_e_holds
              (pp_e_app_values (pp_e_eval C ?rho F) xs) v)"
        using zeta_holds
        by (simp add: zeta_body_def pp_e_eval_app_vec
            shift_F shift_G fresh)
      show ?thesis using iff by blast
    qed
  qed
  show "pp_e_holds
      (pp_e_den
        (Eq (arrow_type \<sigma>s Prop) F G) env) w"
    unfolding pp_e_den_def
    using relation by simp
qed

end


end
