theory Bacon_PP_ZF_Exact_Substitution
  imports 
    "Goodman_Exact_Legacy_04.Bacon_PP_ZF_Exact_Frame"
begin

section \<open>Substitution for Bacon's exact interpretation\<close>

lemma pp_e_prop_ext:
  assumes P: "Elem P (pp_e_domain Prop)"
    and Q: "Elem Q (pp_e_domain Prop)"
    and pointwise: "\<And>w. pp_e_holds P w = pp_e_holds Q w"
  shows "P = Q"
proof -
  have Pn: "Elem P (Power Nat)"
    using P by simp
  have Qn: "Elem Q (Power Nat)"
    using Q by simp
  have "P = pp_e_prop (pp_e_holds P)"
    using pp_n_prop_eta[OF Pn] by simp
  also have "... = pp_e_prop (pp_e_holds Q)"
    using pointwise by simp
  also have "... = Q"
    using pp_n_prop_eta[OF Qn] by simp
  finally show ?thesis .
qed

lemma pp_e_action_holds[simp]:
  "pp_e_holds (pp_b_action Prop i P) w =
    pp_e_holds P (rev i @ w)"
  by simp

lemma pp_e_holds_from_action_eq:
  assumes action: "pp_b_action Prop i P = Q"
  shows "pp_e_holds P (rev i @ w) = pp_e_holds Q w"
proof -
  have "pp_e_holds (pp_b_action Prop i P) w = pp_e_holds Q w"
    using action by simp
  then show ?thesis by simp
qed

lemma pp_e_eqv_action_shift:
  assumes x: "Elem x (pp_e_domain \<sigma>)"
    and y: "Elem y (pp_e_domain \<sigma>)"
  shows "pp_e_eqv \<sigma> (rev i @ w) x y \<longleftrightarrow>
    pp_e_eqv \<sigma> w
      (pp_b_action \<sigma> i x) (pp_b_action \<sigma> i y)"
proof -
  have ax: "Elem (pp_b_action \<sigma> i x) (pp_e_domain \<sigma>)"
    by (rule pp_b_action_closed_all[OF x])
  have ay: "Elem (pp_b_action \<sigma> i y) (pp_e_domain \<sigma>)"
    by (rule pp_b_action_closed_all[OF y])
  have left:
      "pp_e_eqv \<sigma> (rev i @ w) x y \<longleftrightarrow>
       pp_b_action \<sigma> (rev w @ i) x =
       pp_b_action \<sigma> (rev w @ i) y"
    using pp_e_eqv_iff_action_eq[OF x y, of "rev i @ w"]
    by (simp add: rev_append)
  have action_x:
      "pp_b_action \<sigma> (rev w)
          (pp_b_action \<sigma> i x) =
       pp_b_action \<sigma> (rev w @ i) x"
    by (rule pp_b_action_comp_all[OF x])
  have action_y:
      "pp_b_action \<sigma> (rev w)
          (pp_b_action \<sigma> i y) =
       pp_b_action \<sigma> (rev w @ i) y"
    by (rule pp_b_action_comp_all[OF y])
  show ?thesis
    using left pp_e_eqv_iff_action_eq[OF ax ay, of w]
      action_x action_y by simp
qed

definition pp_e_env_action ::
    "ctx \<Rightarrow> pp_word \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow>
      (nat \<Rightarrow> ZF) \<Rightarrow> bool"
where
  "pp_e_env_action \<Gamma> i \<rho> \<eta> \<longleftrightarrow>
    (\<forall>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<longrightarrow>
      \<eta> n = pp_b_action \<sigma> i (\<rho> n))"

lemma pp_e_env_action_lookup:
  assumes rel: "pp_e_env_action \<Gamma> i \<rho> \<eta>"
    and lookup: "lookup \<Gamma> n = Some \<sigma>"
  shows "\<eta> n = pp_b_action \<sigma> i (\<rho> n)"
  using rel lookup unfolding pp_e_env_action_def by blast

lemma pp_e_env_action_extend:
  assumes rel: "pp_e_env_action \<Gamma> i \<rho> \<eta>"
    and image: "b = pp_b_action \<sigma> i a"
  shows "pp_e_env_action (\<sigma> # \<Gamma>) i
    (extend_env a \<rho>) (extend_env b \<eta>)"
proof (unfold pp_e_env_action_def, intro allI impI)
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "extend_env b \<eta> n =
      pp_b_action \<tau> i (extend_env a \<rho> n)"
  proof (cases n)
    case 0
    then show ?thesis using lookup image by simp
  next
    case (Suc m)
    then have old: "lookup \<Gamma> m = Some \<tau>"
      using lookup by simp
    show ?thesis
      using Suc pp_e_env_action_lookup[OF rel old] by simp
  qed
qed

lemma pp_e_env_action_target_typed:
  assumes source: "pp_e_env_typed \<Gamma> \<rho>"
    and rel: "pp_e_env_action \<Gamma> i \<rho> \<eta>"
  shows "pp_e_env_typed \<Gamma> \<eta>"
proof (unfold pp_e_env_typed_def, intro allI impI)
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  have x: "Elem (\<rho> n) (pp_e_domain \<sigma>)"
    by (rule pp_e_env_typed_lookup[OF source lookup])
  have image: "\<eta> n = pp_b_action \<sigma> i (\<rho> n)"
    by (rule pp_e_env_action_lookup[OF rel lookup])
  show "Elem (\<eta> n) (pp_e_domain \<sigma>)"
    unfolding image by (rule pp_b_action_closed_all[OF x])
qed

lemma pp_e_action_bounded_forall:
  assumes F: "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
      Elem (F x) (pp_e_domain Prop)"
    and G: "\<And>a. Elem a (pp_e_domain \<sigma>) \<Longrightarrow>
      Elem (G a) (pp_e_domain Prop)"
    and commute: "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
      pp_b_action Prop i (F x) =
        G (pp_b_action \<sigma> i x)"
  shows "pp_b_action Prop i
      (pp_e_prop (\<lambda>w. \<forall>x. Elem x (pp_e_domain \<sigma>) \<longrightarrow>
        pp_e_holds (F x) w)) =
    pp_e_prop (\<lambda>w. \<forall>a. Elem a (pp_e_domain \<sigma>) \<longrightarrow>
      pp_e_holds (G a) w)"
proof (rule pp_e_prop_ext)
  show "Elem (pp_b_action Prop i
      (pp_e_prop (\<lambda>w. \<forall>x. Elem x (pp_e_domain \<sigma>) \<longrightarrow>
        pp_e_holds (F x) w))) (pp_e_domain Prop)"
    by (rule pp_b_action_closed_all[OF pp_e_prop_in_domain])
  show "Elem (pp_e_prop
      (\<lambda>w. \<forall>a. Elem a (pp_e_domain \<sigma>) \<longrightarrow>
        pp_e_holds (G a) w)) (pp_e_domain Prop)"
    by (rule pp_e_prop_in_domain)
  fix w
  show "pp_e_holds
      (pp_b_action Prop i
        (pp_e_prop (\<lambda>v. \<forall>x.
          Elem x (pp_e_domain \<sigma>) \<longrightarrow>
          pp_e_holds (F x) v))) w =
    pp_e_holds
      (pp_e_prop (\<lambda>v. \<forall>a.
        Elem a (pp_e_domain \<sigma>) \<longrightarrow>
        pp_e_holds (G a) v)) w"
  proof
    assume all_source:
        "pp_e_holds
          (pp_b_action Prop i
            (pp_e_prop (\<lambda>v. \<forall>x.
              Elem x (pp_e_domain \<sigma>) \<longrightarrow>
              pp_e_holds (F x) v))) w"
    show "pp_e_holds
        (pp_e_prop (\<lambda>v. \<forall>a.
          Elem a (pp_e_domain \<sigma>) \<longrightarrow>
          pp_e_holds (G a) v)) w"
    proof (simp, intro allI impI)
      fix a
      assume a: "Elem a (pp_e_domain \<sigma>)"
      obtain x where x: "Elem x (pp_e_domain \<sigma>)"
        and ax: "pp_b_action \<sigma> i x = a"
        using pp_b_action_surjective_all[OF a, of i] by blast
      have source_x: "pp_e_holds (F x) (rev i @ w)"
        using all_source x by simp
      have target_x:
          "pp_e_holds (G (pp_b_action \<sigma> i x)) w"
      proof -
        have view:
            "pp_e_holds (pp_b_action Prop i (F x)) w"
          using source_x by simp
        have identify:
            "G (pp_b_action \<sigma> i x) =
             pp_b_action Prop i (F x)"
          using commute[OF x] by simp
        show ?thesis using view identify by simp
      qed
      show "pp_e_holds (G a) w"
        using target_x ax by simp
    qed
  next
    assume all_target:
        "pp_e_holds
          (pp_e_prop (\<lambda>v. \<forall>a.
            Elem a (pp_e_domain \<sigma>) \<longrightarrow>
            pp_e_holds (G a) v)) w"
    show "pp_e_holds
        (pp_b_action Prop i
          (pp_e_prop (\<lambda>v. \<forall>x.
            Elem x (pp_e_domain \<sigma>) \<longrightarrow>
            pp_e_holds (F x) v))) w"
    proof (simp, intro allI impI)
      fix x
      assume x: "Elem x (pp_e_domain \<sigma>)"
      have ax:
          "Elem (pp_b_action \<sigma> i x) (pp_e_domain \<sigma>)"
        by (rule pp_b_action_closed_all[OF x])
      have target:
          "pp_e_holds (G (pp_b_action \<sigma> i x)) w"
        using all_target ax by simp
      show "pp_e_holds (F x) (rev i @ w)"
      proof -
        have identify:
            "G (pp_b_action \<sigma> i x) =
             pp_b_action Prop i (F x)"
          using commute[OF x] by simp
        have view: "pp_e_holds (pp_b_action Prop i (F x)) w"
          using target identify by simp
        show ?thesis using view by simp
      qed
    qed
  qed
qed

lemma pp_e_action_bounded_exists:
  assumes F: "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
      Elem (F x) (pp_e_domain Prop)"
    and G: "\<And>a. Elem a (pp_e_domain \<sigma>) \<Longrightarrow>
      Elem (G a) (pp_e_domain Prop)"
    and commute: "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
      pp_b_action Prop i (F x) =
        G (pp_b_action \<sigma> i x)"
  shows "pp_b_action Prop i
      (pp_e_prop (\<lambda>w. \<exists>x. Elem x (pp_e_domain \<sigma>) \<and>
        pp_e_holds (F x) w)) =
    pp_e_prop (\<lambda>w. \<exists>a. Elem a (pp_e_domain \<sigma>) \<and>
      pp_e_holds (G a) w)"
proof (rule pp_e_prop_ext)
  show "Elem (pp_b_action Prop i
      (pp_e_prop (\<lambda>w. \<exists>x. Elem x (pp_e_domain \<sigma>) \<and>
        pp_e_holds (F x) w))) (pp_e_domain Prop)"
    by (rule pp_b_action_closed_all[OF pp_e_prop_in_domain])
  show "Elem (pp_e_prop
      (\<lambda>w. \<exists>a. Elem a (pp_e_domain \<sigma>) \<and>
        pp_e_holds (G a) w)) (pp_e_domain Prop)"
    by (rule pp_e_prop_in_domain)
  fix w
  show "pp_e_holds
      (pp_b_action Prop i
        (pp_e_prop (\<lambda>v. \<exists>x.
          Elem x (pp_e_domain \<sigma>) \<and>
          pp_e_holds (F x) v))) w =
    pp_e_holds
      (pp_e_prop (\<lambda>v. \<exists>a.
        Elem a (pp_e_domain \<sigma>) \<and>
        pp_e_holds (G a) v)) w"
  proof
    assume some_source:
        "pp_e_holds
          (pp_b_action Prop i
            (pp_e_prop (\<lambda>v. \<exists>x.
              Elem x (pp_e_domain \<sigma>) \<and>
              pp_e_holds (F x) v))) w"
    then obtain x where x: "Elem x (pp_e_domain \<sigma>)"
      and source_x: "pp_e_holds (F x) (rev i @ w)"
      by auto
    have ax: "Elem (pp_b_action \<sigma> i x) (pp_e_domain \<sigma>)"
      by (rule pp_b_action_closed_all[OF x])
    have target:
        "pp_e_holds (G (pp_b_action \<sigma> i x)) w"
    proof -
      have view: "pp_e_holds (pp_b_action Prop i (F x)) w"
        using source_x by simp
      have identify:
          "G (pp_b_action \<sigma> i x) =
           pp_b_action Prop i (F x)"
        using commute[OF x] by simp
      show ?thesis using view identify by simp
    qed
    show "pp_e_holds
        (pp_e_prop (\<lambda>v. \<exists>a.
          Elem a (pp_e_domain \<sigma>) \<and>
          pp_e_holds (G a) v)) w"
      using ax target by simp blast
  next
    assume some_target:
        "pp_e_holds
          (pp_e_prop (\<lambda>v. \<exists>a.
            Elem a (pp_e_domain \<sigma>) \<and>
            pp_e_holds (G a) v)) w"
    then obtain a where a: "Elem a (pp_e_domain \<sigma>)"
      and target: "pp_e_holds (G a) w"
      by auto
    obtain x where x: "Elem x (pp_e_domain \<sigma>)"
      and ax: "pp_b_action \<sigma> i x = a"
      using pp_b_action_surjective_all[OF a, of i] by blast
    have source_x: "pp_e_holds (F x) (rev i @ w)"
    proof -
      have identify:
          "G (pp_b_action \<sigma> i x) =
           pp_b_action Prop i (F x)"
        using commute[OF x] by simp
      have view: "pp_e_holds (pp_b_action Prop i (F x)) w"
        using target ax identify by simp
      show ?thesis using view by simp
    qed
    show "pp_e_holds
        (pp_b_action Prop i
          (pp_e_prop (\<lambda>v. \<exists>x.
            Elem x (pp_e_domain \<sigma>) \<and>
            pp_e_holds (F x) v))) w"
      using x source_x by simp blast
  qed
qed

locale pp_e_equivariant_constants = pp_e_constants C
  for C :: "string \<Rightarrow> otype \<Rightarrow> ZF" +
  assumes C_action:
    "pp_b_action \<sigma> i (C c \<sigma>) = C c \<sigma>"
begin

theorem pp_e_eval_action:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and source: "pp_e_env_typed \<Gamma> \<rho>"
    and rel: "pp_e_env_action \<Gamma> i \<rho> \<eta>"
  shows "pp_b_action \<tau> i (pp_e_eval C \<rho> M) =
    pp_e_eval C \<eta> M"
  using typed source rel
proof (induction arbitrary: \<rho> \<eta> i rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  then show ?case
    using pp_e_env_action_lookup by simp
next
  case (Const \<Gamma> c \<tau>)
  then show ?case using C_action by simp
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  have f:
      "Elem (pp_e_eval C \<rho> M)
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using pp_e_eval_type[OF App.hyps(1) App.prems(1)]
    by (simp add: pp_e_dom_def)
  have a: "Elem (pp_e_eval C \<rho> N) (pp_e_domain \<sigma>)"
    using pp_e_eval_type[OF App.hyps(2) App.prems(1)]
    by (simp add: pp_e_dom_def)
  have f_commute:
      "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
          (pp_e_eval C \<rho> M) =
       pp_e_eval C \<eta> M"
    by (rule App.IH(1)[OF App.prems])
  have a_commute:
      "pp_b_action \<sigma> i (pp_e_eval C \<rho> N) =
       pp_e_eval C \<eta> N"
    by (rule App.IH(2)[OF App.prems])
  show ?case
    using pp_b_application_substitution_exact[OF f a, of i]
      f_commute a_commute by simp
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have lam_typed:
      "\<Gamma> \<turnstile> Lam \<sigma> M : (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    by (rule has_type.Lam[OF Lam.hyps])
  have source_lam:
      "Elem (pp_e_eval C \<rho> (Lam \<sigma> M))
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using pp_e_eval_type[OF lam_typed Lam.prems(1)]
    by (simp add: pp_e_dom_def)
  have target_env: "pp_e_env_typed \<Gamma> \<eta>"
    by (rule pp_e_env_action_target_typed[OF Lam.prems])
  have target_lam:
      "Elem (pp_e_eval C \<eta> (Lam \<sigma> M))
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using pp_e_eval_type[OF lam_typed target_env]
    by (simp add: pp_e_dom_def)
  have acted:
      "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
        (pp_e_eval C \<rho> (Lam \<sigma> M)))
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_action_closed_all[OF source_lam])
  show ?case
  proof (rule pp_b_function_ext[
      OF pp_b_arrow_member_function[OF acted]
         pp_b_arrow_member_function[OF target_lam]])
    fix a
    assume a: "Elem a (pp_e_domain \<sigma>)"
    let ?x = "pp_b_lift \<sigma> i a"
    have x: "Elem ?x (pp_e_domain \<sigma>)"
      by (rule pp_b_structure_lift_closed[
          OF pp_b_mset_structure_all a])
    have ax: "pp_b_action \<sigma> i ?x = a"
      by (rule pp_b_structure_action_lift[
          OF pp_b_mset_structure_all a])
    have source_ext:
        "pp_e_env_typed (\<sigma> # \<Gamma>) (extend_env ?x \<rho>)"
      by (rule pp_e_env_typed_extend[OF Lam.prems(1) x])
    have rel_ext:
        "pp_e_env_action (\<sigma> # \<Gamma>) i
          (extend_env ?x \<rho>) (extend_env a \<eta>)"
      by (rule pp_e_env_action_extend[
          where b=a and \<sigma>=\<sigma> and a="?x",
          OF Lam.prems(2) ax[symmetric]])
    have body:
        "pp_b_action \<tau> i
          (pp_e_eval C (extend_env ?x \<rho>) M) =
         pp_e_eval C (extend_env a \<eta>) M"
      by (rule Lam.IH[OF source_ext rel_ext])
    show "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
          (pp_e_eval C \<rho> (Lam \<sigma> M)) \<acute> a =
        pp_e_eval C \<eta> (Lam \<sigma> M) \<acute> a"
      using pp_b_arrow_action_apply[
          OF a, of \<tau> i "pp_e_eval C \<rho> (Lam \<sigma> M)"]
        x a body
      by (simp add: Lambda_app)
  qed
next
  case (Eq \<Gamma> M \<sigma> N)
  have Mx: "Elem (pp_e_eval C \<rho> M) (pp_e_domain \<sigma>)"
    using pp_e_eval_type[OF Eq.hyps(1) Eq.prems(1)]
    by (simp add: pp_e_dom_def)
  have Nx: "Elem (pp_e_eval C \<rho> N) (pp_e_domain \<sigma>)"
    using pp_e_eval_type[OF Eq.hyps(2) Eq.prems(1)]
    by (simp add: pp_e_dom_def)
  have Mc:
      "pp_b_action \<sigma> i (pp_e_eval C \<rho> M) =
       pp_e_eval C \<eta> M"
    by (rule Eq.IH(1)[OF Eq.prems])
  have Nc:
      "pp_b_action \<sigma> i (pp_e_eval C \<rho> N) =
       pp_e_eval C \<eta> N"
    by (rule Eq.IH(2)[OF Eq.prems])
  have eq_source:
      "Elem (pp_e_eval C \<rho> (Eq \<sigma> M N)) (pp_e_domain Prop)"
    by (simp only: pp_e_eval.simps; rule pp_e_prop_in_domain)
  have left:
      "Elem (pp_b_action Prop i (pp_e_eval C \<rho> (Eq \<sigma> M N)))
        (pp_e_domain Prop)"
    by (rule pp_b_action_closed_all[OF eq_source])
  have right:
      "Elem (pp_e_eval C \<eta> (Eq \<sigma> M N)) (pp_e_domain Prop)"
    by (simp only: pp_e_eval.simps; rule pp_e_prop_in_domain)
  show ?case
  proof (rule pp_e_prop_ext[OF left right])
    fix w
    have local:
        "pp_e_eqv \<sigma> (rev i @ w)
            (pp_e_eval C \<rho> M) (pp_e_eval C \<rho> N)
        \<longleftrightarrow>
         pp_e_eqv \<sigma> w
            (pp_e_eval C \<eta> M) (pp_e_eval C \<eta> N)"
      using pp_e_eqv_action_shift[OF Mx Nx, of i w] Mc Nc
      by simp
    show "pp_e_holds
        (pp_b_action Prop i (pp_e_eval C \<rho> (Eq \<sigma> M N))) w =
      pp_e_holds (pp_e_eval C \<eta> (Eq \<sigma> M N)) w"
      using local by simp
  qed
next
  case (Neg \<Gamma> A)
  have Ac: "pp_b_action Prop i (pp_e_eval C \<rho> A) =
      pp_e_eval C \<eta> A"
    by (rule Neg.IH[OF Neg.prems])
  have Ah: "pp_e_holds (pp_e_eval C \<rho> A) (rev i @ w) =
      pp_e_holds (pp_e_eval C \<eta> A) w" for w
    by (rule pp_e_holds_from_action_eq[OF Ac])
  show ?case
  proof (rule pp_e_prop_ext)
    show "Elem (pp_b_action Prop i (pp_e_eval C \<rho> (Neg A)))
        (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps;
          rule pp_b_action_closed_all[OF pp_e_prop_in_domain])
    show "Elem (pp_e_eval C \<eta> (Neg A)) (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps; rule pp_e_prop_in_domain)
    fix w
    show "pp_e_holds
        (pp_b_action Prop i (pp_e_eval C \<rho> (Neg A))) w =
      pp_e_holds (pp_e_eval C \<eta> (Neg A)) w"
      using Ah[of w] by simp
  qed
next
  case (Conj \<Gamma> A B)
  have Ac: "pp_b_action Prop i (pp_e_eval C \<rho> A) =
      pp_e_eval C \<eta> A"
    by (rule Conj.IH(1)[OF Conj.prems])
  have Bc: "pp_b_action Prop i (pp_e_eval C \<rho> B) =
      pp_e_eval C \<eta> B"
    by (rule Conj.IH(2)[OF Conj.prems])
  have Ah: "pp_e_holds (pp_e_eval C \<rho> A) (rev i @ w) =
      pp_e_holds (pp_e_eval C \<eta> A) w" for w
    by (rule pp_e_holds_from_action_eq[OF Ac])
  have Bh: "pp_e_holds (pp_e_eval C \<rho> B) (rev i @ w) =
      pp_e_holds (pp_e_eval C \<eta> B) w" for w
    by (rule pp_e_holds_from_action_eq[OF Bc])
  show ?case
  proof (rule pp_e_prop_ext)
    show "Elem (pp_b_action Prop i (pp_e_eval C \<rho> (Conj A B)))
        (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps;
          rule pp_b_action_closed_all[OF pp_e_prop_in_domain])
    show "Elem (pp_e_eval C \<eta> (Conj A B)) (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps; rule pp_e_prop_in_domain)
    fix w
    show "pp_e_holds
        (pp_b_action Prop i (pp_e_eval C \<rho> (Conj A B))) w =
      pp_e_holds (pp_e_eval C \<eta> (Conj A B)) w"
      using Ah[of w] Bh[of w] by simp
  qed
next
  case (Disj \<Gamma> A B)
  have Ac: "pp_b_action Prop i (pp_e_eval C \<rho> A) =
      pp_e_eval C \<eta> A"
    by (rule Disj.IH(1)[OF Disj.prems])
  have Bc: "pp_b_action Prop i (pp_e_eval C \<rho> B) =
      pp_e_eval C \<eta> B"
    by (rule Disj.IH(2)[OF Disj.prems])
  have Ah: "pp_e_holds (pp_e_eval C \<rho> A) (rev i @ w) =
      pp_e_holds (pp_e_eval C \<eta> A) w" for w
    by (rule pp_e_holds_from_action_eq[OF Ac])
  have Bh: "pp_e_holds (pp_e_eval C \<rho> B) (rev i @ w) =
      pp_e_holds (pp_e_eval C \<eta> B) w" for w
    by (rule pp_e_holds_from_action_eq[OF Bc])
  show ?case
  proof (rule pp_e_prop_ext)
    show "Elem (pp_b_action Prop i (pp_e_eval C \<rho> (Disj A B)))
        (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps;
          rule pp_b_action_closed_all[OF pp_e_prop_in_domain])
    show "Elem (pp_e_eval C \<eta> (Disj A B)) (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps; rule pp_e_prop_in_domain)
    fix w
    show "pp_e_holds
        (pp_b_action Prop i (pp_e_eval C \<rho> (Disj A B))) w =
      pp_e_holds (pp_e_eval C \<eta> (Disj A B)) w"
      using Ah[of w] Bh[of w] by simp
  qed
next
  case (Imp \<Gamma> A B)
  have Ac: "pp_b_action Prop i (pp_e_eval C \<rho> A) =
      pp_e_eval C \<eta> A"
    by (rule Imp.IH(1)[OF Imp.prems])
  have Bc: "pp_b_action Prop i (pp_e_eval C \<rho> B) =
      pp_e_eval C \<eta> B"
    by (rule Imp.IH(2)[OF Imp.prems])
  have Ah: "pp_e_holds (pp_e_eval C \<rho> A) (rev i @ w) =
      pp_e_holds (pp_e_eval C \<eta> A) w" for w
    by (rule pp_e_holds_from_action_eq[OF Ac])
  have Bh: "pp_e_holds (pp_e_eval C \<rho> B) (rev i @ w) =
      pp_e_holds (pp_e_eval C \<eta> B) w" for w
    by (rule pp_e_holds_from_action_eq[OF Bc])
  show ?case
  proof (rule pp_e_prop_ext)
    show "Elem (pp_b_action Prop i (pp_e_eval C \<rho> (Imp A B)))
        (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps;
          rule pp_b_action_closed_all[OF pp_e_prop_in_domain])
    show "Elem (pp_e_eval C \<eta> (Imp A B)) (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps; rule pp_e_prop_in_domain)
    fix w
    show "pp_e_holds
        (pp_b_action Prop i (pp_e_eval C \<rho> (Imp A B))) w =
      pp_e_holds (pp_e_eval C \<eta> (Imp A B)) w"
      using Ah[of w] Bh[of w] by simp
  qed
next
  case (Forall \<sigma> \<Gamma> A)
  let ?F = "\<lambda>x. pp_e_eval C (extend_env x \<rho>) A"
  let ?G = "\<lambda>a. pp_e_eval C (extend_env a \<eta>) A"
  have target: "pp_e_env_typed \<Gamma> \<eta>"
    by (rule pp_e_env_action_target_typed[OF Forall.prems])
  have F:
      "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
        Elem (?F x) (pp_e_domain Prop)"
    using pp_e_eval_type[OF Forall.hyps]
      pp_e_env_typed_extend[OF Forall.prems(1)]
    by (simp add: pp_e_dom_def)
  have G:
      "\<And>a. Elem a (pp_e_domain \<sigma>) \<Longrightarrow>
        Elem (?G a) (pp_e_domain Prop)"
    using pp_e_eval_type[OF Forall.hyps]
      pp_e_env_typed_extend[OF target]
    by (simp add: pp_e_dom_def)
  have commute:
      "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
        pp_b_action Prop i (?F x) =
          ?G (pp_b_action \<sigma> i x)"
  proof -
    fix x
    assume x: "Elem x (pp_e_domain \<sigma>)"
    have ax: "Elem (pp_b_action \<sigma> i x) (pp_e_domain \<sigma>)"
      by (rule pp_b_action_closed_all[OF x])
    have source_ext:
        "pp_e_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
      by (rule pp_e_env_typed_extend[OF Forall.prems(1) x])
    have rel_ext:
        "pp_e_env_action (\<sigma> # \<Gamma>) i
          (extend_env x \<rho>)
          (extend_env (pp_b_action \<sigma> i x) \<eta>)"
      by (rule pp_e_env_action_extend[OF Forall.prems(2)]) simp
    show "pp_b_action Prop i (?F x) =
        ?G (pp_b_action \<sigma> i x)"
      by (rule Forall.IH[OF source_ext rel_ext])
  qed
  show ?case
  proof -
    note quant = pp_e_action_bounded_forall[
      where F="\<lambda>x. pp_e_eval C (extend_env x \<rho>) A"
        and G="\<lambda>a. pp_e_eval C (extend_env a \<eta>) A"
        and \<sigma>=\<sigma> and i=i,
      OF F G commute]
    show ?thesis using quant by simp
  qed
next
  case (Exists \<sigma> \<Gamma> A)
  let ?F = "\<lambda>x. pp_e_eval C (extend_env x \<rho>) A"
  let ?G = "\<lambda>a. pp_e_eval C (extend_env a \<eta>) A"
  have target: "pp_e_env_typed \<Gamma> \<eta>"
    by (rule pp_e_env_action_target_typed[OF Exists.prems])
  have F:
      "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
        Elem (?F x) (pp_e_domain Prop)"
    using pp_e_eval_type[OF Exists.hyps]
      pp_e_env_typed_extend[OF Exists.prems(1)]
    by (simp add: pp_e_dom_def)
  have G:
      "\<And>a. Elem a (pp_e_domain \<sigma>) \<Longrightarrow>
        Elem (?G a) (pp_e_domain Prop)"
    using pp_e_eval_type[OF Exists.hyps]
      pp_e_env_typed_extend[OF target]
    by (simp add: pp_e_dom_def)
  have commute:
      "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
        pp_b_action Prop i (?F x) =
          ?G (pp_b_action \<sigma> i x)"
  proof -
    fix x
    assume x: "Elem x (pp_e_domain \<sigma>)"
    have source_ext:
        "pp_e_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
      by (rule pp_e_env_typed_extend[OF Exists.prems(1) x])
    have rel_ext:
        "pp_e_env_action (\<sigma> # \<Gamma>) i
          (extend_env x \<rho>)
          (extend_env (pp_b_action \<sigma> i x) \<eta>)"
      by (rule pp_e_env_action_extend[OF Exists.prems(2)]) simp
    show "pp_b_action Prop i (?F x) =
        ?G (pp_b_action \<sigma> i x)"
      by (rule Exists.IH[OF source_ext rel_ext])
  qed
  show ?case
  proof -
    note quant = pp_e_action_bounded_exists[
      where F="\<lambda>x. pp_e_eval C (extend_env x \<rho>) A"
        and G="\<lambda>a. pp_e_eval C (extend_env a \<eta>) A"
        and \<sigma>=\<sigma> and i=i,
      OF F G commute]
    show ?thesis using quant by simp
  qed
qed

end

lemma pp_e_default_constants_action:
  "pp_b_action \<sigma> i (pp_e_default_constants c \<sigma>) =
    pp_e_default_constants c \<sigma>"
  unfolding pp_e_default_constants_def
  by (rule pp_b_structure_action_default[OF pp_b_mset_structure_all])

interpretation DefaultExactBaconEquivariant:
  pp_e_equivariant_constants pp_e_default_constants
  by standard
    (rule pp_e_default_constants_action)

lemma pp_e_closed_env_action:
  "pp_e_env_action [] i pp_e_closed_env pp_e_closed_env"
  by (simp add: pp_e_env_action_def lookup_def)

end
