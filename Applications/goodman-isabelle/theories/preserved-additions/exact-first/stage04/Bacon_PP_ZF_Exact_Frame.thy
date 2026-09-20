theory Bacon_PP_ZF_Exact_Frame
  imports 
    "Goodman_Exact_Legacy_02.Bacon_PP_ZF_Full_MSet"
    "Goodman_Exact_Legacy_03.Bacon_PP_Axiom_Soundness"
    "Goodman_Exact_Legacy_03.Bacon_PP_Purity_Operator"
begin

section \<open>Bacon's exact all-type HOL-ZF interpretation\<close>

text \<open>
  The carriers in this theory are literally Bacon's recursively restricted
  function spaces \<open>pp_b_domain\<close>.  Local identity at prefix-world \<open>w\<close>
  is connected below with equality after Bacon's division action by
  \<open>rev w\<close>.
\<close>

abbreviation pp_e_domain :: "otype \<Rightarrow> ZF" where
  "pp_e_domain \<sigma> \<equiv> pp_b_domain \<sigma>"

abbreviation pp_e_default :: "otype \<Rightarrow> ZF" where
  "pp_e_default \<sigma> \<equiv> pp_b_default \<sigma>"

abbreviation pp_e_holds :: "ZF \<Rightarrow> nat list \<Rightarrow> bool" where
  "pp_e_holds P w \<equiv> pp_n_holds P w"

abbreviation pp_e_prop :: "(nat list \<Rightarrow> bool) \<Rightarrow> ZF" where
  "pp_e_prop Q \<equiv> pp_n_prop Q"

lemma pp_e_prop_in_power:
  "Elem (pp_e_prop Q) (Power Nat)"
  by (rule pp_n_prop_in_power)

lemma pp_e_prop_in_domain:
  "Elem (pp_e_prop Q) (pp_e_domain Prop)"
  using pp_e_prop_in_power by simp

lemma pp_e_default_in_domain:
  "Elem (pp_e_default \<sigma>) (pp_e_domain \<sigma>)"
  by (rule pp_b_default_in_domain)

theorem pp_e_domain_nonempty:
  "\<exists>x. Elem x (pp_e_domain \<sigma>)"
  using pp_e_default_in_domain by blast

fun pp_e_eqv ::
    "otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> bool"
where
  "pp_e_eqv Ind w x y = (x = y)"
| "pp_e_eqv Prop w P Q =
    (\<forall>v. prefix w v \<longrightarrow>
      (pp_e_holds P v \<longleftrightarrow> pp_e_holds Q v))"
| "pp_e_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g =
    (\<forall>v. prefix w v \<longrightarrow> (\<forall>x y.
      Elem x (pp_e_domain \<sigma>) \<longrightarrow>
      Elem y (pp_e_domain \<sigma>) \<longrightarrow>
      pp_e_eqv \<sigma> v x y \<longrightarrow>
      pp_e_eqv \<tau> v (f \<acute> x) (g \<acute> y)))"

lemma pp_e_action_at_extension:
  assumes x: "Elem x (pp_e_domain \<sigma>)"
    and v: "v = w @ u"
  shows "pp_b_action \<sigma> (rev u)
      (pp_b_action \<sigma> (rev w) x) =
    pp_b_action \<sigma> (rev v) x"
  using pp_b_action_comp_all[OF x, of "rev u" "rev w"] v
  by (simp add: rev_append)

theorem pp_e_eqv_iff_action_eq:
  assumes x: "Elem x (pp_e_domain \<sigma>)"
    and y: "Elem y (pp_e_domain \<sigma>)"
  shows "pp_e_eqv \<sigma> w x y \<longleftrightarrow>
    pp_b_action \<sigma> (rev w) x =
      pp_b_action \<sigma> (rev w) y"
  using x y
proof (induction \<sigma> arbitrary: w x y)
  case Ind
  then show ?case by simp
next
  case Prop
  show ?case
  proof
    assume rel: "pp_e_eqv Prop w x y"
    have ax: "Elem (pp_b_action Prop (rev w) x) (pp_e_domain Prop)"
      by (rule pp_b_action_closed_all[OF Prop.prems(1)])
    have ay: "Elem (pp_b_action Prop (rev w) y) (pp_e_domain Prop)"
      by (rule pp_b_action_closed_all[OF Prop.prems(2)])
    have ax_n: "Elem (pp_b_action Prop (rev w) x) (Power Nat)"
      using ax by simp
    have ay_n: "Elem (pp_b_action Prop (rev w) y) (Power Nat)"
      using ay by simp
    show "pp_b_action Prop (rev w) x =
        pp_b_action Prop (rev w) y"
    proof (rule pp_n_bacon_extract_injective_on_domain[OF ax_n ay_n])
      show "pp_n_bacon_extract (pp_b_action Prop (rev w) x) =
          pp_n_bacon_extract (pp_b_action Prop (rev w) y)"
      proof (rule set_eqI)
        fix i
        have future: "prefix w (w @ rev i)"
          by (simp add: prefix_def)
        have same:
            "pp_e_holds x (w @ rev i) =
             pp_e_holds y (w @ rev i)"
          using rel future by simp
        show "i \<in> pp_n_bacon_extract
                (pp_b_action Prop (rev w) x) \<longleftrightarrow>
              i \<in> pp_n_bacon_extract
                (pp_b_action Prop (rev w) y)"
          using same
          by (simp add: pp_n_bacon_extract_def rev_append)
      qed
    qed
  next
    assume same:
        "pp_b_action Prop (rev w) x =
         pp_b_action Prop (rev w) y"
    show "pp_e_eqv Prop w x y"
    proof (simp only: pp_e_eqv.simps, intro allI impI)
      fix v
      assume future: "prefix w v"
      then obtain u where v: "v = w @ u"
        by (auto simp: prefix_def)
      have shifted:
          "pp_b_action Prop (rev v) x =
           pp_b_action Prop (rev v) y"
        using arg_cong[OF same, where f="pp_b_action Prop (rev u)"]
          pp_e_action_at_extension[OF Prop.prems(1) v]
          pp_e_action_at_extension[OF Prop.prems(2) v]
        by simp
      have root:
          "pp_e_holds (pp_b_action Prop (rev v) x) [] =
           pp_e_holds (pp_b_action Prop (rev v) y) []"
        using shifted by simp
      show "pp_e_holds x v = pp_e_holds y v"
        using root by simp
    qed
  qed
next
  case (Arr \<sigma> \<tau>)
  show ?case
  proof
    assume rel: "pp_e_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w x y"
    have ax:
        "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (rev w) x)
          (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      by (rule pp_b_action_closed_all[OF Arr.prems(1)])
    have ay:
        "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (rev w) y)
          (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      by (rule pp_b_action_closed_all[OF Arr.prems(2)])
    show "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (rev w) x =
        pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (rev w) y"
    proof (rule pp_b_function_ext[
        OF pp_b_arrow_member_function[OF ax]
           pp_b_arrow_member_function[OF ay]])
      fix a
      assume a: "Elem a (pp_e_domain \<sigma>)"
      have lift: "Elem (pp_b_lift \<sigma> (rev w) a) (pp_e_domain \<sigma>)"
        by (rule pp_b_structure_lift_closed[
            OF pp_b_mset_structure_all a])
      have lift_action:
          "pp_b_action \<sigma> (rev w)
              (pp_b_lift \<sigma> (rev w) a) = a"
        by (rule pp_b_structure_action_lift[
            OF pp_b_mset_structure_all a])
      have lift_rel:
          "pp_e_eqv \<sigma> w
            (pp_b_lift \<sigma> (rev w) a)
            (pp_b_lift \<sigma> (rev w) a)"
        using Arr.IH(1)[OF lift lift, of w] lift_action by simp
      have out_rel:
          "pp_e_eqv \<tau> w
            (x \<acute> pp_b_lift \<sigma> (rev w) a)
            (y \<acute> pp_b_lift \<sigma> (rev w) a)"
        using rel lift lift lift_rel by simp
      have out_x:
          "Elem (x \<acute> pp_b_lift \<sigma> (rev w) a)
            (pp_e_domain \<tau>)"
        by (rule pp_b_app_closed[OF Arr.prems(1) lift])
      have out_y:
          "Elem (y \<acute> pp_b_lift \<sigma> (rev w) a)
            (pp_e_domain \<tau>)"
        by (rule pp_b_app_closed[OF Arr.prems(2) lift])
      have out_action:
          "pp_b_action \<tau> (rev w)
              (x \<acute> pp_b_lift \<sigma> (rev w) a) =
           pp_b_action \<tau> (rev w)
              (y \<acute> pp_b_lift \<sigma> (rev w) a)"
        using Arr.IH(2)[OF out_x out_y, of w] out_rel by simp
      show "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (rev w) x
              \<acute> a =
            pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (rev w) y
              \<acute> a"
        using pp_b_arrow_action_apply[OF a, of \<tau> "rev w" x]
          pp_b_arrow_action_apply[OF a, of \<tau> "rev w" y]
          out_action by simp
    qed
  next
    assume same:
        "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (rev w) x =
         pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (rev w) y"
    show "pp_e_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w x y"
    proof (simp only: pp_e_eqv.simps, intro allI impI)
      fix v a b
      assume future: "prefix w v"
        and a: "Elem a (pp_e_domain \<sigma>)"
        and b: "Elem b (pp_e_domain \<sigma>)"
        and ab: "pp_e_eqv \<sigma> v a b"
      then obtain u where v: "v = w @ u"
        by (auto simp: prefix_def)
      have shifted:
          "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (rev v) x =
           pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (rev v) y"
        using arg_cong[OF same,
          where f="pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (rev u)"]
          pp_e_action_at_extension[OF Arr.prems(1) v]
          pp_e_action_at_extension[OF Arr.prems(2) v]
        by simp
      have aa:
          "pp_b_action \<sigma> (rev v) a =
           pp_b_action \<sigma> (rev v) b"
        using Arr.IH(1)[OF a b, of v] ab by simp
      have fa: "Elem (x \<acute> a) (pp_e_domain \<tau>)"
        by (rule pp_b_app_closed[OF Arr.prems(1) a])
      have gb: "Elem (y \<acute> b) (pp_e_domain \<tau>)"
        by (rule pp_b_app_closed[OF Arr.prems(2) b])
      have out_eq:
          "pp_b_action \<tau> (rev v) (x \<acute> a) =
           pp_b_action \<tau> (rev v) (y \<acute> b)"
        using shifted aa
          pp_b_application_substitution_exact[OF Arr.prems(1) a, of "rev v"]
          pp_b_application_substitution_exact[OF Arr.prems(2) b, of "rev v"]
        by simp
      show "pp_e_eqv \<tau> v (x \<acute> a) (y \<acute> b)"
        using Arr.IH(2)[OF fa gb, of v] out_eq by simp
    qed
  qed
qed

lemma pp_e_eqv_reflexive:
  "Elem x (pp_e_domain \<sigma>) \<Longrightarrow> pp_e_eqv \<sigma> w x x"
  using pp_e_eqv_iff_action_eq by simp

lemma pp_e_eqv_symmetric:
  assumes "Elem x (pp_e_domain \<sigma>)"
    "Elem y (pp_e_domain \<sigma>)" "pp_e_eqv \<sigma> w x y"
  shows "pp_e_eqv \<sigma> w y x"
  using assms pp_e_eqv_iff_action_eq by metis

lemma pp_e_eqv_transitive:
  assumes "Elem x (pp_e_domain \<sigma>)" "Elem y (pp_e_domain \<sigma>)"
    "Elem z (pp_e_domain \<sigma>)" "pp_e_eqv \<sigma> w x y"
    "pp_e_eqv \<sigma> w y z"
  shows "pp_e_eqv \<sigma> w x z"
  using assms pp_e_eqv_iff_action_eq by metis

lemma pp_e_eqv_persistent_typed:
  assumes x: "Elem x (pp_e_domain \<sigma>)"
    and y: "Elem y (pp_e_domain \<sigma>)"
    and eqv: "pp_e_eqv \<sigma> w x y"
    and future: "prefix w v"
  shows "pp_e_eqv \<sigma> v x y"
proof -
  obtain u where v: "v = w @ u"
    using future by (auto simp: prefix_def)
  have same:
      "pp_b_action \<sigma> (rev w) x =
       pp_b_action \<sigma> (rev w) y"
    using pp_e_eqv_iff_action_eq[OF x y] eqv by simp
  have shifted:
      "pp_b_action \<sigma> (rev v) x =
       pp_b_action \<sigma> (rev v) y"
    using arg_cong[OF same, where f="pp_b_action \<sigma> (rev u)"]
      pp_e_action_at_extension[OF x v]
      pp_e_action_at_extension[OF y v]
    by simp
  show ?thesis
    using pp_e_eqv_iff_action_eq[OF x y, of v] shifted by simp
qed

lemma pp_e_eqv_persistent:
  assumes eqv: "pp_e_eqv \<sigma> w x y"
    and future: "prefix w v"
  shows "pp_e_eqv \<sigma> v x y"
  using eqv future
proof (induction \<sigma> arbitrary: w v x y)
  case Ind
  then show ?case by simp
next
  case Prop
  then show ?case
    using prefix_order.trans by auto
next
  case (Arr \<sigma> \<tau>)
  then show ?case
    using prefix_order.trans by auto
qed

lemma pp_e_app_closed:
  assumes "Elem f (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    "Elem x (pp_e_domain \<sigma>)"
  shows "Elem (f \<acute> x) (pp_e_domain \<tau>)"
  using assms by (rule pp_b_app_closed)

lemma pp_e_app_respects:
  assumes "pp_e_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w f g"
    "Elem x (pp_e_domain \<sigma>)" "Elem y (pp_e_domain \<sigma>)"
    "pp_e_eqv \<sigma> w x y"
  shows "pp_e_eqv \<tau> w (f \<acute> x) (g \<acute> y)"
  using assms by simp

section \<open>Structural denotation on the branching frame\<close>

fun pp_e_eval ::
    "(string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow>
      (nat \<Rightarrow> ZF) \<Rightarrow> oterm \<Rightarrow> ZF" where
  "pp_e_eval C \<rho> (Var n) = \<rho> n"
| "pp_e_eval C \<rho> (Const c \<sigma>) = C c \<sigma>"
| "pp_e_eval C \<rho> (App M N) =
    (pp_e_eval C \<rho> M) \<acute> (pp_e_eval C \<rho> N)"
| "pp_e_eval C \<rho> (Lam \<sigma> M) =
    Lambda (pp_e_domain \<sigma>)
      (\<lambda>x. pp_e_eval C (extend_env x \<rho>) M)"
| "pp_e_eval C \<rho> (Eq \<sigma> M N) =
    pp_e_prop (\<lambda>w.
      pp_e_eqv \<sigma> w (pp_e_eval C \<rho> M) (pp_e_eval C \<rho> N))"
| "pp_e_eval C \<rho> (Neg A) =
    pp_e_prop (\<lambda>w. \<not> pp_e_holds (pp_e_eval C \<rho> A) w)"
| "pp_e_eval C \<rho> (Conj A B) =
    pp_e_prop (\<lambda>w.
      pp_e_holds (pp_e_eval C \<rho> A) w \<and>
      pp_e_holds (pp_e_eval C \<rho> B) w)"
| "pp_e_eval C \<rho> (Disj A B) =
    pp_e_prop (\<lambda>w.
      pp_e_holds (pp_e_eval C \<rho> A) w \<or>
      pp_e_holds (pp_e_eval C \<rho> B) w)"
| "pp_e_eval C \<rho> (Imp A B) =
    pp_e_prop (\<lambda>w.
      pp_e_holds (pp_e_eval C \<rho> A) w \<longrightarrow>
      pp_e_holds (pp_e_eval C \<rho> B) w)"
| "pp_e_eval C \<rho> (Forall \<sigma> A) =
    pp_e_prop (\<lambda>w.
      \<forall>x. Elem x (pp_e_domain \<sigma>) \<longrightarrow>
        pp_e_holds (pp_e_eval C (extend_env x \<rho>) A) w)"
| "pp_e_eval C \<rho> (Exists \<sigma> A) =
    pp_e_prop (\<lambda>w.
      \<exists>x. Elem x (pp_e_domain \<sigma>) \<and>
        pp_e_holds (pp_e_eval C (extend_env x \<rho>) A) w)"

lemma pp_e_eval_Eq_holds[simp]:
  "pp_e_holds (pp_e_eval C \<rho> (Eq \<sigma> M N)) w \<longleftrightarrow>
    pp_e_eqv \<sigma> w (pp_e_eval C \<rho> M) (pp_e_eval C \<rho> N)"
  by simp

lemma pp_e_eval_Neg_holds[simp]:
  "pp_e_holds (pp_e_eval C \<rho> (Neg A)) w \<longleftrightarrow>
    \<not> pp_e_holds (pp_e_eval C \<rho> A) w"
  by simp

lemma pp_e_eval_Conj_holds[simp]:
  "pp_e_holds (pp_e_eval C \<rho> (Conj A B)) w \<longleftrightarrow>
    pp_e_holds (pp_e_eval C \<rho> A) w \<and>
    pp_e_holds (pp_e_eval C \<rho> B) w"
  by simp

lemma pp_e_eval_Disj_holds[simp]:
  "pp_e_holds (pp_e_eval C \<rho> (Disj A B)) w \<longleftrightarrow>
    pp_e_holds (pp_e_eval C \<rho> A) w \<or>
    pp_e_holds (pp_e_eval C \<rho> B) w"
  by simp

lemma pp_e_eval_Imp_holds[simp]:
  "pp_e_holds (pp_e_eval C \<rho> (Imp A B)) w \<longleftrightarrow>
    (pp_e_holds (pp_e_eval C \<rho> A) w \<longrightarrow>
      pp_e_holds (pp_e_eval C \<rho> B) w)"
  by simp

lemma pp_e_eval_Forall_holds[simp]:
  "pp_e_holds (pp_e_eval C \<rho> (Forall \<sigma> A)) w \<longleftrightarrow>
    (\<forall>x. Elem x (pp_e_domain \<sigma>) \<longrightarrow>
      pp_e_holds (pp_e_eval C (extend_env x \<rho>) A) w)"
  by simp

lemma pp_e_eval_Exists_holds[simp]:
  "pp_e_holds (pp_e_eval C \<rho> (Exists \<sigma> A)) w \<longleftrightarrow>
    (\<exists>x. Elem x (pp_e_domain \<sigma>) \<and>
      pp_e_holds (pp_e_eval C (extend_env x \<rho>) A) w)"
  by simp

lemma pp_e_prop_eqv_truth_iff:
  "pp_e_eqv Prop w P (pp_zf_truth True) \<longleftrightarrow>
    (\<forall>v. prefix w v \<longrightarrow> pp_e_holds P v)"
  by simp

lemma pp_e_eval_ObjTrue:
  "pp_e_eval C \<rho> ObjTrue = pp_zf_truth True"
  unfolding ObjTrue_def
  apply simp
  unfolding pp_zf_truth_def pp_n_prop_def pp_zf_prop_def
  apply (subst Ext)
  by (auto simp: Sep Elem_nat2Nat_Nat)

lemma pp_e_eval_ObjBox_holds:
  "pp_e_holds (pp_e_eval C \<rho> (\<box>\<^sub>o A)) w
    \<longleftrightarrow>
    pp_e_eqv Prop w (pp_e_eval C \<rho> A) (pp_zf_truth True)"
  by (simp add: ObjBox_def pp_e_eval_ObjTrue)

lemma pp_e_three_extensions_index_two[simp]:
  "extend_env q (extend_env r (extend_env X \<rho>)) 2 = X"
  by (simp add: numeral_2_eq_2)

definition pp_e_env_typed ::
    "ctx \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> bool" where
  "pp_e_env_typed \<Gamma> \<rho> \<longleftrightarrow>
    (\<forall>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<longrightarrow>
      Elem (\<rho> n) (pp_e_domain \<sigma>))"

definition pp_e_env_eqv ::
    "nat list \<Rightarrow> ctx \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow>
      (nat \<Rightarrow> ZF) \<Rightarrow> bool" where
  "pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longleftrightarrow>
    pp_e_env_typed \<Gamma> \<rho> \<and>
    pp_e_env_typed \<Gamma> \<eta> \<and>
    (\<forall>n \<sigma>. lookup \<Gamma> n = Some \<sigma> \<longrightarrow>
      pp_e_eqv \<sigma> w (\<rho> n) (\<eta> n))"

lemma pp_e_env_typed_lookup:
  assumes env: "pp_e_env_typed \<Gamma> \<rho>"
    and lookup: "lookup \<Gamma> n = Some \<sigma>"
  shows "Elem (\<rho> n) (pp_e_domain \<sigma>)"
  using env lookup unfolding pp_e_env_typed_def by blast

lemma pp_e_env_typed_extend:
  assumes env: "pp_e_env_typed \<Gamma> \<rho>"
    and x: "Elem x (pp_e_domain \<sigma>)"
  shows "pp_e_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
proof (unfold pp_e_env_typed_def, intro allI impI)
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "Elem (extend_env x \<rho> n) (pp_e_domain \<tau>)"
  proof (cases n)
    case 0
    then have "\<tau> = \<sigma>"
      using lookup by simp
    then show ?thesis
      using 0 x by simp
  next
    case (Suc m)
    then have "lookup \<Gamma> m = Some \<tau>"
      using lookup by simp
    then have "Elem (\<rho> m) (pp_e_domain \<tau>)"
      using pp_e_env_typed_lookup[OF env] by blast
    then show ?thesis
      using Suc by simp
  qed
qed

lemma pp_e_env_eqv_typed_left:
  "pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<Longrightarrow> pp_e_env_typed \<Gamma> \<rho>"
  unfolding pp_e_env_eqv_def by blast

lemma pp_e_env_eqv_typed_right:
  "pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<Longrightarrow> pp_e_env_typed \<Gamma> \<eta>"
  unfolding pp_e_env_eqv_def by blast

lemma pp_e_env_eqv_lookup:
  assumes env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
    and lookup: "lookup \<Gamma> n = Some \<sigma>"
  shows "pp_e_eqv \<sigma> w (\<rho> n) (\<eta> n)"
  using env lookup unfolding pp_e_env_eqv_def by blast

lemma pp_e_env_eqv_refl:
  assumes env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_env_eqv w \<Gamma> \<rho> \<rho>"
proof (unfold pp_e_env_eqv_def, intro conjI allI impI)
  show "pp_e_env_typed \<Gamma> \<rho>"
    using env .
  show "pp_e_env_typed \<Gamma> \<rho>"
    using env .
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  have "Elem (\<rho> n) (pp_e_domain \<sigma>)"
    using pp_e_env_typed_lookup[OF env lookup] .
  then show "pp_e_eqv \<sigma> w (\<rho> n) (\<rho> n)"
    by (rule pp_e_eqv_reflexive)
qed

lemma pp_e_env_eqv_persistent:
  assumes env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
    and future: "prefix w v"
  shows "pp_e_env_eqv v \<Gamma> \<rho> \<eta>"
proof (unfold pp_e_env_eqv_def, intro conjI allI impI)
  show "pp_e_env_typed \<Gamma> \<rho>"
    using pp_e_env_eqv_typed_left[OF env] .
  show "pp_e_env_typed \<Gamma> \<eta>"
    using pp_e_env_eqv_typed_right[OF env] .
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  have "pp_e_eqv \<sigma> w (\<rho> n) (\<eta> n)"
    using pp_e_env_eqv_lookup[OF env lookup] .
  then show "pp_e_eqv \<sigma> v (\<rho> n) (\<eta> n)"
    using future by (rule pp_e_eqv_persistent)
qed

lemma pp_e_env_eqv_extend:
  assumes env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
    and x: "Elem x (pp_e_domain \<sigma>)"
    and y: "Elem y (pp_e_domain \<sigma>)"
    and xy: "pp_e_eqv \<sigma> w x y"
  shows "pp_e_env_eqv w (\<sigma> # \<Gamma>)
    (extend_env x \<rho>) (extend_env y \<eta>)"
proof (unfold pp_e_env_eqv_def, intro conjI allI impI)
  show "pp_e_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
    using pp_e_env_typed_extend[OF pp_e_env_eqv_typed_left[OF env] x] .
  show "pp_e_env_typed (\<sigma> # \<Gamma>) (extend_env y \<eta>)"
    using pp_e_env_typed_extend[OF pp_e_env_eqv_typed_right[OF env] y] .
  fix n \<tau>
  assume lookup: "lookup (\<sigma> # \<Gamma>) n = Some \<tau>"
  show "pp_e_eqv \<tau> w
      (extend_env x \<rho> n) (extend_env y \<eta> n)"
  proof (cases n)
    case 0
    then have "\<tau> = \<sigma>"
      using lookup by simp
    then show ?thesis
      using 0 xy by simp
  next
    case (Suc m)
    then have "lookup \<Gamma> m = Some \<tau>"
      using lookup by simp
    then have "pp_e_eqv \<tau> w (\<rho> m) (\<eta> m)"
      using pp_e_env_eqv_lookup[OF env] by blast
    then show ?thesis
      using Suc by simp
  qed
qed

lemma pp_e_lambda_closed:
  assumes typed:
      "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
        Elem (F x) (pp_e_domain \<tau>)"
    and respects:
      "\<And>w x y. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
        Elem y (pp_e_domain \<sigma>) \<Longrightarrow>
        pp_e_eqv \<sigma> w x y \<Longrightarrow>
        pp_e_eqv \<tau> w (F x) (F y)"
  shows "Elem (Lambda (pp_e_domain \<sigma>) F)
    (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
proof (simp only: pp_b_arrow_domain_iff, intro conjI)
  show "Elem (Lambda (pp_e_domain \<sigma>) F)
      (Fun (pp_e_domain \<sigma>) (pp_e_domain \<tau>))"
    using typed by (simp add: Elem_Lambda_Fun)
  show "\<forall>i x y.
      Elem x (pp_e_domain \<sigma>) \<longrightarrow>
      Elem y (pp_e_domain \<sigma>) \<longrightarrow>
      pp_b_action \<sigma> i x = pp_b_action \<sigma> i y \<longrightarrow>
      pp_b_action \<tau> i
        (Lambda (pp_e_domain \<sigma>) F \<acute> x) =
      pp_b_action \<tau> i
        (Lambda (pp_e_domain \<sigma>) F \<acute> y)"
  proof (intro allI impI)
    fix i x y
    assume x: "Elem x (pp_e_domain \<sigma>)"
      and y: "Elem y (pp_e_domain \<sigma>)"
      and same: "pp_b_action \<sigma> i x = pp_b_action \<sigma> i y"
    have xy: "pp_e_eqv \<sigma> (rev i) x y"
      using pp_e_eqv_iff_action_eq[OF x y, of "rev i"] same by simp
    have Fxy: "pp_e_eqv \<tau> (rev i) (F x) (F y)"
      by (rule respects[OF x y xy])
    have Fx: "Elem (F x) (pp_e_domain \<tau>)"
      by (rule typed[OF x])
    have Fy: "Elem (F y) (pp_e_domain \<tau>)"
      by (rule typed[OF y])
    show "pp_b_action \<tau> i
          (Lambda (pp_e_domain \<sigma>) F \<acute> x) =
        pp_b_action \<tau> i
          (Lambda (pp_e_domain \<sigma>) F \<acute> y)"
      using pp_e_eqv_iff_action_eq[OF Fx Fy, of "rev i"] Fxy x y
      by (simp add: Lambda_app)
  qed
qed

lemma pp_e_eqv_congruence:
  assumes x: "Elem x (pp_e_domain \<sigma>)"
    and x': "Elem x' (pp_e_domain \<sigma>)"
    and y: "Elem y (pp_e_domain \<sigma>)"
    and y': "Elem y' (pp_e_domain \<sigma>)"
    and xx': "pp_e_eqv \<sigma> w x x'"
    and yy': "pp_e_eqv \<sigma> w y y'"
  shows "pp_e_eqv \<sigma> w x y \<longleftrightarrow>
    pp_e_eqv \<sigma> w x' y'"
proof
  assume xy: "pp_e_eqv \<sigma> w x y"
  have x'x: "pp_e_eqv \<sigma> w x' x"
    using pp_e_eqv_symmetric[OF x x' xx'] .
  have x'y: "pp_e_eqv \<sigma> w x' y"
    using pp_e_eqv_transitive[OF x' x y x'x xy] .
  show "pp_e_eqv \<sigma> w x' y'"
    using pp_e_eqv_transitive[OF x' y y' x'y yy'] .
next
  assume x'y': "pp_e_eqv \<sigma> w x' y'"
  have y'y: "pp_e_eqv \<sigma> w y' y"
    using pp_e_eqv_symmetric[OF y y' yy'] .
  have xy': "pp_e_eqv \<sigma> w x y'"
    using pp_e_eqv_transitive[OF x x' y' xx' x'y'] .
  show "pp_e_eqv \<sigma> w x y"
    using pp_e_eqv_transitive[OF x y' y xy' y'y] .
qed

lemma pp_e_prop_eqv_pp_e_prop_iff:
  "pp_e_eqv Prop w (pp_e_prop P) (pp_e_prop Q) \<longleftrightarrow>
    (\<forall>v. prefix w v \<longrightarrow> (P v \<longleftrightarrow> Q v))"
  by simp

lemma pp_e_prop_eqv_at:
  assumes PQ: "pp_e_eqv Prop w P Q"
    and future: "prefix w v"
  shows "pp_e_holds P v \<longleftrightarrow> pp_e_holds Q v"
  using PQ future by simp

definition pp_e_dom :: "otype \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_e_dom \<sigma> x \<longleftrightarrow> Elem x (pp_e_domain \<sigma>)"

lemma pp_e_eval_rename:
  "pp_e_eval C \<rho> (rename r M) =
    pp_e_eval C (\<lambda>n. \<rho> (r n)) M"
proof (induction M arbitrary: \<rho> r)
  case (Lam \<sigma> M)
  have env_eq:
      "(\<lambda>n. extend_env x \<rho> (lift_ren r n)) =
        extend_env x (\<lambda>n. \<rho> (r n))" for x
    by (rule ext) (case_tac n; simp)
  show ?case
    using Lam.IH[of "extend_env x \<rho>" "lift_ren r" for x]
    by (simp add: env_eq)
next
  case (Forall \<sigma> M)
  have env_eq:
      "(\<lambda>n. extend_env x \<rho> (lift_ren r n)) =
        extend_env x (\<lambda>n. \<rho> (r n))" for x
    by (rule ext) (case_tac n; simp)
  show ?case
    using Forall.IH[of "extend_env x \<rho>" "lift_ren r" for x]
    by (simp add: env_eq)
next
  case (Exists \<sigma> M)
  have env_eq:
      "(\<lambda>n. extend_env x \<rho> (lift_ren r n)) =
        extend_env x (\<lambda>n. \<rho> (r n))" for x
    by (rule ext) (case_tac n; simp)
  show ?case
    using Exists.IH[of "extend_env x \<rho>" "lift_ren r" for x]
    by (simp add: env_eq)
qed (simp_all add: fun_eq_iff)

lemma pp_e_eval_shift:
  "pp_e_eval C (extend_env x \<rho>) (shift M) = pp_e_eval C \<rho> M"
  unfolding shift_def
  using pp_e_eval_rename[of C "extend_env x \<rho>" Suc M]
  by simp

definition pp_e_list_env :: "ZF list \<Rightarrow> nat \<Rightarrow> ZF" where
  "pp_e_list_env env = nth_default Empty env"

lemma pp_e_list_env_Cons:
  "pp_e_list_env (x # env) = extend_env x (pp_e_list_env env)"
  by (rule ext, rename_tac n, case_tac n)
    (simp_all add: pp_e_list_env_def nth_default_def)

lemma env_ok_implies_pp_e_env_typed:
  assumes env: "env_ok (map pp_e_dom \<Gamma>) xs"
  shows "pp_e_env_typed \<Gamma> (pp_e_list_env xs)"
proof (unfold pp_e_env_typed_def, intro allI impI)
  fix n \<sigma>
  assume lookup: "lookup \<Gamma> n = Some \<sigma>"
  then have n_lt: "n < length \<Gamma>" and nth: "\<Gamma> ! n = \<sigma>"
    by (auto simp: lookup_def split: if_splits)
  from env have len: "length xs = length \<Gamma>"
    and entries:
      "\<forall>k<length \<Gamma>. pp_e_dom (\<Gamma> ! k) (xs ! k)"
    by (auto simp: env_ok_def)
  have env_n: "pp_e_list_env xs n = xs ! n"
    using n_lt len
    by (simp add: pp_e_list_env_def nth_default_nth)
  have typed_n: "pp_e_dom (\<Gamma> ! n) (xs ! n)"
    using entries n_lt by blast
  show "Elem (pp_e_list_env xs n) (pp_e_domain \<sigma>)"
    using env_n typed_n nth by (simp add: pp_e_dom_def)
qed

locale pp_e_constants =
  fixes C :: "string \<Rightarrow> otype \<Rightarrow> ZF"
  assumes C_typed: "Elem (C c \<sigma>) (pp_e_domain \<sigma>)"
begin

theorem pp_e_eval_fundamental:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
  shows
    "(\<forall>\<rho>. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_e_eval C \<rho> M) (pp_e_domain \<tau>)) \<and>
     (\<forall>w \<rho> \<eta>. pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_e_eqv \<tau> w (pp_e_eval C \<rho> M) (pp_e_eval C \<eta> M))"
  using typed
proof (induction rule: has_type.induct)
  case (Var \<Gamma> n \<tau>)
  show ?case
  proof
    show "\<forall>\<rho>. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_e_eval C \<rho> (Var n)) (pp_e_domain \<tau>)"
      using Var.hyps pp_e_env_typed_lookup by simp
    show "\<forall>w \<rho> \<eta>. pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_e_eqv \<tau> w
          (pp_e_eval C \<rho> (Var n)) (pp_e_eval C \<eta> (Var n))"
      using Var.hyps pp_e_env_eqv_lookup by simp
  qed
next
  case (Const \<Gamma> c \<tau>)
  show ?case
  proof
    show "\<forall>\<rho>. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_e_eval C \<rho> (Const c \<tau>)) (pp_e_domain \<tau>)"
      using C_typed by simp
    show "\<forall>w \<rho> \<eta>. pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_e_eqv \<tau> w
          (pp_e_eval C \<rho> (Const c \<tau>))
          (pp_e_eval C \<eta> (Const c \<tau>))"
      using C_typed pp_e_eqv_reflexive by simp
  qed
next
  case (App \<Gamma> M \<sigma> \<tau> N)
  show ?case
  proof
    show "\<forall>\<rho>. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_e_eval C \<rho> (App M N)) (pp_e_domain \<tau>)"
    proof (intro allI impI)
      fix \<rho>
      assume env: "pp_e_env_typed \<Gamma> \<rho>"
      have function_member:
          "Elem (pp_e_eval C \<rho> M)
            (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
        using App.IH(1) env by blast
      have argument:
          "Elem (pp_e_eval C \<rho> N) (pp_e_domain \<sigma>)"
        using App.IH(2) env by blast
      show "Elem (pp_e_eval C \<rho> (App M N)) (pp_e_domain \<tau>)"
        using pp_e_app_closed[OF function_member argument] by simp
    qed
    show "\<forall>w \<rho> \<eta>. pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_e_eqv \<tau> w
          (pp_e_eval C \<rho> (App M N)) (pp_e_eval C \<eta> (App M N))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
      have functions_related:
          "pp_e_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
            (pp_e_eval C \<rho> M) (pp_e_eval C \<eta> M)"
        using App.IH(1) env by blast
      have left_argument:
          "Elem (pp_e_eval C \<rho> N) (pp_e_domain \<sigma>)"
        using App.IH(2) pp_e_env_eqv_typed_left[OF env] by blast
      have right_argument:
          "Elem (pp_e_eval C \<eta> N) (pp_e_domain \<sigma>)"
        using App.IH(2) pp_e_env_eqv_typed_right[OF env] by blast
      have arguments:
          "pp_e_eqv \<sigma> w
            (pp_e_eval C \<rho> N) (pp_e_eval C \<eta> N)"
        using App.IH(2) env by blast
      show "pp_e_eqv \<tau> w
          (pp_e_eval C \<rho> (App M N)) (pp_e_eval C \<eta> (App M N))"
        using pp_e_app_respects[
          OF functions_related left_argument right_argument arguments]
        by simp
    qed
  qed
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  show ?case
  proof
    show "\<forall>\<rho>. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_e_eval C \<rho> (Lam \<sigma> M))
          (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    proof (intro allI impI)
      fix \<rho>
      assume env: "pp_e_env_typed \<Gamma> \<rho>"
      have body_typed:
          "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
            Elem (pp_e_eval C (extend_env x \<rho>) M)
              (pp_e_domain \<tau>)"
      proof -
        fix x
        assume x: "Elem x (pp_e_domain \<sigma>)"
        have extended:
            "pp_e_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
          using pp_e_env_typed_extend[OF env x] .
        show "Elem (pp_e_eval C (extend_env x \<rho>) M)
            (pp_e_domain \<tau>)"
          using Lam.IH extended by blast
      qed
      have body_respects:
          "\<And>w x y. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
            Elem y (pp_e_domain \<sigma>) \<Longrightarrow>
            pp_e_eqv \<sigma> w x y \<Longrightarrow>
            pp_e_eqv \<tau> w
              (pp_e_eval C (extend_env x \<rho>) M)
              (pp_e_eval C (extend_env y \<rho>) M)"
      proof -
        fix w x y
        assume x: "Elem x (pp_e_domain \<sigma>)"
          and y: "Elem y (pp_e_domain \<sigma>)"
          and xy: "pp_e_eqv \<sigma> w x y"
        have base: "pp_e_env_eqv w \<Gamma> \<rho> \<rho>"
          using pp_e_env_eqv_refl[OF env] .
        have extended:
            "pp_e_env_eqv w (\<sigma> # \<Gamma>)
              (extend_env x \<rho>) (extend_env y \<rho>)"
          using pp_e_env_eqv_extend[OF base x y xy] .
        show "pp_e_eqv \<tau> w
            (pp_e_eval C (extend_env x \<rho>) M)
            (pp_e_eval C (extend_env y \<rho>) M)"
          using Lam.IH extended by blast
      qed
      show "Elem (pp_e_eval C \<rho> (Lam \<sigma> M))
          (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
        using pp_e_lambda_closed[OF body_typed body_respects] by simp
    qed
    show "\<forall>w \<rho> \<eta>. pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_e_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_e_eval C \<rho> (Lam \<sigma> M))
          (pp_e_eval C \<eta> (Lam \<sigma> M))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
      show "pp_e_eqv (\<sigma> \<rightarrow>\<^sub>o \<tau>) w
          (pp_e_eval C \<rho> (Lam \<sigma> M))
          (pp_e_eval C \<eta> (Lam \<sigma> M))"
        unfolding pp_e_eval.simps pp_e_eqv.simps
      proof (intro allI impI)
        fix v x y
        assume future: "prefix w v"
          and x: "Elem x (pp_e_domain \<sigma>)"
          and y: "Elem y (pp_e_domain \<sigma>)"
          and xy: "pp_e_eqv \<sigma> v x y"
        have base: "pp_e_env_eqv v \<Gamma> \<rho> \<eta>"
          using pp_e_env_eqv_persistent[OF env future] .
        have extended:
            "pp_e_env_eqv v (\<sigma> # \<Gamma>)
              (extend_env x \<rho>) (extend_env y \<eta>)"
          using pp_e_env_eqv_extend[OF base x y xy] .
        have body:
            "pp_e_eqv \<tau> v
              (pp_e_eval C (extend_env x \<rho>) M)
              (pp_e_eval C (extend_env y \<eta>) M)"
          using Lam.IH extended by blast
        show "pp_e_eqv \<tau> v
            ((Lambda (pp_e_domain \<sigma>)
              (\<lambda>x. pp_e_eval C (extend_env x \<rho>) M)) \<acute> x)
            ((Lambda (pp_e_domain \<sigma>)
              (\<lambda>x. pp_e_eval C (extend_env x \<eta>) M)) \<acute> y)"
          using body x y by (simp add: Lambda_app)
      qed
    qed
  qed
next
  case (Eq \<Gamma> M \<sigma> N)
  show ?case
  proof
    show "\<forall>\<rho>. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_e_eval C \<rho> (Eq \<sigma> M N)) (pp_e_domain Prop)"
    proof (intro allI impI)
      fix \<rho>
      assume "pp_e_env_typed \<Gamma> \<rho>"
      show "Elem (pp_e_eval C \<rho> (Eq \<sigma> M N)) (pp_e_domain Prop)"
        unfolding pp_e_eval.simps
        by (rule pp_e_prop_in_domain)
    qed
    show "\<forall>w \<rho> \<eta>. pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Eq \<sigma> M N))
          (pp_e_eval C \<eta> (Eq \<sigma> M N))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
      show "pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Eq \<sigma> M N))
          (pp_e_eval C \<eta> (Eq \<sigma> M N))"
        unfolding pp_e_eval.simps pp_e_prop_eqv_pp_e_prop_iff
      proof (intro allI impI)
        fix v
        assume future: "prefix w v"
        have env_v: "pp_e_env_eqv v \<Gamma> \<rho> \<eta>"
          using pp_e_env_eqv_persistent[OF env future] .
        have M_left:
            "Elem (pp_e_eval C \<rho> M) (pp_e_domain \<sigma>)"
          using Eq.IH(1) pp_e_env_eqv_typed_left[OF env] by blast
        have M_right:
            "Elem (pp_e_eval C \<eta> M) (pp_e_domain \<sigma>)"
          using Eq.IH(1) pp_e_env_eqv_typed_right[OF env] by blast
        have N_left:
            "Elem (pp_e_eval C \<rho> N) (pp_e_domain \<sigma>)"
          using Eq.IH(2) pp_e_env_eqv_typed_left[OF env] by blast
        have N_right:
            "Elem (pp_e_eval C \<eta> N) (pp_e_domain \<sigma>)"
          using Eq.IH(2) pp_e_env_eqv_typed_right[OF env] by blast
        have M_related:
            "pp_e_eqv \<sigma> v
              (pp_e_eval C \<rho> M) (pp_e_eval C \<eta> M)"
          using Eq.IH(1) env_v by blast
        have N_related:
            "pp_e_eqv \<sigma> v
              (pp_e_eval C \<rho> N) (pp_e_eval C \<eta> N)"
          using Eq.IH(2) env_v by blast
        show "pp_e_eqv \<sigma> (v)
              (pp_e_eval C \<rho> M) (pp_e_eval C \<rho> N) =
            pp_e_eqv \<sigma> (v)
              (pp_e_eval C \<eta> M) (pp_e_eval C \<eta> N)"
          using pp_e_eqv_congruence[
            OF M_left M_right N_left N_right M_related N_related]
          by simp
      qed
    qed
  qed
next
  case (Neg \<Gamma> A)
  show ?case
  proof
    show "\<forall>\<rho>. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_e_eval C \<rho> (Neg A)) (pp_e_domain Prop)"
      by (intro allI impI; simp only: pp_e_eval.simps;
          rule pp_e_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Neg A)) (pp_e_eval C \<eta> (Neg A))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
      have related:
          "pp_e_eqv Prop w (pp_e_eval C \<rho> A) (pp_e_eval C \<eta> A)"
        using Neg.IH env by blast
      show "pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Neg A)) (pp_e_eval C \<eta> (Neg A))"
        unfolding pp_e_eval.simps pp_e_prop_eqv_pp_e_prop_iff
        using pp_e_prop_eqv_at[OF related] by blast
    qed
  qed
next
  case (Conj \<Gamma> A B)
  show ?case
  proof
    show "\<forall>\<rho>. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_e_eval C \<rho> (Conj A B)) (pp_e_domain Prop)"

      by (intro allI impI; simp only: pp_e_eval.simps;
          rule pp_e_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Conj A B))
          (pp_e_eval C \<eta> (Conj A B))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
      have A_related:
          "pp_e_eqv Prop w (pp_e_eval C \<rho> A) (pp_e_eval C \<eta> A)"
        using Conj.IH(1) env by blast
      have B_related:
          "pp_e_eqv Prop w (pp_e_eval C \<rho> B) (pp_e_eval C \<eta> B)"
        using Conj.IH(2) env by blast
      show "pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Conj A B))
          (pp_e_eval C \<eta> (Conj A B))"
        unfolding pp_e_eval.simps pp_e_prop_eqv_pp_e_prop_iff
        using pp_e_prop_eqv_at[OF A_related]
          pp_e_prop_eqv_at[OF B_related] by blast
    qed
  qed
next
  case (Disj \<Gamma> A B)
  show ?case
  proof
    show "\<forall>\<rho>. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_e_eval C \<rho> (Disj A B)) (pp_e_domain Prop)"
      by (intro allI impI; simp only: pp_e_eval.simps;
          rule pp_e_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Disj A B))
          (pp_e_eval C \<eta> (Disj A B))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
      have A_related:
          "pp_e_eqv Prop w (pp_e_eval C \<rho> A) (pp_e_eval C \<eta> A)"
        using Disj.IH(1) env by blast
      have B_related:
          "pp_e_eqv Prop w (pp_e_eval C \<rho> B) (pp_e_eval C \<eta> B)"
        using Disj.IH(2) env by blast
      show "pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Disj A B))
          (pp_e_eval C \<eta> (Disj A B))"
        unfolding pp_e_eval.simps pp_e_prop_eqv_pp_e_prop_iff
        using pp_e_prop_eqv_at[OF A_related]
          pp_e_prop_eqv_at[OF B_related] by blast
    qed
  qed
next
  case (Imp \<Gamma> A B)
  show ?case
  proof
    show "\<forall>\<rho>. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_e_eval C \<rho> (Imp A B)) (pp_e_domain Prop)"
      by (intro allI impI; simp only: pp_e_eval.simps;
          rule pp_e_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Imp A B))
          (pp_e_eval C \<eta> (Imp A B))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
      have A_related:
          "pp_e_eqv Prop w (pp_e_eval C \<rho> A) (pp_e_eval C \<eta> A)"
        using Imp.IH(1) env by blast
      have B_related:
          "pp_e_eqv Prop w (pp_e_eval C \<rho> B) (pp_e_eval C \<eta> B)"
        using Imp.IH(2) env by blast
      show "pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Imp A B))
          (pp_e_eval C \<eta> (Imp A B))"
        unfolding pp_e_eval.simps pp_e_prop_eqv_pp_e_prop_iff
        using pp_e_prop_eqv_at[OF A_related]
          pp_e_prop_eqv_at[OF B_related] by blast
    qed
  qed
next
  case (Forall \<sigma> \<Gamma> A)
  show ?case
  proof
    show "\<forall>\<rho>. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_e_eval C \<rho> (Forall \<sigma> A)) (pp_e_domain Prop)"
      by (intro allI impI; simp only: pp_e_eval.simps;
          rule pp_e_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Forall \<sigma> A))
          (pp_e_eval C \<eta> (Forall \<sigma> A))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
      show "pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Forall \<sigma> A))
          (pp_e_eval C \<eta> (Forall \<sigma> A))"
        unfolding pp_e_eval.simps pp_e_prop_eqv_pp_e_prop_iff
      proof (intro allI impI)
        fix v
        assume future: "prefix w v"
        have base: "pp_e_env_eqv v \<Gamma> \<rho> \<eta>"
          using pp_e_env_eqv_persistent[OF env future] .
        have body_iff:
            "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
              (pp_e_holds (pp_e_eval C (extend_env x \<rho>) A) v \<longleftrightarrow>
               pp_e_holds (pp_e_eval C (extend_env x \<eta>) A) v)"
        proof -
          fix x
          assume x: "Elem x (pp_e_domain \<sigma>)"
          have xx: "pp_e_eqv \<sigma> v x x"
            using pp_e_eqv_reflexive[OF x] .
          have extended:
              "pp_e_env_eqv v (\<sigma> # \<Gamma>)
                (extend_env x \<rho>) (extend_env x \<eta>)"
            using pp_e_env_eqv_extend[OF base x x xx] .
          have related:
              "pp_e_eqv Prop v
                (pp_e_eval C (extend_env x \<rho>) A)
                (pp_e_eval C (extend_env x \<eta>) A)"
            using Forall.IH extended by blast
          show "pp_e_holds (pp_e_eval C (extend_env x \<rho>) A) v \<longleftrightarrow>
              pp_e_holds (pp_e_eval C (extend_env x \<eta>) A) v"
            using pp_e_prop_eqv_at[OF related, of v] by simp
        qed
        show "(\<forall>x. Elem x (pp_e_domain \<sigma>) \<longrightarrow>
              pp_e_holds (pp_e_eval C (extend_env x \<rho>) A) v) =
            (\<forall>x. Elem x (pp_e_domain \<sigma>) \<longrightarrow>
              pp_e_holds (pp_e_eval C (extend_env x \<eta>) A) v)"
          using body_iff by blast
      qed
    qed
  qed
next
  case (Exists \<sigma> \<Gamma> A)
  show ?case
  proof
    show "\<forall>\<rho>. pp_e_env_typed \<Gamma> \<rho> \<longrightarrow>
        Elem (pp_e_eval C \<rho> (Exists \<sigma> A)) (pp_e_domain Prop)"
      by (intro allI impI; simp only: pp_e_eval.simps;
          rule pp_e_prop_in_domain)
    show "\<forall>w \<rho> \<eta>. pp_e_env_eqv w \<Gamma> \<rho> \<eta> \<longrightarrow>
        pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Exists \<sigma> A))
          (pp_e_eval C \<eta> (Exists \<sigma> A))"
    proof (intro allI impI)
      fix w \<rho> \<eta>
      assume env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
      show "pp_e_eqv Prop w
          (pp_e_eval C \<rho> (Exists \<sigma> A))
          (pp_e_eval C \<eta> (Exists \<sigma> A))"
        unfolding pp_e_eval.simps pp_e_prop_eqv_pp_e_prop_iff
      proof (intro allI impI)
        fix v
        assume future: "prefix w v"
        have base: "pp_e_env_eqv v \<Gamma> \<rho> \<eta>"
          using pp_e_env_eqv_persistent[OF env future] .
        have body_iff:
            "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
              (pp_e_holds (pp_e_eval C (extend_env x \<rho>) A) v \<longleftrightarrow>
               pp_e_holds (pp_e_eval C (extend_env x \<eta>) A) v)"
        proof -
          fix x
          assume x: "Elem x (pp_e_domain \<sigma>)"
          have xx: "pp_e_eqv \<sigma> v x x"
            using pp_e_eqv_reflexive[OF x] .
          have extended:
              "pp_e_env_eqv v (\<sigma> # \<Gamma>)
                (extend_env x \<rho>) (extend_env x \<eta>)"
            using pp_e_env_eqv_extend[OF base x x xx] .
          have related:
              "pp_e_eqv Prop v
                (pp_e_eval C (extend_env x \<rho>) A)
                (pp_e_eval C (extend_env x \<eta>) A)"
            using Exists.IH extended by blast
          show "pp_e_holds (pp_e_eval C (extend_env x \<rho>) A) v \<longleftrightarrow>
              pp_e_holds (pp_e_eval C (extend_env x \<eta>) A) v"
            using pp_e_prop_eqv_at[OF related, of v] by simp
        qed
        show "(\<exists>x. Elem x (pp_e_domain \<sigma>) \<and>
              pp_e_holds (pp_e_eval C (extend_env x \<rho>) A) v) =
            (\<exists>x. Elem x (pp_e_domain \<sigma>) \<and>
              pp_e_holds (pp_e_eval C (extend_env x \<eta>) A) v)"
          using body_iff by blast
      qed
    qed
  qed
qed

lemma pp_e_eval_type:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_dom \<tau> (pp_e_eval C \<rho> M)"
  using pp_e_eval_fundamental[OF typed] env
  unfolding pp_e_dom_def by blast

lemma pp_e_eval_respects:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and env: "pp_e_env_eqv w \<Gamma> \<rho> \<eta>"
  shows "pp_e_eqv \<tau> w
    (pp_e_eval C \<rho> M) (pp_e_eval C \<eta> M)"
  using pp_e_eval_fundamental[OF typed] env by blast

definition pp_e_den :: "oterm \<Rightarrow> ZF list \<Rightarrow> ZF" where
  "pp_e_den A env = pp_e_eval C (pp_e_list_env env) A"

sublocale ExactBaconHenkin:
  henkin_action_model pp_e_dom pp_e_holds pp_e_den
proof
  fix \<Gamma> A \<sigma> env
  assume typed: "\<Gamma> \<turnstile> A : \<sigma>"
    and env: "env_ok (map pp_e_dom \<Gamma>) env"
  show "pp_e_dom \<sigma> (pp_e_den A env)"
    unfolding pp_e_den_def
    using pp_e_eval_type[
      OF typed env_ok_implies_pp_e_env_typed[OF env]] .
next
  show "pp_e_holds (pp_e_den (Neg A) env) w \<longleftrightarrow>
      \<not> pp_e_holds (pp_e_den A env) w" for A env w
    by (simp only: pp_e_den_def pp_e_eval_Neg_holds)
next
  show "pp_e_holds (pp_e_den (Imp A B) env) w \<longleftrightarrow>
      (pp_e_holds (pp_e_den A env) w \<longrightarrow>
       pp_e_holds (pp_e_den B env) w)" for A B env w
    by (simp only: pp_e_den_def pp_e_eval_Imp_holds)
next
  show "pp_e_holds (pp_e_den (Forall \<sigma> Q) env) w \<longleftrightarrow>
      (\<forall>x. pp_e_dom \<sigma> x \<longrightarrow>
        pp_e_holds (pp_e_den Q (x # env)) w)" for \<sigma> Q env w
    by (simp only: pp_e_den_def pp_e_dom_def pp_e_list_env_Cons
      pp_e_eval_Forall_holds)
next
  show "pp_e_holds (pp_e_den (Exists \<sigma> P) env) w \<longleftrightarrow>
      (\<exists>x. pp_e_dom \<sigma> x \<and>
        pp_e_holds (pp_e_den P (x # env)) w)" for \<sigma> P env w
    by (simp only: pp_e_den_def pp_e_dom_def pp_e_list_env_Cons
      pp_e_eval_Exists_holds)
next
  show "pp_e_den (shift A) (x # env) = pp_e_den A env" for A x env
    by (simp add: pp_e_den_def pp_e_list_env_Cons pp_e_eval_shift)
next
  show "\<exists>x. pp_e_dom \<sigma> x" for \<sigma>
    using pp_e_domain_nonempty by (simp add: pp_e_dom_def)
qed


end

definition pp_e_default_constants ::
    "string \<Rightarrow> otype \<Rightarrow> ZF" where
  "pp_e_default_constants c \<sigma> = pp_e_default \<sigma>"

interpretation DefaultExactBaconConstants:
  pp_e_constants pp_e_default_constants
  by standard
    (simp add: pp_e_default_constants_def pp_e_default_in_domain)

definition pp_e_closed_env :: "nat \<Rightarrow> ZF" where
  "pp_e_closed_env n = Empty"

lemma pp_e_empty_env_typed:
  "pp_e_env_typed [] \<rho>"
  by (simp add: pp_e_env_typed_def lookup_def)

lemma pp_e_empty_env_eqv:
  "pp_e_env_eqv w [] \<rho> \<eta>"
  by (simp add: pp_e_env_eqv_def pp_e_env_typed_def lookup_def)

section \<open>Internal classifiers\<close>

definition pp_e_predicate_admissible ::
    "otype \<Rightarrow> (nat list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "pp_e_predicate_admissible \<sigma> Q \<longleftrightarrow>
    (\<forall>w x y.
      Elem x (pp_e_domain \<sigma>) \<longrightarrow>
      Elem y (pp_e_domain \<sigma>) \<longrightarrow>
      pp_e_eqv \<sigma> w x y \<longrightarrow>
      (\<forall>v. prefix w v \<longrightarrow> (Q v x \<longleftrightarrow> Q v y)))"

definition pp_e_classifier ::
    "otype \<Rightarrow> (nat list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow> ZF"
  where
  "pp_e_classifier \<sigma> Q =
    Lambda (pp_e_domain \<sigma>) (\<lambda>x. pp_e_prop (\<lambda>w. Q w x))"

lemma pp_e_classifier_in_domain:
  assumes admissible: "pp_e_predicate_admissible \<sigma> Q"
  shows "Elem (pp_e_classifier \<sigma> Q)
    (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
proof (unfold pp_e_classifier_def, rule pp_e_lambda_closed)
  show "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
      Elem (pp_e_prop (\<lambda>w. Q w x)) (pp_e_domain Prop)"
    by (rule pp_e_prop_in_domain)
  fix w x y
  assume x: "Elem x (pp_e_domain \<sigma>)"
    and y: "Elem y (pp_e_domain \<sigma>)"
    and xy: "pp_e_eqv \<sigma> w x y"
  show "pp_e_eqv Prop w
      (pp_e_prop (\<lambda>v. Q v x))
      (pp_e_prop (\<lambda>v. Q v y))"
    unfolding pp_e_prop_eqv_pp_e_prop_iff
    using admissible x y xy
    by (simp add: pp_e_predicate_admissible_def)
qed

lemma pp_e_classifier_apply:
  assumes x: "Elem x (pp_e_domain \<sigma>)"
  shows "(pp_e_classifier \<sigma> Q) \<acute> x =
    pp_e_prop (\<lambda>w. Q w x)"
  using x by (simp add: pp_e_classifier_def Lambda_app)

lemma pp_e_classifier_holds:
  assumes x: "Elem x (pp_e_domain \<sigma>)"
  shows "pp_e_holds ((pp_e_classifier \<sigma> Q) \<acute> x) w
    \<longleftrightarrow> Q w x"
  using pp_e_classifier_apply[OF x, of Q] by simp

lemma pp_e_truth_in_domain:
  "Elem (pp_zf_truth b) (pp_e_domain Prop)"
  using pp_zf_truth_in_power[of b] by simp

definition pp_e_moving_seed :: "nat list \<Rightarrow> ZF" where
  "pp_e_moving_seed w =
    pp_e_prop (\<lambda>v. prefix (w @ [Suc 0]) v)"

lemma pp_e_moving_seed_in_domain:
  "Elem (pp_e_moving_seed w) (pp_e_domain Prop)"
  unfolding pp_e_moving_seed_def
  by (rule pp_e_prop_in_domain)

lemma pp_e_moving_seed_holds[simp]:
  "pp_e_holds (pp_e_moving_seed w) v \<longleftrightarrow>
    prefix (w @ [Suc 0]) v"
  by (simp add: pp_e_moving_seed_def)

lemma pp_e_split_no_common_successor:
  "\<not> (\<exists>z.
    prefix (w @ [0]) z \<and>
    prefix (w @ [Suc 0]) z)"
proof
  assume "\<exists>z.
      prefix (w @ [0]) z \<and>
      prefix (w @ [Suc 0]) z"
  then obtain z where zero_z: "prefix (w @ [0]) z"
    and one_z: "prefix (w @ [Suc 0]) z"
    by blast
  have "prefix (w @ [0]) (w @ [Suc 0]) \<or>
      prefix (w @ [Suc 0]) (w @ [0])"
    using prefix_same_cases[OF zero_z one_z] .
  then show False by simp
qed

lemma pp_e_moving_seed_false_now:
  "\<not> pp_e_eqv Prop w
    (pp_e_moving_seed w) (pp_zf_truth True)"
proof
  assume eqv:
      "pp_e_eqv Prop w
        (pp_e_moving_seed w) (pp_zf_truth True)"
  have at_w:
      "pp_e_holds (pp_e_moving_seed w) w \<longleftrightarrow>
        pp_e_holds (pp_zf_truth True) w"
    using pp_e_prop_eqv_at[OF eqv, of w] by simp
  then show False by simp
qed

lemma pp_e_moving_seed_true_on_left:
  "pp_e_eqv Prop (w @ [Suc 0])
    (pp_e_moving_seed w) (pp_zf_truth True)"
  by simp

lemma pp_e_moving_seed_no_box_on_false_cone:
  assumes future: "prefix (w @ [0]) v"
  shows "\<not> pp_e_eqv Prop v
    (pp_e_moving_seed w) (pp_zf_truth True)"
proof
  assume box:
      "pp_e_eqv Prop v
        (pp_e_moving_seed w) (pp_zf_truth True)"
  have at_v:
      "pp_e_holds (pp_e_moving_seed w) v \<longleftrightarrow>
        pp_e_holds (pp_zf_truth True) v"
    using pp_e_prop_eqv_at[OF box, of v] by simp
  have true_branch: "prefix (w @ [Suc 0]) v"
    using at_v by simp
  show False
    using pp_e_split_no_common_successor[of w]
      future true_branch by blast
qed

fun pp_e_moving_fundamental_at ::
    "otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool" where
  "pp_e_moving_fundamental_at Ind w x = False"
| "pp_e_moving_fundamental_at Prop w x =
    pp_e_eqv Prop w x (pp_e_moving_seed w)"
| "pp_e_moving_fundamental_at (\<sigma> \<rightarrow>\<^sub>o \<tau>) w x =
    False"

lemma pp_e_moving_fundamental_admissible:
  "pp_e_predicate_admissible \<sigma>
    (pp_e_moving_fundamental_at \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    by (simp add: pp_e_predicate_admissible_def)
next
  case Prop
  show ?thesis
    unfolding Prop pp_e_predicate_admissible_def
  proof (intro allI impI)
    fix w x y v
    assume x: "Elem x (pp_e_domain Prop)"
      and y: "Elem y (pp_e_domain Prop)"
      and xy: "pp_e_eqv Prop w x y"
      and future: "prefix w v"
    have xy_v: "pp_e_eqv Prop v x y"
      using pp_e_eqv_persistent[OF xy future] .
    have seed_refl:
        "pp_e_eqv Prop v
          (pp_e_moving_seed v) (pp_e_moving_seed v)"
      using pp_e_eqv_reflexive[OF pp_e_moving_seed_in_domain] .
    show "pp_e_moving_fundamental_at Prop v x =
        pp_e_moving_fundamental_at Prop v y"
      using pp_e_eqv_congruence[
        OF x y pp_e_moving_seed_in_domain
          pp_e_moving_seed_in_domain xy_v seed_refl]
      by simp
  qed
next
  case (Arr \<sigma> \<tau>)
  then show ?thesis
    by (simp add: pp_e_predicate_admissible_def)
qed

fun pp_e_moving_internal_constants ::
    "(otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool) \<Rightarrow>
      string \<Rightarrow> otype \<Rightarrow> ZF" where
  "pp_e_moving_internal_constants Pure c Ind = pp_e_default Ind"
| "pp_e_moving_internal_constants Pure c Prop = pp_e_default Prop"
| "pp_e_moving_internal_constants Pure c (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    (if c = pp_pure_name \<and> \<tau> = Prop
     then pp_e_classifier \<sigma> (Pure \<sigma>)
     else if c = pp_fun_name \<and> \<tau> = Prop
     then pp_e_classifier \<sigma> (pp_e_moving_fundamental_at \<sigma>)
     else pp_e_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))"

locale pp_e_moving_internal_parameters =
  fixes Pure :: "otype \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool"
  assumes Pure_admissible:
      "\<And>\<sigma>. pp_e_predicate_admissible \<sigma> (Pure \<sigma>)"
begin

lemma pp_e_moving_internal_constants_typed:
  "Elem (pp_e_moving_internal_constants Pure c \<sigma>)
    (pp_e_domain \<sigma>)"
proof (cases \<sigma>)
  case Ind
  then show ?thesis
    using pp_e_default_in_domain[of Ind] by simp
next
  case Prop
  then show ?thesis
    using pp_e_default_in_domain[of Prop] by simp
next
  case (Arr \<sigma> \<tau>)
  have pure_classifier:
      "Elem (pp_e_classifier \<sigma> (Pure \<sigma>))
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_e_classifier_in_domain[OF Pure_admissible] .
  have fun_classifier:
      "Elem
        (pp_e_classifier \<sigma> (pp_e_moving_fundamental_at \<sigma>))
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o Prop))"
    using pp_e_classifier_in_domain[
      OF pp_e_moving_fundamental_admissible] .
  have default:
      "Elem (pp_e_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using pp_e_default_in_domain .
  show ?thesis
    using Arr pure_classifier fun_classifier default by auto
qed

sublocale MovingExactBaconConstants:
  pp_e_constants "pp_e_moving_internal_constants Pure"
  by standard (rule pp_e_moving_internal_constants_typed)

lemma pp_e_moving_eval_Pure[simp]:
  "pp_e_eval (pp_e_moving_internal_constants Pure) \<rho> (pp_Pure \<sigma>) =
    pp_e_classifier \<sigma> (Pure \<sigma>)"
  by (simp add: pp_Pure_def pp_pure_name_def)

lemma pp_e_moving_eval_Fun[simp]:
  "pp_e_eval (pp_e_moving_internal_constants Pure) \<rho> (pp_Fun \<sigma>) =
    pp_e_classifier \<sigma> (pp_e_moving_fundamental_at \<sigma>)"
  by (simp add: pp_Fun_def pp_fun_name_def pp_pure_name_def)

lemma pp_e_moving_eval_pure_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds
      (pp_e_eval (pp_e_moving_internal_constants Pure) \<rho>
        (pp_pure \<sigma> M)) w
    \<longleftrightarrow>
      Pure \<sigma> w
        (pp_e_eval (pp_e_moving_internal_constants Pure) \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_e_eval (pp_e_moving_internal_constants Pure) \<rho> M)
        (pp_e_domain \<sigma>)"
    using MovingExactBaconConstants.pp_e_eval_type[OF typed env]
    by (simp add: pp_e_dom_def)
  show ?thesis
    unfolding pp_pure_def
    using pp_e_classifier_holds[OF argument, of "Pure \<sigma>" w]
    by simp
qed

lemma pp_e_moving_eval_fun_holds:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>"
    and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds
      (pp_e_eval (pp_e_moving_internal_constants Pure) \<rho>
        (pp_fun \<sigma> M)) w
    \<longleftrightarrow>
      pp_e_moving_fundamental_at \<sigma> w
        (pp_e_eval (pp_e_moving_internal_constants Pure) \<rho> M)"
proof -
  have argument:
      "Elem
        (pp_e_eval (pp_e_moving_internal_constants Pure) \<rho> M)
        (pp_e_domain \<sigma>)"
    using MovingExactBaconConstants.pp_e_eval_type[OF typed env]
    by (simp add: pp_e_dom_def)
  show ?thesis
    unfolding pp_fun_def
    using pp_e_classifier_holds[
      OF argument, of "pp_e_moving_fundamental_at \<sigma>" w]
    by simp
qed

lemma pp_e_moving_unique_fundamental_holds:
  "pp_e_holds
    (pp_e_eval (pp_e_moving_internal_constants Pure) \<rho>
      (pp_unique_fundamental Prop)) w"
proof -
  let ?r = "pp_e_moving_seed w"
  have base: "pp_e_env_typed [] \<rho>"
    by (simp add: pp_e_env_typed_def lookup_def)
  have r_env:
      "pp_e_env_typed [Prop] (extend_env ?r \<rho>)"
    using pp_e_env_typed_extend[
      OF base pp_e_moving_seed_in_domain] .
  have r_is_fundamental:
      "pp_e_holds
        (pp_e_eval (pp_e_moving_internal_constants Pure)
          (extend_env ?r \<rho>) (pp_fun Prop (Var 0))) w"
  proof -
    have var_type: "[Prop] \<turnstile> Var 0 : Prop"
      by simp
    have rr: "pp_e_eqv Prop w ?r ?r"
      using pp_e_eqv_reflexive[OF pp_e_moving_seed_in_domain] .
    show ?thesis
      using pp_e_moving_eval_fun_holds[
        OF var_type r_env, of w] rr
      by simp
  qed
  have uniqueness:
      "\<forall>y. Elem y (pp_e_domain Prop) \<longrightarrow>
        pp_e_holds
          (pp_e_eval (pp_e_moving_internal_constants Pure)
            (extend_env y (extend_env ?r \<rho>))
            (Imp
              (pp_fun Prop (Var 0))
              (Eq Prop (Var 0) (Var 1)))) w"
  proof (intro allI impI)
    fix y
    assume y: "Elem y (pp_e_domain Prop)"
    have yr_env:
        "pp_e_env_typed [Prop, Prop]
          (extend_env y (extend_env ?r \<rho>))"
      using pp_e_env_typed_extend[OF r_env y] .
    have y_type: "[Prop, Prop] \<turnstile> Var 0 : Prop"
      by simp
    have fun_iff:
        "pp_e_holds
          (pp_e_eval (pp_e_moving_internal_constants Pure)
            (extend_env y (extend_env ?r \<rho>))
            (pp_fun Prop (Var 0))) w
        \<longleftrightarrow> pp_e_eqv Prop w y ?r"
      using pp_e_moving_eval_fun_holds[
        OF y_type yr_env, of w] by simp
    have eq_iff:
        "pp_e_holds
          (pp_e_eval (pp_e_moving_internal_constants Pure)
            (extend_env y (extend_env ?r \<rho>))
            (Eq Prop (Var 0) (Var 1))) w
        \<longleftrightarrow> pp_e_eqv Prop w y ?r"
      by simp
    show "pp_e_holds
        (pp_e_eval (pp_e_moving_internal_constants Pure)
          (extend_env y (extend_env ?r \<rho>))
          (Imp
            (pp_fun Prop (Var 0))
            (Eq Prop (Var 0) (Var 1)))) w"
      unfolding pp_e_eval_Imp_holds
      using fun_iff eq_iff by blast
  qed
  show ?thesis
    unfolding pp_unique_fundamental_def
    apply (simp only: pp_e_eval_Exists_holds)
    apply (rule exI[of _ ?r])
    using pp_e_moving_seed_in_domain r_is_fundamental uniqueness
    by (simp only: pp_e_eval_Conj_holds pp_e_eval_Forall_holds)
qed

lemma pp_e_moving_no_fundamentals_holds:
  assumes nonprop: "\<sigma> \<noteq> Prop"
  shows "pp_e_holds
    (pp_e_eval (pp_e_moving_internal_constants Pure) \<rho>
      (pp_no_fundamentals \<sigma>)) w"
proof -
  have base: "pp_e_env_typed [] \<rho>"
    by (simp add: pp_e_env_typed_def lookup_def)
  show ?thesis
    unfolding pp_no_fundamentals_def
    apply (simp only: pp_e_eval_Forall_holds)
    apply (intro allI impI)
  proof -
    fix x
    assume x: "Elem x (pp_e_domain \<sigma>)"
    have extended:
        "pp_e_env_typed [\<sigma>] (extend_env x \<rho>)"
      using pp_e_env_typed_extend[OF base x] .
    have var_type: "[\<sigma>] \<turnstile> Var 0 : \<sigma>"
      by simp
    have fun_false:
        "\<not> pp_e_moving_fundamental_at \<sigma> w x"
      using nonprop by (cases \<sigma>) auto
    have fun_iff:
        "pp_e_holds
          (pp_e_eval (pp_e_moving_internal_constants Pure)
            (extend_env x \<rho>) (pp_fun \<sigma> (Var 0))) w
        \<longleftrightarrow> pp_e_moving_fundamental_at \<sigma> w x"
      using pp_e_moving_eval_fun_holds[
        OF var_type extended, of w] by simp
    have not_fun:
        "\<not> pp_e_holds
          (pp_e_eval (pp_e_moving_internal_constants Pure)
            (extend_env x \<rho>) (pp_fun \<sigma> (Var 0))) w"
      using fun_iff fun_false by blast
    show "pp_e_holds
        (pp_e_eval (pp_e_moving_internal_constants Pure)
          (extend_env x \<rho>)
          (Neg (pp_fun \<sigma> (Var 0)))) w"
      using pp_e_eval_Neg_holds[
        of "pp_e_moving_internal_constants Pure" "extend_env x \<rho>"
          "pp_fun \<sigma> (Var 0)" w]
        not_fun
      by blast
  qed
qed

theorem pp_e_moving_unique_fundamental_gvalid:
  "MovingExactBaconConstants.ExactBaconHenkin.gvalid []
    (pp_unique_fundamental Prop)"
  unfolding MovingExactBaconConstants.ExactBaconHenkin.gvalid_def
    MovingExactBaconConstants.pp_e_den_def
  using pp_e_moving_unique_fundamental_holds by blast

theorem pp_e_moving_no_fundamentals_gvalid:
  assumes "\<sigma> \<noteq> Prop"
  shows "MovingExactBaconConstants.ExactBaconHenkin.gvalid []
    (pp_no_fundamentals \<sigma>)"
  unfolding MovingExactBaconConstants.ExactBaconHenkin.gvalid_def
    MovingExactBaconConstants.pp_e_den_def
  using pp_e_moving_no_fundamentals_holds[OF assms] by blast


end

end
