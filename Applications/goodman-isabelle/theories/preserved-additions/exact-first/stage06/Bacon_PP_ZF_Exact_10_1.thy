theory Bacon_PP_ZF_Exact_10_1
  imports 
    "Goodman_Exact_Legacy_05.Bacon_PP_ZF_Exact_Substitution"
begin

section \<open>Bacon's Theorem 10.1 on the exact carriers\<close>

text \<open>
  The reserved substitutions are the one-letter words @{term "[n]"}.  They
  are pairwise disjoint cones for Bacon's right-division action.  The
  following recursion is therefore carried out directly in his monoid and
  on the recursively restricted carriers of Definition 7.2.
\<close>

fun pp_e_propositional_type :: "otype \<Rightarrow> bool" where
  "pp_e_propositional_type Ind = False"
| "pp_e_propositional_type Prop = True"
| "pp_e_propositional_type (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    (pp_e_propositional_type \<sigma> \<and>
     pp_e_propositional_type \<tau>)"

definition pp_e_typed_sequence ::
    "otype \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> bool"
where
  "pp_e_typed_sequence \<sigma> a \<longleftrightarrow>
    (\<forall>n. Elem (a n) (pp_e_domain \<sigma>))"

fun pp_e_branch_glue ::
    "otype \<Rightarrow> (nat \<Rightarrow> ZF) \<Rightarrow> ZF"
where
  "pp_e_branch_glue Ind a = a 0"
| "pp_e_branch_glue Prop a =
    pp_n_bacon_embed
      (pp_glued_witness (\<lambda>n. pp_n_bacon_extract (a n)))"
| "pp_e_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f =
    Lambda (pp_e_domain \<sigma>)
      (\<lambda>x. pp_e_branch_glue \<tau>
        (\<lambda>n. f n \<acute> pp_b_action \<sigma> [n] x))"

lemma pp_e_branch_glue_Prop_in_domain:
  "Elem (pp_e_branch_glue Prop a) (pp_e_domain Prop)"
  unfolding pp_e_branch_glue.simps
  using pp_n_bacon_embed_in_domain[
    of "pp_glued_witness (\<lambda>n. pp_n_bacon_extract (a n))"]
  by simp

lemma pp_e_branch_glue_Prop_action:
  assumes typed: "pp_e_typed_sequence Prop a"
  shows "pp_b_action Prop [n] (pp_e_branch_glue Prop a) = a n"
proof -
  have an: "Elem (a n) (pp_e_domain Prop)"
    using typed unfolding pp_e_typed_sequence_def by blast
  have extracted:
      "pp_view [n]
        (pp_glued_witness (\<lambda>m. pp_n_bacon_extract (a m))) =
       pp_n_bacon_extract (a n)"
    by simp
  have action:
      "pp_b_action Prop [n] (pp_e_branch_glue Prop a) =
       pp_n_bacon_embed
        (pp_view [n]
          (pp_glued_witness (\<lambda>m. pp_n_bacon_extract (a m))))"
    unfolding pp_e_branch_glue.simps
    using pp_n_prop_action_is_bacon_division[
      of "[n]" "pp_glued_witness (\<lambda>m. pp_n_bacon_extract (a m))"]
      extracted
    by (simp add: pp_prop_action_def)
  show ?thesis
    using action extracted pp_n_bacon_embed_extract[of "a n"] an
    by simp
qed

lemma pp_e_branch_output_typed:
  assumes fseq:
      "pp_e_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f"
    and x: "Elem x (pp_e_domain \<sigma>)"
  shows "pp_e_typed_sequence \<tau>
    (\<lambda>n. f n \<acute> pp_b_action \<sigma> [n] x)"
  unfolding pp_e_typed_sequence_def
proof
  fix n
  have fn:
      "Elem (f n) (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using fseq unfolding pp_e_typed_sequence_def by blast
  have ax:
      "Elem (pp_b_action \<sigma> [n] x) (pp_e_domain \<sigma>)"
    by (rule pp_b_action_closed_all[OF x])
  show "Elem (f n \<acute> pp_b_action \<sigma> [n] x)
      (pp_e_domain \<tau>)"
    by (rule pp_b_app_closed[OF fn ax])
qed

definition pp_e_branch_glue_invariant :: "otype \<Rightarrow> bool" where
  "pp_e_branch_glue_invariant \<sigma> \<longleftrightarrow>
    (pp_e_propositional_type \<sigma> \<longrightarrow>
      ((\<forall>a. pp_e_typed_sequence \<sigma> a \<longrightarrow>
          Elem (pp_e_branch_glue \<sigma> a) (pp_e_domain \<sigma>))
       \<and>
       (\<forall>a n. pp_e_typed_sequence \<sigma> a \<longrightarrow>
          pp_b_action \<sigma> [n] (pp_e_branch_glue \<sigma> a) = a n)))"

lemma pp_e_nonempty_word_snoc:
  assumes "i \<noteq> []"
  shows "\<exists>k n. i = k @ [n]"
proof (intro exI[of _ "butlast i"] exI[of _ "last i"])
  show "i = butlast i @ [last i]"
    using assms by simp
qed

theorem pp_e_branch_glue_invariant_all:
  "pp_e_branch_glue_invariant \<sigma>"
proof (induction \<sigma>)
  case Ind
  then show ?case
    by (simp add: pp_e_branch_glue_invariant_def)
next
  case Prop
  show ?case
    unfolding pp_e_branch_glue_invariant_def
    using pp_e_branch_glue_Prop_in_domain
      pp_e_branch_glue_Prop_action by blast
next
  case (Arr \<sigma> \<tau>)
  show ?case
  proof (unfold pp_e_branch_glue_invariant_def, intro impI conjI)
    assume prop_arr: "pp_e_propositional_type (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    then have prop_sigma: "pp_e_propositional_type \<sigma>"
      and prop_tau: "pp_e_propositional_type \<tau>"
      by simp_all
    have tau_domain:
        "\<And>a. pp_e_typed_sequence \<tau> a \<Longrightarrow>
          Elem (pp_e_branch_glue \<tau> a) (pp_e_domain \<tau>)"
      using Arr.IH(2) prop_tau
      unfolding pp_e_branch_glue_invariant_def by blast
    have tau_action:
        "\<And>a n. pp_e_typed_sequence \<tau> a \<Longrightarrow>
          pp_b_action \<tau> [n] (pp_e_branch_glue \<tau> a) = a n"
      using Arr.IH(2) prop_tau
      unfolding pp_e_branch_glue_invariant_def by blast
    have arr_domain: "\<forall>f. pp_e_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<longrightarrow>
        Elem (pp_e_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    proof (intro allI impI)
      fix f
      assume fseq: "pp_e_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f"
      let ?G = "\<lambda>x. pp_e_branch_glue \<tau>
        (\<lambda>n. f n \<acute> pp_b_action \<sigma> [n] x)"
      have maps: "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
          Elem (?G x) (pp_e_domain \<tau>)"
      proof -
        fix x
        assume x: "Elem x (pp_e_domain \<sigma>)"
        have outputs: "pp_e_typed_sequence \<tau>
            (\<lambda>n. f n \<acute> pp_b_action \<sigma> [n] x)"
          by (rule pp_e_branch_output_typed[OF fseq x])
        show "Elem (?G x) (pp_e_domain \<tau>)"
          by (rule tau_domain[OF outputs])
      qed
      have function_member:
          "Elem (Lambda (pp_e_domain \<sigma>) ?G)
            (Fun (pp_e_domain \<sigma>) (pp_e_domain \<tau>))"
        using maps by (simp add: Elem_Lambda_Fun)
      have respects:
          "\<forall>i x y.
            Elem x (pp_e_domain \<sigma>) \<longrightarrow>
            Elem y (pp_e_domain \<sigma>) \<longrightarrow>
            pp_b_action \<sigma> i x = pp_b_action \<sigma> i y \<longrightarrow>
            pp_b_action \<tau> i
              ((Lambda (pp_e_domain \<sigma>) ?G) \<acute> x) =
            pp_b_action \<tau> i
              ((Lambda (pp_e_domain \<sigma>) ?G) \<acute> y)"
      proof (intro allI impI)
        fix i x y
        assume x: "Elem x (pp_e_domain \<sigma>)"
          and y: "Elem y (pp_e_domain \<sigma>)"
          and same: "pp_b_action \<sigma> i x = pp_b_action \<sigma> i y"
        show "pp_b_action \<tau> i
              ((Lambda (pp_e_domain \<sigma>) ?G) \<acute> x) =
            pp_b_action \<tau> i
              ((Lambda (pp_e_domain \<sigma>) ?G) \<acute> y)"
        proof (cases "i = []")
          case True
          have xy: "x = y"
            using same pp_b_action_one_all[OF x]
              pp_b_action_one_all[OF y] True by simp
          show ?thesis using xy by simp
        next
          case False
          obtain k n where i: "i = k @ [n]"
            using pp_e_nonempty_word_snoc[OF False] by blast
          have ax: "Elem (pp_b_action \<sigma> [n] x) (pp_e_domain \<sigma>)"
            by (rule pp_b_action_closed_all[OF x])
          have ay: "Elem (pp_b_action \<sigma> [n] y) (pp_e_domain \<sigma>)"
            by (rule pp_b_action_closed_all[OF y])
          have inputs:
              "pp_b_action \<sigma> k (pp_b_action \<sigma> [n] x) =
               pp_b_action \<sigma> k (pp_b_action \<sigma> [n] y)"
            using pp_b_action_comp_all[OF x, of k "[n]"]
              pp_b_action_comp_all[OF y, of k "[n]"] same i by simp
          have fn:
              "Elem (f n) (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
            using fseq unfolding pp_e_typed_sequence_def by blast
          have component:
              "pp_b_action \<tau> k
                (f n \<acute> pp_b_action \<sigma> [n] x) =
               pp_b_action \<tau> k
                (f n \<acute> pp_b_action \<sigma> [n] y)"
            by (rule pp_b_arrow_member_respects[OF fn ax ay inputs])
          have outputs_x: "pp_e_typed_sequence \<tau>
              (\<lambda>m. f m \<acute> pp_b_action \<sigma> [m] x)"
            by (rule pp_e_branch_output_typed[OF fseq x])
          have outputs_y: "pp_e_typed_sequence \<tau>
              (\<lambda>m. f m \<acute> pp_b_action \<sigma> [m] y)"
            by (rule pp_e_branch_output_typed[OF fseq y])
          have cone_x:
              "pp_b_action \<tau> [n] (?G x) =
               f n \<acute> pp_b_action \<sigma> [n] x"
            by (rule tau_action[OF outputs_x])
          have cone_y:
              "pp_b_action \<tau> [n] (?G y) =
               f n \<acute> pp_b_action \<sigma> [n] y"
            by (rule tau_action[OF outputs_y])
          have Gx: "Elem (?G x) (pp_e_domain \<tau>)"
            by (rule maps[OF x])
          have Gy: "Elem (?G y) (pp_e_domain \<tau>)"
            by (rule maps[OF y])
          have left:
              "pp_b_action \<tau> i (?G x) =
               pp_b_action \<tau> k
                (f n \<acute> pp_b_action \<sigma> [n] x)"
            using pp_b_action_comp_all[OF Gx, of k "[n]"]
              cone_x i by simp
          have right:
              "pp_b_action \<tau> i (?G y) =
               pp_b_action \<tau> k
                (f n \<acute> pp_b_action \<sigma> [n] y)"
            using pp_b_action_comp_all[OF Gy, of k "[n]"]
              cone_y i by simp
          show ?thesis
            using x y left component right by (simp add: Lambda_app)
        qed
      qed
      show "Elem (pp_e_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
        unfolding pp_e_branch_glue.simps
        by (rule iffD2[OF pp_b_arrow_domain_iff])
          (rule conjI[OF function_member respects])
    qed
    show "\<forall>f. pp_e_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<longrightarrow>
        Elem (pp_e_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f)
          (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
      by (rule arr_domain)
    show "\<forall>f n. pp_e_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f \<longrightarrow>
        pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) [n]
          (pp_e_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f) = f n"
    proof (intro allI impI)
      fix f n
      assume fseq: "pp_e_typed_sequence (\<sigma> \<rightarrow>\<^sub>o \<tau>) f"
      let ?G = "pp_e_branch_glue (\<sigma> \<rightarrow>\<^sub>o \<tau>) f"
      have G: "Elem ?G (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
        using arr_domain fseq by blast
      have action_G:
          "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) [n] ?G)
            (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
        by (rule pp_b_action_closed_all[OF G])
      have fn: "Elem (f n) (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
        using fseq unfolding pp_e_typed_sequence_def by blast
      show "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) [n] ?G = f n"
      proof (rule pp_b_function_ext[
          OF pp_b_arrow_member_function[OF action_G]
             pp_b_arrow_member_function[OF fn]])
        fix x
        assume x: "Elem x (pp_e_domain \<sigma>)"
        have lift_x:
            "Elem (pp_b_lift \<sigma> [n] x) (pp_e_domain \<sigma>)"
          by (rule pp_b_structure_lift_closed[
            OF pp_b_mset_structure_all x])
        have outputs: "pp_e_typed_sequence \<tau>
            (\<lambda>m. f m \<acute>
              pp_b_action \<sigma> [m] (pp_b_lift \<sigma> [n] x))"
          by (rule pp_e_branch_output_typed[OF fseq lift_x])
        have cone:
            "pp_b_action \<tau> [n]
              (pp_e_branch_glue \<tau>
                (\<lambda>m. f m \<acute>
                  pp_b_action \<sigma> [m] (pp_b_lift \<sigma> [n] x))) =
             f n \<acute>
               pp_b_action \<sigma> [n] (pp_b_lift \<sigma> [n] x)"
          by (rule tau_action[OF outputs])
        have recover:
            "pp_b_action \<sigma> [n] (pp_b_lift \<sigma> [n] x) = x"
          by (rule pp_b_structure_action_lift[
            OF pp_b_mset_structure_all x])
        show "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) [n] ?G \<acute> x =
            f n \<acute> x"
          using pp_b_arrow_action_apply[OF x, of \<tau> "[n]" ?G]
            lift_x cone recover
          by (simp add: Lambda_app)
      qed
    qed
qed
qed

theorem pp_e_branch_glue_in_domain:
  assumes prop_type: "pp_e_propositional_type \<sigma>"
    and typed: "pp_e_typed_sequence \<sigma> a"
  shows "Elem (pp_e_branch_glue \<sigma> a) (pp_e_domain \<sigma>)"
  using pp_e_branch_glue_invariant_all prop_type typed
  unfolding pp_e_branch_glue_invariant_def by blast

theorem pp_e_branch_glue_action:
  assumes prop_type: "pp_e_propositional_type \<sigma>"
    and typed: "pp_e_typed_sequence \<sigma> a"
  shows "pp_b_action \<sigma> [n] (pp_e_branch_glue \<sigma> a) = a n"
  using pp_e_branch_glue_invariant_all prop_type typed
  unfolding pp_e_branch_glue_invariant_def by blast

theorem pp_e_Bacon_10_1_elements:
  assumes prop_type: "pp_e_propositional_type \<sigma>"
    and typed: "\<And>n. Elem (a n) (pp_e_domain \<sigma>)"
  shows "\<exists>x. Elem x (pp_e_domain \<sigma>) \<and>
    (\<forall>n. pp_b_action \<sigma> [n] x = a n)"
proof -
  have sequence: "pp_e_typed_sequence \<sigma> a"
    using typed unfolding pp_e_typed_sequence_def by blast
  have domain: "Elem (pp_e_branch_glue \<sigma> a) (pp_e_domain \<sigma>)"
    by (rule pp_e_branch_glue_in_domain[OF prop_type sequence])
  have actions: "\<forall>n.
      pp_b_action \<sigma> [n] (pp_e_branch_glue \<sigma> a) = a n"
    using pp_e_branch_glue_action[OF prop_type sequence] by blast
  show ?thesis
    using domain actions by blast
qed

definition pp_e_Bacon_glued_constants ::
    "(nat \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow>
      string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_e_Bacon_glued_constants A c \<sigma> =
    (if pp_e_propositional_type \<sigma>
     then pp_e_branch_glue \<sigma> (\<lambda>n. A n c \<sigma>)
     else pp_e_default \<sigma>)"

lemma pp_e_Bacon_glued_constants_typed:
  assumes family:
      "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
  shows "Elem (pp_e_Bacon_glued_constants A c \<sigma>)
    (pp_e_domain \<sigma>)"
proof (cases "pp_e_propositional_type \<sigma>")
  case True
  have sequence: "pp_e_typed_sequence \<sigma> (\<lambda>n. A n c \<sigma>)"
    using family[OF True]
    unfolding pp_e_typed_sequence_def by blast
  show ?thesis
    unfolding pp_e_Bacon_glued_constants_def
    using True pp_e_branch_glue_in_domain[OF True sequence] by simp
next
  case False
  show ?thesis
    unfolding pp_e_Bacon_glued_constants_def
    using False pp_e_default_in_domain by simp
qed

lemma pp_e_Bacon_glued_constants_action:
  assumes family:
      "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and prop_type: "pp_e_propositional_type \<sigma>"
  shows "pp_b_action \<sigma> [n]
      (pp_e_Bacon_glued_constants A c \<sigma>) = A n c \<sigma>"
proof -
  have sequence: "pp_e_typed_sequence \<sigma> (\<lambda>m. A m c \<sigma>)"
    using family[OF prop_type]
    unfolding pp_e_typed_sequence_def by blast
  show ?thesis
    unfolding pp_e_Bacon_glued_constants_def
    using prop_type pp_e_branch_glue_action[
      OF prop_type sequence, of n] by simp
qed

fun pp_e_propositional_term :: "oterm \<Rightarrow> bool" where
  "pp_e_propositional_term (Var n) = True"
| "pp_e_propositional_term (Const c \<sigma>) =
    pp_e_propositional_type \<sigma>"
| "pp_e_propositional_term (App M N) =
    (pp_e_propositional_term M \<and> pp_e_propositional_term N)"
| "pp_e_propositional_term (Lam \<sigma> M) =
    (pp_e_propositional_type \<sigma> \<and> pp_e_propositional_term M)"
| "pp_e_propositional_term (Eq \<sigma> M N) =
    (pp_e_propositional_type \<sigma> \<and>
     pp_e_propositional_term M \<and> pp_e_propositional_term N)"
| "pp_e_propositional_term (Neg A) = pp_e_propositional_term A"
| "pp_e_propositional_term (Conj A B) =
    (pp_e_propositional_term A \<and> pp_e_propositional_term B)"
| "pp_e_propositional_term (Disj A B) =
    (pp_e_propositional_term A \<and> pp_e_propositional_term B)"
| "pp_e_propositional_term (Imp A B) =
    (pp_e_propositional_term A \<and> pp_e_propositional_term B)"
| "pp_e_propositional_term (Forall \<sigma> A) =
    (pp_e_propositional_type \<sigma> \<and> pp_e_propositional_term A)"
| "pp_e_propositional_term (Exists \<sigma> A) =
    (pp_e_propositional_type \<sigma> \<and> pp_e_propositional_term A)"

definition pp_e_Bacon_completed_constants ::
    "(nat \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF) \<Rightarrow>
      nat \<Rightarrow> string \<Rightarrow> otype \<Rightarrow> ZF"
where
  "pp_e_Bacon_completed_constants A n c \<sigma> =
    (if pp_e_propositional_type \<sigma>
     then A n c \<sigma>
     else pp_e_default \<sigma>)"

lemma pp_e_Bacon_completed_constants_typed:
  assumes family:
      "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
  shows "Elem (pp_e_Bacon_completed_constants A n c \<sigma>)
    (pp_e_domain \<sigma>)"
  using family[of \<sigma> n c] pp_e_default_in_domain[of \<sigma>]
  by (simp add: pp_e_Bacon_completed_constants_def)

lemma pp_e_Bacon_glued_completed_action:
  assumes family:
      "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
  shows "pp_b_action \<sigma> [n]
      (pp_e_Bacon_glued_constants A c \<sigma>) =
    pp_e_Bacon_completed_constants A n c \<sigma>"
proof (cases "pp_e_propositional_type \<sigma>")
  case True
  show ?thesis
    using pp_e_Bacon_glued_constants_action[OF family True]
    by (simp add: pp_e_Bacon_completed_constants_def True)
next
  case False
  show ?thesis
    using pp_b_structure_action_default[
      OF pp_b_mset_structure_all, where i="[n]"]
    by (simp add: pp_e_Bacon_glued_constants_def
        pp_e_Bacon_completed_constants_def False)
qed

lemma pp_e_eval_completed_constants_propositional:
  assumes fragment: "pp_e_propositional_term M"
  shows "pp_e_eval (pp_e_Bacon_completed_constants A n) \<rho> M =
    pp_e_eval (A n) \<rho> M"
  using fragment
  by (induction M arbitrary: \<rho>)
    (simp_all add: pp_e_Bacon_completed_constants_def)

locale pp_e_action_related_constants =
  pp_e_constants C + Right: pp_e_constants D
  for C D :: "string \<Rightarrow> otype \<Rightarrow> ZF"
    and j :: pp_word +
  assumes C_action:
    "pp_b_action \<sigma> j (C c \<sigma>) = D c \<sigma>"
begin

theorem pp_e_eval_action_related:
  assumes typed: "\<Gamma> \<turnstile> M : \<tau>"
    and source: "pp_e_env_typed \<Gamma> \<rho>"
    and rel: "pp_e_env_action \<Gamma> j \<rho> \<eta>"
  shows "pp_b_action \<tau> j (pp_e_eval C \<rho> M) =
    pp_e_eval D \<eta> M"
  using typed source rel
proof (induction arbitrary: \<rho> \<eta> rule: has_type.induct)
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
      "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
          (pp_e_eval C \<rho> M) =
       pp_e_eval D \<eta> M"
    by (rule App.IH(1)[OF App.prems])
  have a_commute:
      "pp_b_action \<sigma> j (pp_e_eval C \<rho> N) =
       pp_e_eval D \<eta> N"
    by (rule App.IH(2)[OF App.prems])
  show ?case
    using pp_b_application_substitution_exact[OF f a, of j]
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
      "Elem (pp_e_eval D \<eta> (Lam \<sigma> M))
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    using Right.pp_e_eval_type[OF lam_typed target_env]
    by (simp add: pp_e_dom_def)
  have acted:
      "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
        (pp_e_eval C \<rho> (Lam \<sigma> M)))
        (pp_e_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_action_closed_all[OF source_lam])
  show ?case
  proof (rule pp_b_function_ext[
      OF pp_b_arrow_member_function[OF acted]
         pp_b_arrow_member_function[OF target_lam]])
    fix a
    assume a: "Elem a (pp_e_domain \<sigma>)"
    let ?x = "pp_b_lift \<sigma> j a"
    have x: "Elem ?x (pp_e_domain \<sigma>)"
      by (rule pp_b_structure_lift_closed[
          OF pp_b_mset_structure_all a])
    have ax: "pp_b_action \<sigma> j ?x = a"
      by (rule pp_b_structure_action_lift[
          OF pp_b_mset_structure_all a])
    have source_ext:
        "pp_e_env_typed (\<sigma> # \<Gamma>) (extend_env ?x \<rho>)"
      by (rule pp_e_env_typed_extend[OF Lam.prems(1) x])
    have rel_ext:
        "pp_e_env_action (\<sigma> # \<Gamma>) j
          (extend_env ?x \<rho>) (extend_env a \<eta>)"
      by (rule pp_e_env_action_extend[
          where b=a and \<sigma>=\<sigma> and a="?x",
          OF Lam.prems(2) ax[symmetric]])
    have body:
        "pp_b_action \<tau> j
          (pp_e_eval C (extend_env ?x \<rho>) M) =
         pp_e_eval D (extend_env a \<eta>) M"
      by (rule Lam.IH[OF source_ext rel_ext])
    show "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
          (pp_e_eval C \<rho> (Lam \<sigma> M)) \<acute> a =
        pp_e_eval D \<eta> (Lam \<sigma> M) \<acute> a"
      using pp_b_arrow_action_apply[
          OF a, of \<tau> j "pp_e_eval C \<rho> (Lam \<sigma> M)"]
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
      "pp_b_action \<sigma> j (pp_e_eval C \<rho> M) =
       pp_e_eval D \<eta> M"
    by (rule Eq.IH(1)[OF Eq.prems])
  have Nc:
      "pp_b_action \<sigma> j (pp_e_eval C \<rho> N) =
       pp_e_eval D \<eta> N"
    by (rule Eq.IH(2)[OF Eq.prems])
  have eq_source:
      "Elem (pp_e_eval C \<rho> (Eq \<sigma> M N)) (pp_e_domain Prop)"
    by (simp only: pp_e_eval.simps; rule pp_e_prop_in_domain)
  have left:
      "Elem (pp_b_action Prop j (pp_e_eval C \<rho> (Eq \<sigma> M N)))
        (pp_e_domain Prop)"
    by (rule pp_b_action_closed_all[OF eq_source])
  have right:
      "Elem (pp_e_eval D \<eta> (Eq \<sigma> M N)) (pp_e_domain Prop)"
    by (simp only: pp_e_eval.simps; rule pp_e_prop_in_domain)
  show ?case
  proof (rule pp_e_prop_ext[OF left right])
    fix w
    have local:
        "pp_e_eqv \<sigma> (rev j @ w)
            (pp_e_eval C \<rho> M) (pp_e_eval C \<rho> N)
        \<longleftrightarrow>
         pp_e_eqv \<sigma> w
            (pp_e_eval D \<eta> M) (pp_e_eval D \<eta> N)"
      using pp_e_eqv_action_shift[OF Mx Nx, of j w] Mc Nc
      by simp
    show "pp_e_holds
        (pp_b_action Prop j (pp_e_eval C \<rho> (Eq \<sigma> M N))) w =
      pp_e_holds (pp_e_eval D \<eta> (Eq \<sigma> M N)) w"
      using local by simp
  qed
next
  case (Neg \<Gamma> A)
  have Ac: "pp_b_action Prop j (pp_e_eval C \<rho> A) =
      pp_e_eval D \<eta> A"
    by (rule Neg.IH[OF Neg.prems])
  have Ah: "pp_e_holds (pp_e_eval C \<rho> A) (rev j @ w) =
      pp_e_holds (pp_e_eval D \<eta> A) w" for w
    by (rule pp_e_holds_from_action_eq[OF Ac])
  show ?case
  proof (rule pp_e_prop_ext)
    show "Elem (pp_b_action Prop j (pp_e_eval C \<rho> (Neg A)))
        (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps;
          rule pp_b_action_closed_all[OF pp_e_prop_in_domain])
    show "Elem (pp_e_eval D \<eta> (Neg A)) (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps; rule pp_e_prop_in_domain)
    fix w
    show "pp_e_holds
        (pp_b_action Prop j (pp_e_eval C \<rho> (Neg A))) w =
      pp_e_holds (pp_e_eval D \<eta> (Neg A)) w"
      using Ah[of w] by simp
  qed
next
  case (Conj \<Gamma> A B)
  have Ac: "pp_b_action Prop j (pp_e_eval C \<rho> A) =
      pp_e_eval D \<eta> A"
    by (rule Conj.IH(1)[OF Conj.prems])
  have Bc: "pp_b_action Prop j (pp_e_eval C \<rho> B) =
      pp_e_eval D \<eta> B"
    by (rule Conj.IH(2)[OF Conj.prems])
  have Ah: "pp_e_holds (pp_e_eval C \<rho> A) (rev j @ w) =
      pp_e_holds (pp_e_eval D \<eta> A) w" for w
    by (rule pp_e_holds_from_action_eq[OF Ac])
  have Bh: "pp_e_holds (pp_e_eval C \<rho> B) (rev j @ w) =
      pp_e_holds (pp_e_eval D \<eta> B) w" for w
    by (rule pp_e_holds_from_action_eq[OF Bc])
  show ?case
  proof (rule pp_e_prop_ext)
    show "Elem (pp_b_action Prop j (pp_e_eval C \<rho> (Conj A B)))
        (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps;
          rule pp_b_action_closed_all[OF pp_e_prop_in_domain])
    show "Elem (pp_e_eval D \<eta> (Conj A B)) (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps; rule pp_e_prop_in_domain)
    fix w
    show "pp_e_holds
        (pp_b_action Prop j (pp_e_eval C \<rho> (Conj A B))) w =
      pp_e_holds (pp_e_eval D \<eta> (Conj A B)) w"
      using Ah[of w] Bh[of w] by simp
  qed
next
  case (Disj \<Gamma> A B)
  have Ac: "pp_b_action Prop j (pp_e_eval C \<rho> A) =
      pp_e_eval D \<eta> A"
    by (rule Disj.IH(1)[OF Disj.prems])
  have Bc: "pp_b_action Prop j (pp_e_eval C \<rho> B) =
      pp_e_eval D \<eta> B"
    by (rule Disj.IH(2)[OF Disj.prems])
  have Ah: "pp_e_holds (pp_e_eval C \<rho> A) (rev j @ w) =
      pp_e_holds (pp_e_eval D \<eta> A) w" for w
    by (rule pp_e_holds_from_action_eq[OF Ac])
  have Bh: "pp_e_holds (pp_e_eval C \<rho> B) (rev j @ w) =
      pp_e_holds (pp_e_eval D \<eta> B) w" for w
    by (rule pp_e_holds_from_action_eq[OF Bc])
  show ?case
  proof (rule pp_e_prop_ext)
    show "Elem (pp_b_action Prop j (pp_e_eval C \<rho> (Disj A B)))
        (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps;
          rule pp_b_action_closed_all[OF pp_e_prop_in_domain])
    show "Elem (pp_e_eval D \<eta> (Disj A B)) (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps; rule pp_e_prop_in_domain)
    fix w
    show "pp_e_holds
        (pp_b_action Prop j (pp_e_eval C \<rho> (Disj A B))) w =
      pp_e_holds (pp_e_eval D \<eta> (Disj A B)) w"
      using Ah[of w] Bh[of w] by simp
  qed
next
  case (Imp \<Gamma> A B)
  have Ac: "pp_b_action Prop j (pp_e_eval C \<rho> A) =
      pp_e_eval D \<eta> A"
    by (rule Imp.IH(1)[OF Imp.prems])
  have Bc: "pp_b_action Prop j (pp_e_eval C \<rho> B) =
      pp_e_eval D \<eta> B"
    by (rule Imp.IH(2)[OF Imp.prems])
  have Ah: "pp_e_holds (pp_e_eval C \<rho> A) (rev j @ w) =
      pp_e_holds (pp_e_eval D \<eta> A) w" for w
    by (rule pp_e_holds_from_action_eq[OF Ac])
  have Bh: "pp_e_holds (pp_e_eval C \<rho> B) (rev j @ w) =
      pp_e_holds (pp_e_eval D \<eta> B) w" for w
    by (rule pp_e_holds_from_action_eq[OF Bc])
  show ?case
  proof (rule pp_e_prop_ext)
    show "Elem (pp_b_action Prop j (pp_e_eval C \<rho> (Imp A B)))
        (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps;
          rule pp_b_action_closed_all[OF pp_e_prop_in_domain])
    show "Elem (pp_e_eval D \<eta> (Imp A B)) (pp_e_domain Prop)"
      by (simp only: pp_e_eval.simps; rule pp_e_prop_in_domain)
    fix w
    show "pp_e_holds
        (pp_b_action Prop j (pp_e_eval C \<rho> (Imp A B))) w =
      pp_e_holds (pp_e_eval D \<eta> (Imp A B)) w"
      using Ah[of w] Bh[of w] by simp
  qed
next
  case (Forall \<sigma> \<Gamma> A)
  let ?F = "\<lambda>x. pp_e_eval C (extend_env x \<rho>) A"
  let ?G = "\<lambda>a. pp_e_eval D (extend_env a \<eta>) A"
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
    using Right.pp_e_eval_type[OF Forall.hyps]
      pp_e_env_typed_extend[OF target]
    by (simp add: pp_e_dom_def)
  have commute:
      "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
        pp_b_action Prop j (?F x) =
          ?G (pp_b_action \<sigma> j x)"
  proof -
    fix x
    assume x: "Elem x (pp_e_domain \<sigma>)"
    have ax: "Elem (pp_b_action \<sigma> j x) (pp_e_domain \<sigma>)"
      by (rule pp_b_action_closed_all[OF x])
    have source_ext:
        "pp_e_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
      by (rule pp_e_env_typed_extend[OF Forall.prems(1) x])
    have rel_ext:
        "pp_e_env_action (\<sigma> # \<Gamma>) j
          (extend_env x \<rho>)
          (extend_env (pp_b_action \<sigma> j x) \<eta>)"
      by (rule pp_e_env_action_extend[OF Forall.prems(2)]) simp
    show "pp_b_action Prop j (?F x) =
        ?G (pp_b_action \<sigma> j x)"
      by (rule Forall.IH[OF source_ext rel_ext])
  qed
  show ?case
  proof -
    note quant = pp_e_action_bounded_forall[
      where F="\<lambda>x. pp_e_eval C (extend_env x \<rho>) A"
        and G="\<lambda>a. pp_e_eval D (extend_env a \<eta>) A"
        and \<sigma>=\<sigma> and i=j,
      OF F G commute]
    show ?thesis using quant by simp
  qed
next
  case (Exists \<sigma> \<Gamma> A)
  let ?F = "\<lambda>x. pp_e_eval C (extend_env x \<rho>) A"
  let ?G = "\<lambda>a. pp_e_eval D (extend_env a \<eta>) A"
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
    using Right.pp_e_eval_type[OF Exists.hyps]
      pp_e_env_typed_extend[OF target]
    by (simp add: pp_e_dom_def)
  have commute:
      "\<And>x. Elem x (pp_e_domain \<sigma>) \<Longrightarrow>
        pp_b_action Prop j (?F x) =
          ?G (pp_b_action \<sigma> j x)"
  proof -
    fix x
    assume x: "Elem x (pp_e_domain \<sigma>)"
    have source_ext:
        "pp_e_env_typed (\<sigma> # \<Gamma>) (extend_env x \<rho>)"
      by (rule pp_e_env_typed_extend[OF Exists.prems(1) x])
    have rel_ext:
        "pp_e_env_action (\<sigma> # \<Gamma>) j
          (extend_env x \<rho>)
          (extend_env (pp_b_action \<sigma> j x) \<eta>)"
      by (rule pp_e_env_action_extend[OF Exists.prems(2)]) simp
    show "pp_b_action Prop j (?F x) =
        ?G (pp_b_action \<sigma> j x)"
      by (rule Exists.IH[OF source_ext rel_ext])
  qed
  show ?case
  proof -
    note quant = pp_e_action_bounded_exists[
      where F="\<lambda>x. pp_e_eval C (extend_env x \<rho>) A"
        and G="\<lambda>a. pp_e_eval D (extend_env a \<eta>) A"
        and \<sigma>=\<sigma> and i=j,
      OF F G commute]
    show ?thesis using quant by simp
  qed
qed

end

lemma pp_e_Bacon_10_1_term_action:
  assumes family:
      "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
    and typed: "[] \<turnstile> M : \<tau>"
    and fragment: "pp_e_propositional_term M"
  shows "pp_b_action \<tau> [n]
      (pp_e_eval (pp_e_Bacon_glued_constants A) pp_e_closed_env M) =
    pp_e_eval (A n) pp_e_closed_env M"
proof -
  interpret Related: pp_e_action_related_constants
      "pp_e_Bacon_glued_constants A"
      "pp_e_Bacon_completed_constants A n" "[n]"
  proof
    show "Elem (pp_e_Bacon_glued_constants A c \<sigma>)
        (pp_e_domain \<sigma>)" for c \<sigma>
      by (rule pp_e_Bacon_glued_constants_typed[OF family])
    show "Elem (pp_e_Bacon_completed_constants A n c \<sigma>)
        (pp_e_domain \<sigma>)" for c \<sigma>
      by (rule pp_e_Bacon_completed_constants_typed[OF family])
    show "pp_b_action \<sigma> [n]
        (pp_e_Bacon_glued_constants A c \<sigma>) =
      pp_e_Bacon_completed_constants A n c \<sigma>" for \<sigma> c
      by (rule pp_e_Bacon_glued_completed_action[OF family])
  qed
  have source: "pp_e_env_typed [] pp_e_closed_env"
    by (simp add: pp_e_env_typed_def lookup_def)
  have rel:
      "pp_e_env_action [] [n] pp_e_closed_env pp_e_closed_env"
    by (simp add: pp_e_env_action_def lookup_def)
  have action:
      "pp_b_action \<tau> [n]
        (pp_e_eval (pp_e_Bacon_glued_constants A) pp_e_closed_env M) =
       pp_e_eval (pp_e_Bacon_completed_constants A n) pp_e_closed_env M"
    by (rule Related.pp_e_eval_action_related[OF typed source rel])
  show ?thesis
    using action pp_e_eval_completed_constants_propositional[
      OF fragment, of A n pp_e_closed_env] by simp
qed

theorem pp_e_Bacon_10_1:
  assumes family:
      "\<And>n c \<sigma>. pp_e_propositional_type \<sigma> \<Longrightarrow>
        Elem (A n c \<sigma>) (pp_e_domain \<sigma>)"
  shows "\<exists>C.
    (\<forall>c \<sigma>. Elem (C c \<sigma>) (pp_e_domain \<sigma>))
    \<and>
    (\<forall>n c \<sigma>. pp_e_propositional_type \<sigma> \<longrightarrow>
      pp_b_action \<sigma> [n] (C c \<sigma>) = A n c \<sigma>)
    \<and>
    (\<forall>n M \<tau>.
      [] \<turnstile> M : \<tau> \<longrightarrow>
      pp_e_propositional_term M \<longrightarrow>
      pp_b_action \<tau> [n]
        (pp_e_eval C pp_e_closed_env M) =
      pp_e_eval (A n) pp_e_closed_env M)"
proof (rule exI[where x="pp_e_Bacon_glued_constants A"])
  show "(\<forall>c \<sigma>. Elem (pp_e_Bacon_glued_constants A c \<sigma>)
          (pp_e_domain \<sigma>))
      \<and>
      (\<forall>n c \<sigma>. pp_e_propositional_type \<sigma> \<longrightarrow>
        pp_b_action \<sigma> [n]
          (pp_e_Bacon_glued_constants A c \<sigma>) = A n c \<sigma>)
      \<and>
      (\<forall>n M \<tau>. [] \<turnstile> M : \<tau> \<longrightarrow>
        pp_e_propositional_term M \<longrightarrow>
        pp_b_action \<tau> [n]
          (pp_e_eval (pp_e_Bacon_glued_constants A) pp_e_closed_env M) =
        pp_e_eval (A n) pp_e_closed_env M)"
  proof (rule conjI)
    show "\<forall>c \<sigma>. Elem (pp_e_Bacon_glued_constants A c \<sigma>)
        (pp_e_domain \<sigma>)"
      by (intro allI; rule pp_e_Bacon_glued_constants_typed[OF family])
  next
    show "(\<forall>n c \<sigma>. pp_e_propositional_type \<sigma> \<longrightarrow>
          pp_b_action \<sigma> [n]
            (pp_e_Bacon_glued_constants A c \<sigma>) = A n c \<sigma>)
        \<and>
        (\<forall>n M \<tau>. [] \<turnstile> M : \<tau> \<longrightarrow>
          pp_e_propositional_term M \<longrightarrow>
          pp_b_action \<tau> [n]
            (pp_e_eval (pp_e_Bacon_glued_constants A) pp_e_closed_env M) =
          pp_e_eval (A n) pp_e_closed_env M)"
    proof (rule conjI)
      show "\<forall>n c \<sigma>. pp_e_propositional_type \<sigma> \<longrightarrow>
          pp_b_action \<sigma> [n]
            (pp_e_Bacon_glued_constants A c \<sigma>) = A n c \<sigma>"
        by (intro allI impI;
          rule pp_e_Bacon_glued_constants_action[OF family])
    next
      show "\<forall>n M \<tau>. [] \<turnstile> M : \<tau> \<longrightarrow>
          pp_e_propositional_term M \<longrightarrow>
          pp_b_action \<tau> [n]
            (pp_e_eval (pp_e_Bacon_glued_constants A) pp_e_closed_env M) =
          pp_e_eval (A n) pp_e_closed_env M"
        by (intro allI impI;
          rule pp_e_Bacon_10_1_term_action[OF family])
    qed
  qed
qed

end
