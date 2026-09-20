theory Bacon_PP_ZF_Full_MSet
  imports 
    "Goodman_Exact_Legacy_01.Bacon_PP_ZF_Word_Propositions"
begin

section \<open>The exact all-type surjective M-set construction\<close>

text \<open>
  This is a direct HOL-ZF transcription of Bacon's Definitions 7.1, 7.2,
  and 8.1.  The individual domain is chosen to be a singleton surjective M-set;
  the proposition domain is \<open>Power Nat\<close>, coding
  \<open>Pow (nat list)\<close> exactly.

  At an arrow type, membership is precisely Bacon's condition

      if i x = i y, then i (f x) = i (f y).

  The action uses the canonical preimage supplied by \<open>pp_b_lift\<close>.
  Establishing closure and surjectivity of this mutual recursion is the
  all-type form of Bacon's Proposition 8; it is stated only after those
  obligations have been proved.
\<close>

fun pp_b_domain :: "otype \<Rightarrow> ZF"
and pp_b_action :: "otype \<Rightarrow> pp_word \<Rightarrow> ZF \<Rightarrow> ZF"
and pp_b_lift :: "otype \<Rightarrow> pp_word \<Rightarrow> ZF \<Rightarrow> ZF"
where
  "pp_b_domain Ind = Singleton Empty"
| "pp_b_domain Prop = Power Nat"
| "pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    Sep (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))
      (\<lambda>f. \<forall>i x y.
        Elem x (pp_b_domain \<sigma>) \<longrightarrow>
        Elem y (pp_b_domain \<sigma>) \<longrightarrow>
        pp_b_action \<sigma> i x = pp_b_action \<sigma> i y \<longrightarrow>
        pp_b_action \<tau> i (f \<acute> x) =
          pp_b_action \<tau> i (f \<acute> y))"
| "pp_b_action Ind i x = x"
| "pp_b_action Prop i P = pp_n_prop_action i P"
| "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f =
    Lambda (pp_b_domain \<sigma>)
      (\<lambda>x. pp_b_action \<tau> i
        (f \<acute> pp_b_lift \<sigma> i x))"
| "pp_b_lift Ind i x = x"
| "pp_b_lift Prop i P = pp_n_prop_lift i P"
| "pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f =
    Lambda (pp_b_domain \<sigma>)
      (\<lambda>x. pp_b_lift \<tau> i
        (f \<acute> pp_b_action \<sigma> i x))"

subsection \<open>Literal correspondence with Bacon's clauses\<close>

lemma pp_b_individual_domain:
  "pp_b_domain Ind = Singleton Empty"
  by simp

lemma pp_b_proposition_domain:
  "pp_b_domain Prop = Power Nat"
  by simp

lemma pp_b_arrow_domain_iff:
  "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<longleftrightarrow>
    Elem f (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>)) \<and>
    (\<forall>i x y.
      Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      Elem y (pp_b_domain \<sigma>) \<longrightarrow>
      pp_b_action \<sigma> i x = pp_b_action \<sigma> i y \<longrightarrow>
      pp_b_action \<tau> i (f \<acute> x) =
        pp_b_action \<tau> i (f \<acute> y))"
  by (simp add: Sep)

lemma pp_b_arrow_action_apply:
  assumes x: "Elem x (pp_b_domain \<sigma>)"
  shows "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f \<acute> x =
    pp_b_action \<tau> i (f \<acute> pp_b_lift \<sigma> i x)"
  using x by (simp add: Lambda_app)

lemma pp_b_arrow_lift_apply:
  assumes x: "Elem x (pp_b_domain \<sigma>)"
  shows "pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f \<acute> x =
    pp_b_lift \<tau> i (f \<acute> pp_b_action \<sigma> i x)"
  using x by (simp add: Lambda_app)

lemma pp_b_arrow_member_function:
  assumes f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "Elem f (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
proof -
  have both:
      "Elem f (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>)) \<and>
       (\<forall>i x y.
        Elem x (pp_b_domain \<sigma>) \<longrightarrow>
        Elem y (pp_b_domain \<sigma>) \<longrightarrow>
        pp_b_action \<sigma> i x = pp_b_action \<sigma> i y \<longrightarrow>
        pp_b_action \<tau> i (f \<acute> x) =
          pp_b_action \<tau> i (f \<acute> y))"
    using f by (rule iffD1[OF pp_b_arrow_domain_iff])
  then show ?thesis by blast
qed

lemma pp_b_arrow_member_respects:
  assumes f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_b_domain \<sigma>)"
    and y: "Elem y (pp_b_domain \<sigma>)"
    and same: "pp_b_action \<sigma> i x = pp_b_action \<sigma> i y"
  shows "pp_b_action \<tau> i (f \<acute> x) =
    pp_b_action \<tau> i (f \<acute> y)"
proof -
  have respects:
      "\<forall>i x y.
        Elem x (pp_b_domain \<sigma>) \<longrightarrow>
        Elem y (pp_b_domain \<sigma>) \<longrightarrow>
        pp_b_action \<sigma> i x = pp_b_action \<sigma> i y \<longrightarrow>
        pp_b_action \<tau> i (f \<acute> x) =
          pp_b_action \<tau> i (f \<acute> y)"
    using f by (rule conjunct2[OF iffD1[OF pp_b_arrow_domain_iff]])
  show ?thesis using respects x y same by blast
qed

lemma pp_b_app_closed:
  assumes f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and x: "Elem x (pp_b_domain \<sigma>)"
  shows "Elem (f \<acute> x) (pp_b_domain \<tau>)"
proof -
  have f_fun: "Elem f (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF f])
  have is_fun: "isFun f"
    by (rule pp_zf_function_isFun[OF f_fun])
  have domain: "Domain f = pp_b_domain \<sigma>"
    by (rule pp_zf_function_domain[OF f_fun])
  have in_range: "Elem (f \<acute> x) (Range f)"
    using fun_value_in_range[OF is_fun] x domain by simp
  have range_subset: "subset (Range f) (pp_b_domain \<tau>)"
    by (rule Fun_Range[OF f_fun])
  show ?thesis
    using in_range range_subset by (auto simp: subset_def)
qed

lemma pp_b_function_ext:
  assumes f: "Elem f (Fun A B)"
    and g: "Elem g (Fun A B)"
    and pointwise: "\<And>x. Elem x A \<Longrightarrow> f \<acute> x = g \<acute> x"
  shows "f = g"
proof -
  obtain F where f_rep: "f = Lambda A F"
    using Elem_Fun_Lambda[OF f] by auto
  obtain G where g_rep: "g = Lambda A G"
    using Elem_Fun_Lambda[OF g] by auto
  have "\<And>x. Elem x A \<Longrightarrow> F x = G x"
    using pointwise unfolding f_rep g_rep by (simp add: Lambda_app)
  then show ?thesis
    unfolding f_rep g_rep by (simp add: Lambda_ext)
qed

lemma pp_b_prop_action_exact:
  "pp_b_action Prop i (pp_n_bacon_embed P) =
    pp_n_bacon_embed (pp_prop_action i P)"
  by (simp add: pp_n_prop_action_is_bacon_division)

subsection \<open>Canonical default values\<close>

fun pp_b_default :: "otype \<Rightarrow> ZF" where
  "pp_b_default Ind = Empty"
| "pp_b_default Prop = Empty"
| "pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>) =
    Lambda (pp_b_domain \<sigma>) (\<lambda>_. pp_b_default \<tau>)"

lemma pp_b_default_in_domain:
  "Elem (pp_b_default \<sigma>) (pp_b_domain \<sigma>)"
proof (induction \<sigma>)
  case Ind
  then show ?case by (simp add: Singleton)
next
  case Prop
  then show ?case by (simp add: Power subset_empty)
next
  case (Arr \<sigma> \<tau>)
  have function_member:
      "Elem (Lambda (pp_b_domain \<sigma>) (\<lambda>_. pp_b_default \<tau>))
        (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    using Arr.IH(2) by (simp add: Elem_Lambda_Fun)
  have respects:
      "\<forall>i x y.
        Elem x (pp_b_domain \<sigma>) \<longrightarrow>
        Elem y (pp_b_domain \<sigma>) \<longrightarrow>
        pp_b_action \<sigma> i x = pp_b_action \<sigma> i y \<longrightarrow>
        pp_b_action \<tau> i
          ((Lambda (pp_b_domain \<sigma>) (\<lambda>_. pp_b_default \<tau>)) \<acute> x) =
        pp_b_action \<tau> i
          ((Lambda (pp_b_domain \<sigma>) (\<lambda>_. pp_b_default \<tau>)) \<acute> y)"
    by (simp add: Lambda_app)
  show ?case
    unfolding pp_b_default.simps
    by (rule iffD2[OF pp_b_arrow_domain_iff])
      (rule conjI[OF function_member respects])
qed

subsection \<open>The simultaneous Proposition 8 invariant\<close>

definition pp_b_action_closed_at :: "otype \<Rightarrow> bool" where
  "pp_b_action_closed_at \<sigma> \<longleftrightarrow>
    (\<forall>i x. Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      Elem (pp_b_action \<sigma> i x) (pp_b_domain \<sigma>))"

definition pp_b_lift_closed_at :: "otype \<Rightarrow> bool" where
  "pp_b_lift_closed_at \<sigma> \<longleftrightarrow>
    (\<forall>i x. Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      Elem (pp_b_lift \<sigma> i x) (pp_b_domain \<sigma>))"

definition pp_b_action_one_at :: "otype \<Rightarrow> bool" where
  "pp_b_action_one_at \<sigma> \<longleftrightarrow>
    (\<forall>x. Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      pp_b_action \<sigma> [] x = x)"

definition pp_b_action_comp_at :: "otype \<Rightarrow> bool" where
  "pp_b_action_comp_at \<sigma> \<longleftrightarrow>
    (\<forall>i j x. Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      pp_b_action \<sigma> i (pp_b_action \<sigma> j x) =
        pp_b_action \<sigma> (i @ j) x)"

definition pp_b_action_lift_at :: "otype \<Rightarrow> bool" where
  "pp_b_action_lift_at \<sigma> \<longleftrightarrow>
    (\<forall>i x. Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      pp_b_action \<sigma> i (pp_b_lift \<sigma> i x) = x)"

definition pp_b_lift_one_at :: "otype \<Rightarrow> bool" where
  "pp_b_lift_one_at \<sigma> \<longleftrightarrow>
    (\<forall>x. Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      pp_b_lift \<sigma> [] x = x)"

definition pp_b_lift_comp_at :: "otype \<Rightarrow> bool" where
  "pp_b_lift_comp_at \<sigma> \<longleftrightarrow>
    (\<forall>i j x. Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      pp_b_lift \<sigma> j (pp_b_lift \<sigma> i x) =
        pp_b_lift \<sigma> (i @ j) x)"

definition pp_b_action_default_at :: "otype \<Rightarrow> bool" where
  "pp_b_action_default_at \<sigma> \<longleftrightarrow>
    (\<forall>i. pp_b_action \<sigma> i (pp_b_default \<sigma>) =
      pp_b_default \<sigma>)"

definition pp_b_lift_default_at :: "otype \<Rightarrow> bool" where
  "pp_b_lift_default_at \<sigma> \<longleftrightarrow>
    (\<forall>i. pp_b_lift \<sigma> i (pp_b_default \<sigma>) =
      pp_b_default \<sigma>)"

definition pp_b_incomparable_at :: "otype \<Rightarrow> bool" where
  "pp_b_incomparable_at \<sigma> \<longleftrightarrow>
    (\<forall>i j x. Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      (\<nexists>k. j = k @ i) \<longrightarrow>
      (\<nexists>k. i = k @ j) \<longrightarrow>
      pp_b_action \<sigma> j (pp_b_lift \<sigma> i x) =
        pp_b_default \<sigma>)"

definition pp_b_mset_structure :: "otype \<Rightarrow> bool" where
  "pp_b_mset_structure \<sigma> \<longleftrightarrow>
    pp_b_action_closed_at \<sigma> \<and>
    pp_b_lift_closed_at \<sigma> \<and>
    pp_b_action_one_at \<sigma> \<and>
    pp_b_action_comp_at \<sigma> \<and>
    pp_b_action_lift_at \<sigma> \<and>
    pp_b_lift_one_at \<sigma> \<and>
    pp_b_lift_comp_at \<sigma> \<and>
    pp_b_action_default_at \<sigma> \<and>
    pp_b_lift_default_at \<sigma> \<and>
    pp_b_incomparable_at \<sigma>"

lemma pp_b_structure_action_closed:
  assumes struct: "pp_b_mset_structure \<sigma>"
    and x: "Elem x (pp_b_domain \<sigma>)"
  shows "Elem (pp_b_action \<sigma> i x) (pp_b_domain \<sigma>)"
  using struct x unfolding pp_b_mset_structure_def
    pp_b_action_closed_at_def by blast

lemma pp_b_structure_lift_closed:
  assumes struct: "pp_b_mset_structure \<sigma>"
    and x: "Elem x (pp_b_domain \<sigma>)"
  shows "Elem (pp_b_lift \<sigma> i x) (pp_b_domain \<sigma>)"
  using struct x unfolding pp_b_mset_structure_def
    pp_b_lift_closed_at_def by blast

lemma pp_b_structure_action_comp:
  assumes struct: "pp_b_mset_structure \<sigma>"
    and x: "Elem x (pp_b_domain \<sigma>)"
  shows "pp_b_action \<sigma> i (pp_b_action \<sigma> j x) =
    pp_b_action \<sigma> (i @ j) x"
  using struct x unfolding pp_b_mset_structure_def
    pp_b_action_comp_at_def by blast

lemma pp_b_structure_action_lift:
  assumes struct: "pp_b_mset_structure \<sigma>"
    and x: "Elem x (pp_b_domain \<sigma>)"
  shows "pp_b_action \<sigma> i (pp_b_lift \<sigma> i x) = x"
  using struct x unfolding pp_b_mset_structure_def
    pp_b_action_lift_at_def by blast

lemma pp_b_structure_lift_comp:
  assumes struct: "pp_b_mset_structure \<sigma>"
    and x: "Elem x (pp_b_domain \<sigma>)"
  shows "pp_b_lift \<sigma> j (pp_b_lift \<sigma> i x) =
    pp_b_lift \<sigma> (i @ j) x"
  using struct x unfolding pp_b_mset_structure_def
    pp_b_lift_comp_at_def by blast

lemma pp_b_structure_action_one:
  assumes struct: "pp_b_mset_structure \<sigma>"
    and x: "Elem x (pp_b_domain \<sigma>)"
  shows "pp_b_action \<sigma> [] x = x"
  using struct x unfolding pp_b_mset_structure_def
    pp_b_action_one_at_def by blast

lemma pp_b_structure_lift_one:
  assumes struct: "pp_b_mset_structure \<sigma>"
    and x: "Elem x (pp_b_domain \<sigma>)"
  shows "pp_b_lift \<sigma> [] x = x"
  using struct x unfolding pp_b_mset_structure_def
    pp_b_lift_one_at_def by blast

lemma pp_b_structure_action_default:
  assumes struct: "pp_b_mset_structure \<sigma>"
  shows "pp_b_action \<sigma> i (pp_b_default \<sigma>) = pp_b_default \<sigma>"
  using struct unfolding pp_b_mset_structure_def
    pp_b_action_default_at_def by blast

lemma pp_b_structure_lift_default:
  assumes struct: "pp_b_mset_structure \<sigma>"
  shows "pp_b_lift \<sigma> i (pp_b_default \<sigma>) = pp_b_default \<sigma>"
  using struct unfolding pp_b_mset_structure_def
    pp_b_lift_default_at_def by blast

lemma pp_b_structure_incomparable:
  assumes struct: "pp_b_mset_structure \<sigma>"
    and x: "Elem x (pp_b_domain \<sigma>)"
    and not_ji: "\<nexists>k. j = k @ i"
    and not_ij: "\<nexists>k. i = k @ j"
  shows "pp_b_action \<sigma> j (pp_b_lift \<sigma> i x) = pp_b_default \<sigma>"
  using struct x not_ji not_ij unfolding pp_b_mset_structure_def
    pp_b_incomparable_at_def by blast

lemma pp_b_structure_action_lift_longer:
  assumes struct: "pp_b_mset_structure \<sigma>"
    and x: "Elem x (pp_b_domain \<sigma>)"
  shows "pp_b_action \<sigma> (k @ i) (pp_b_lift \<sigma> i x) =
    pp_b_action \<sigma> k x"
proof -
  have lifted: "Elem (pp_b_lift \<sigma> i x) (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_lift_closed[OF struct x])
  have "pp_b_action \<sigma> (k @ i) (pp_b_lift \<sigma> i x) =
      pp_b_action \<sigma> k
        (pp_b_action \<sigma> i (pp_b_lift \<sigma> i x))"
    using pp_b_structure_action_comp[OF struct lifted, of k i]
    by simp
  also have "... = pp_b_action \<sigma> k x"
    using pp_b_structure_action_lift[OF struct x, of i] by simp
  finally show ?thesis .
qed

lemma pp_b_structure_action_lift_shorter:
  assumes struct: "pp_b_mset_structure \<sigma>"
    and x: "Elem x (pp_b_domain \<sigma>)"
  shows "pp_b_action \<sigma> j (pp_b_lift \<sigma> (k @ j) x) =
    pp_b_lift \<sigma> k x"
proof -
  have lift_k: "Elem (pp_b_lift \<sigma> k x) (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_lift_closed[OF struct x])
  have lift_comp:
      "pp_b_lift \<sigma> j (pp_b_lift \<sigma> k x) =
       pp_b_lift \<sigma> (k @ j) x"
    by (rule pp_b_structure_lift_comp[OF struct x])
  have "pp_b_action \<sigma> j (pp_b_lift \<sigma> (k @ j) x) =
      pp_b_action \<sigma> j (pp_b_lift \<sigma> j (pp_b_lift \<sigma> k x))"
    using lift_comp by simp
  also have "... = pp_b_lift \<sigma> k x"
    by (rule pp_b_structure_action_lift[OF struct lift_k])
  finally show ?thesis .
qed

lemma pp_b_mset_structure_Ind:
  "pp_b_mset_structure Ind"
  unfolding pp_b_mset_structure_def pp_b_action_closed_at_def
    pp_b_lift_closed_at_def pp_b_action_one_at_def
    pp_b_action_comp_at_def pp_b_action_lift_at_def
    pp_b_lift_one_at_def pp_b_lift_comp_at_def
    pp_b_action_default_at_def pp_b_lift_default_at_def
    pp_b_incomparable_at_def
  by (simp add: Singleton)

lemma pp_b_mset_structure_Prop:
  "pp_b_mset_structure Prop"
  unfolding pp_b_mset_structure_def pp_b_action_closed_at_def
    pp_b_lift_closed_at_def pp_b_action_one_at_def
    pp_b_action_comp_at_def pp_b_action_lift_at_def
    pp_b_lift_one_at_def pp_b_lift_comp_at_def
    pp_b_action_default_at_def pp_b_lift_default_at_def
    pp_b_incomparable_at_def
  apply (intro conjI allI impI)
  subgoal using pp_n_prop_action_in_domain by simp
  subgoal using pp_n_prop_lift_in_domain by simp
  subgoal using pp_n_prop_action_one
    by (simp add: pp_subst_one_def)
  subgoal using pp_n_prop_action_comp
    by (simp add: pp_subst_comp_def)
  subgoal using pp_n_prop_action_lift by simp
  subgoal using pp_n_prop_lift_one by simp
  subgoal using pp_n_prop_lift_comp by simp
  subgoal using pp_n_prop_action_empty by simp
  subgoal using pp_n_prop_lift_empty by simp
  subgoal using pp_n_prop_action_lift_incomparable by simp
  done

lemma pp_b_arrow_action_closed:
  assumes sigma: "pp_b_mset_structure \<sigma>"
    and tau: "pp_b_mset_structure \<tau>"
    and f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f)
    (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
proof -
  let ?F = "\<lambda>x. pp_b_action \<tau> i (f \<acute> pp_b_lift \<sigma> i x)"
  have maps: "\<And>x. Elem x (pp_b_domain \<sigma>) \<Longrightarrow>
      Elem (?F x) (pp_b_domain \<tau>)"
  proof -
    fix x
    assume x: "Elem x (pp_b_domain \<sigma>)"
    have lift_x: "Elem (pp_b_lift \<sigma> i x) (pp_b_domain \<sigma>)"
      by (rule pp_b_structure_lift_closed[OF sigma x])
    have value_x: "Elem (f \<acute> pp_b_lift \<sigma> i x) (pp_b_domain \<tau>)"
      by (rule pp_b_app_closed[OF f lift_x])
    show "Elem (?F x) (pp_b_domain \<tau>)"
      by (rule pp_b_structure_action_closed[OF tau value_x])
  qed
  have function_member:
      "Elem (Lambda (pp_b_domain \<sigma>) ?F)
        (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    using maps by (simp add: Elem_Lambda_Fun)
  have respects:
      "\<forall>j x y.
        Elem x (pp_b_domain \<sigma>) \<longrightarrow>
        Elem y (pp_b_domain \<sigma>) \<longrightarrow>
        pp_b_action \<sigma> j x = pp_b_action \<sigma> j y \<longrightarrow>
        pp_b_action \<tau> j ((Lambda (pp_b_domain \<sigma>) ?F) \<acute> x) =
        pp_b_action \<tau> j ((Lambda (pp_b_domain \<sigma>) ?F) \<acute> y)"
  proof (intro allI impI)
    fix j x y
    assume x: "Elem x (pp_b_domain \<sigma>)"
      and y: "Elem y (pp_b_domain \<sigma>)"
      and same: "pp_b_action \<sigma> j x = pp_b_action \<sigma> j y"
    have lift_x: "Elem (pp_b_lift \<sigma> i x) (pp_b_domain \<sigma>)"
      by (rule pp_b_structure_lift_closed[OF sigma x])
    have lift_y: "Elem (pp_b_lift \<sigma> i y) (pp_b_domain \<sigma>)"
      by (rule pp_b_structure_lift_closed[OF sigma y])
    have shifted:
        "pp_b_action \<sigma> (j @ i) (pp_b_lift \<sigma> i x) =
         pp_b_action \<sigma> (j @ i) (pp_b_lift \<sigma> i y)"
      using pp_b_structure_action_lift_longer[OF sigma x, of j i]
        pp_b_structure_action_lift_longer[OF sigma y, of j i]
        same by simp
    have f_shifted:
        "pp_b_action \<tau> (j @ i) (f \<acute> pp_b_lift \<sigma> i x) =
         pp_b_action \<tau> (j @ i) (f \<acute> pp_b_lift \<sigma> i y)"
      by (rule pp_b_arrow_member_respects[OF f lift_x lift_y shifted])
    have value_x: "Elem (f \<acute> pp_b_lift \<sigma> i x) (pp_b_domain \<tau>)"
      by (rule pp_b_app_closed[OF f lift_x])
    have value_y: "Elem (f \<acute> pp_b_lift \<sigma> i y) (pp_b_domain \<tau>)"
      by (rule pp_b_app_closed[OF f lift_y])
    have left:
        "pp_b_action \<tau> j
          (pp_b_action \<tau> i (f \<acute> pp_b_lift \<sigma> i x)) =
         pp_b_action \<tau> (j @ i) (f \<acute> pp_b_lift \<sigma> i x)"
      by (rule pp_b_structure_action_comp[OF tau value_x])
    have right:
        "pp_b_action \<tau> j
          (pp_b_action \<tau> i (f \<acute> pp_b_lift \<sigma> i y)) =
         pp_b_action \<tau> (j @ i) (f \<acute> pp_b_lift \<sigma> i y)"
      by (rule pp_b_structure_action_comp[OF tau value_y])
    show "pp_b_action \<tau> j ((Lambda (pp_b_domain \<sigma>) ?F) \<acute> x) =
        pp_b_action \<tau> j ((Lambda (pp_b_domain \<sigma>) ?F) \<acute> y)"
      using left f_shifted right x y by (simp add: Lambda_app)
  qed
  show ?thesis
    unfolding pp_b_action.simps
    by (rule iffD2[OF pp_b_arrow_domain_iff])
      (rule conjI[OF function_member respects])
qed

lemma pp_b_arrow_lift_closed:
  assumes sigma: "pp_b_mset_structure \<sigma>"
    and tau: "pp_b_mset_structure \<tau>"
    and f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "Elem (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f)
    (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
proof -
  let ?G = "\<lambda>x. pp_b_lift \<tau> i (f \<acute> pp_b_action \<sigma> i x)"
  have maps: "\<And>x. Elem x (pp_b_domain \<sigma>) \<Longrightarrow>
      Elem (?G x) (pp_b_domain \<tau>)"
  proof -
    fix x
    assume x: "Elem x (pp_b_domain \<sigma>)"
    have action_x: "Elem (pp_b_action \<sigma> i x) (pp_b_domain \<sigma>)"
      by (rule pp_b_structure_action_closed[OF sigma x])
    have value_x: "Elem (f \<acute> pp_b_action \<sigma> i x) (pp_b_domain \<tau>)"
      by (rule pp_b_app_closed[OF f action_x])
    show "Elem (?G x) (pp_b_domain \<tau>)"
      by (rule pp_b_structure_lift_closed[OF tau value_x])
  qed
  have function_member:
      "Elem (Lambda (pp_b_domain \<sigma>) ?G)
        (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    using maps by (simp add: Elem_Lambda_Fun)
  have respects:
      "\<forall>j x y.
        Elem x (pp_b_domain \<sigma>) \<longrightarrow>
        Elem y (pp_b_domain \<sigma>) \<longrightarrow>
        pp_b_action \<sigma> j x = pp_b_action \<sigma> j y \<longrightarrow>
        pp_b_action \<tau> j ((Lambda (pp_b_domain \<sigma>) ?G) \<acute> x) =
        pp_b_action \<tau> j ((Lambda (pp_b_domain \<sigma>) ?G) \<acute> y)"
  proof (intro allI impI)
    fix j x y
    assume x: "Elem x (pp_b_domain \<sigma>)"
      and y: "Elem y (pp_b_domain \<sigma>)"
      and same: "pp_b_action \<sigma> j x = pp_b_action \<sigma> j y"
    have action_x: "Elem (pp_b_action \<sigma> i x) (pp_b_domain \<sigma>)"
      by (rule pp_b_structure_action_closed[OF sigma x])
    have action_y: "Elem (pp_b_action \<sigma> i y) (pp_b_domain \<sigma>)"
      by (rule pp_b_structure_action_closed[OF sigma y])
    have value_x: "Elem (f \<acute> pp_b_action \<sigma> i x) (pp_b_domain \<tau>)"
      by (rule pp_b_app_closed[OF f action_x])
    have value_y: "Elem (f \<acute> pp_b_action \<sigma> i y) (pp_b_domain \<tau>)"
      by (rule pp_b_app_closed[OF f action_y])
    show "pp_b_action \<tau> j ((Lambda (pp_b_domain \<sigma>) ?G) \<acute> x) =
        pp_b_action \<tau> j ((Lambda (pp_b_domain \<sigma>) ?G) \<acute> y)"
    proof (cases "\<exists>k. j = k @ i")
      case True
      then obtain k where j: "j = k @ i" by blast
      have inputs:
          "pp_b_action \<sigma> k (pp_b_action \<sigma> i x) =
           pp_b_action \<sigma> k (pp_b_action \<sigma> i y)"
      proof -
        have left: "pp_b_action \<sigma> k (pp_b_action \<sigma> i x) =
            pp_b_action \<sigma> j x"
          using pp_b_structure_action_comp[OF sigma x, of k i] j by simp
        have right: "pp_b_action \<sigma> k (pp_b_action \<sigma> i y) =
            pp_b_action \<sigma> j y"
          using pp_b_structure_action_comp[OF sigma y, of k i] j by simp
        show ?thesis using left same right by simp
      qed
      have f_inputs:
          "pp_b_action \<tau> k (f \<acute> pp_b_action \<sigma> i x) =
           pp_b_action \<tau> k (f \<acute> pp_b_action \<sigma> i y)"
        by (rule pp_b_arrow_member_respects[OF f action_x action_y inputs])
      have left:
          "pp_b_action \<tau> j
            (pp_b_lift \<tau> i (f \<acute> pp_b_action \<sigma> i x)) =
           pp_b_action \<tau> k (f \<acute> pp_b_action \<sigma> i x)"
        using pp_b_structure_action_lift_longer[OF tau value_x, of k i]
          j by simp
      have right:
          "pp_b_action \<tau> j
            (pp_b_lift \<tau> i (f \<acute> pp_b_action \<sigma> i y)) =
           pp_b_action \<tau> k (f \<acute> pp_b_action \<sigma> i y)"
        using pp_b_structure_action_lift_longer[OF tau value_y, of k i]
          j by simp
      show ?thesis
        using left f_inputs right x y by (simp add: Lambda_app)
    next
      case not_ji: False
      show ?thesis
      proof (cases "\<exists>k. i = k @ j")
        case True
        then obtain k where i: "i = k @ j" by blast
        have inputs: "pp_b_action \<sigma> i x = pp_b_action \<sigma> i y"
        proof -
          have left: "pp_b_action \<sigma> i x =
              pp_b_action \<sigma> k (pp_b_action \<sigma> j x)"
            using pp_b_structure_action_comp[OF sigma x, of k j] i by simp
          have right: "pp_b_action \<sigma> i y =
              pp_b_action \<sigma> k (pp_b_action \<sigma> j y)"
            using pp_b_structure_action_comp[OF sigma y, of k j] i by simp
          show ?thesis using left same right by simp
        qed
        have same_values:
            "f \<acute> pp_b_action \<sigma> i x =
             f \<acute> pp_b_action \<sigma> i y"
          using inputs by simp
        show ?thesis using same_values x y by (simp add: Lambda_app)
      next
        case not_ij: False
        have left:
            "pp_b_action \<tau> j
              (pp_b_lift \<tau> i (f \<acute> pp_b_action \<sigma> i x)) =
             pp_b_default \<tau>"
          by (rule pp_b_structure_incomparable[OF tau value_x not_ji not_ij])
        have right:
            "pp_b_action \<tau> j
              (pp_b_lift \<tau> i (f \<acute> pp_b_action \<sigma> i y)) =
             pp_b_default \<tau>"
          by (rule pp_b_structure_incomparable[OF tau value_y not_ji not_ij])
        show ?thesis using left right x y by (simp add: Lambda_app)
      qed
    qed
  qed
  show ?thesis
    using function_member respects
    unfolding pp_b_lift.simps
    by (simp only: pp_b_arrow_domain_iff)
qed

lemma pp_b_arrow_action_one:
  assumes sigma: "pp_b_mset_structure \<sigma>"
    and tau: "pp_b_mset_structure \<tau>"
    and f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) [] f = f"
proof (rule pp_b_function_ext)
  show "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) [] f)
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function)
      (rule pp_b_arrow_action_closed[OF sigma tau f])
  show "Elem f (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF f])
  fix x
  assume x: "Elem x (pp_b_domain \<sigma>)"
  have fx: "Elem (f \<acute> x) (pp_b_domain \<tau>)"
    by (rule pp_b_app_closed[OF f x])
  show "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) [] f \<acute> x = f \<acute> x"
    using pp_b_arrow_action_apply[OF x, of \<tau> "[]" f]
      pp_b_structure_lift_one[OF sigma x]
      pp_b_structure_action_one[OF tau fx]
    by simp
qed

lemma pp_b_arrow_lift_one:
  assumes sigma: "pp_b_mset_structure \<sigma>"
    and tau: "pp_b_mset_structure \<tau>"
    and f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) [] f = f"
proof (rule pp_b_function_ext)
  show "Elem (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) [] f)
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function)
      (rule pp_b_arrow_lift_closed[OF sigma tau f])
  show "Elem f (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF f])
  fix x
  assume x: "Elem x (pp_b_domain \<sigma>)"
  have fx: "Elem (f \<acute> x) (pp_b_domain \<tau>)"
    by (rule pp_b_app_closed[OF f x])
  show "pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) [] f \<acute> x = f \<acute> x"
    using pp_b_arrow_lift_apply[OF x, of \<tau> "[]" f]
      pp_b_structure_action_one[OF sigma x]
      pp_b_structure_lift_one[OF tau fx]
    by simp
qed

lemma pp_b_arrow_action_comp:
  assumes sigma: "pp_b_mset_structure \<sigma>"
    and tau: "pp_b_mset_structure \<tau>"
    and f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
      (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j f) =
    pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (i @ j) f"
proof -
  have action_j:
      "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j f)
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_arrow_action_closed[OF sigma tau f])
  have action_i_j:
      "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
        (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j f))
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_arrow_action_closed[OF sigma tau action_j])
  have lhs_fun: "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
      (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j f))
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF action_i_j])
  have action_append:
      "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (i @ j) f)
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_arrow_action_closed[OF sigma tau f])
  have rhs_fun: "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (i @ j) f)
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF action_append])
  have pointwise: "\<And>x. Elem x (pp_b_domain \<sigma>) \<Longrightarrow>
      pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
        (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j f) \<acute> x =
      pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (i @ j) f \<acute> x"
  proof -
    fix x
    assume x: "Elem x (pp_b_domain \<sigma>)"
  have lift_i: "Elem (pp_b_lift \<sigma> i x) (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_lift_closed[OF sigma x])
  have lift_i_j:
      "pp_b_lift \<sigma> j (pp_b_lift \<sigma> i x) =
       pp_b_lift \<sigma> (i @ j) x"
    by (rule pp_b_structure_lift_comp[OF sigma x])
  have lift_append:
      "Elem (pp_b_lift \<sigma> (i @ j) x) (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_lift_closed[OF sigma x])
  have f_value:
      "Elem (f \<acute> pp_b_lift \<sigma> (i @ j) x) (pp_b_domain \<tau>)"
    by (rule pp_b_app_closed[OF f lift_append])
  have target_comp:
      "pp_b_action \<tau> i
        (pp_b_action \<tau> j
          (f \<acute> pp_b_lift \<sigma> (i @ j) x)) =
       pp_b_action \<tau> (i @ j)
          (f \<acute> pp_b_lift \<sigma> (i @ j) x)"
    by (rule pp_b_structure_action_comp[OF tau f_value])
  have "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
        (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j f) \<acute> x =
      pp_b_action \<tau> i
        (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j f
          \<acute> pp_b_lift \<sigma> i x)"
    by (rule pp_b_arrow_action_apply[OF x])
  also have "... = pp_b_action \<tau> i
        (pp_b_action \<tau> j
          (f \<acute> pp_b_lift \<sigma> j (pp_b_lift \<sigma> i x)))"
    by (simp only: pp_b_arrow_action_apply[OF lift_i])
  also have "... = pp_b_action \<tau> i
        (pp_b_action \<tau> j
          (f \<acute> pp_b_lift \<sigma> (i @ j) x))"
    by (simp only: lift_i_j)
  also have "... = pp_b_action \<tau> (i @ j)
      (f \<acute> pp_b_lift \<sigma> (i @ j) x)"
    by (rule target_comp)
  also have "... =
      pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (i @ j) f \<acute> x"
    by (rule sym, rule pp_b_arrow_action_apply[OF x])
    finally show
        "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
          (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j f) \<acute> x =
         pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) (i @ j) f \<acute> x" .
  qed
  show ?thesis
    by (rule pp_b_function_ext[OF lhs_fun rhs_fun pointwise])
qed

lemma pp_b_arrow_lift_comp:
  assumes sigma: "pp_b_mset_structure \<sigma>"
    and tau: "pp_b_mset_structure \<tau>"
    and f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
      (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f) =
    pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) (i @ j) f"
proof -
  have lift_i:
      "Elem (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f)
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_arrow_lift_closed[OF sigma tau f])
  have lift_j_i:
      "Elem (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
        (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f))
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_arrow_lift_closed[OF sigma tau lift_i])
  have lhs_fun: "Elem (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
      (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f))
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF lift_j_i])
  have lift_append:
      "Elem (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) (i @ j) f)
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_arrow_lift_closed[OF sigma tau f])
  have rhs_fun: "Elem (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) (i @ j) f)
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF lift_append])
  have pointwise: "\<And>x. Elem x (pp_b_domain \<sigma>) \<Longrightarrow>
      pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
        (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f) \<acute> x =
      pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) (i @ j) f \<acute> x"
  proof -
    fix x
    assume x: "Elem x (pp_b_domain \<sigma>)"
  have action_j: "Elem (pp_b_action \<sigma> j x) (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_action_closed[OF sigma x])
  have action_i_j:
      "pp_b_action \<sigma> i (pp_b_action \<sigma> j x) =
       pp_b_action \<sigma> (i @ j) x"
    by (rule pp_b_structure_action_comp[OF sigma x])
  have action_append:
      "Elem (pp_b_action \<sigma> (i @ j) x) (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_action_closed[OF sigma x])
  have f_value:
      "Elem (f \<acute> pp_b_action \<sigma> (i @ j) x) (pp_b_domain \<tau>)"
    by (rule pp_b_app_closed[OF f action_append])
  have target_comp:
      "pp_b_lift \<tau> j
        (pp_b_lift \<tau> i
          (f \<acute> pp_b_action \<sigma> (i @ j) x)) =
       pp_b_lift \<tau> (i @ j)
          (f \<acute> pp_b_action \<sigma> (i @ j) x)"
    by (rule pp_b_structure_lift_comp[OF tau f_value])
  have "pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
        (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f) \<acute> x =
      pp_b_lift \<tau> j
        (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f
          \<acute> pp_b_action \<sigma> j x)"
    by (rule pp_b_arrow_lift_apply[OF x])
  also have "... = pp_b_lift \<tau> j
        (pp_b_lift \<tau> i
          (f \<acute> pp_b_action \<sigma> i (pp_b_action \<sigma> j x)))"
    by (simp only: pp_b_arrow_lift_apply[OF action_j])
  also have "... = pp_b_lift \<tau> j
        (pp_b_lift \<tau> i
          (f \<acute> pp_b_action \<sigma> (i @ j) x))"
    by (simp only: action_i_j)
  also have "... = pp_b_lift \<tau> (i @ j)
      (f \<acute> pp_b_action \<sigma> (i @ j) x)"
    by (rule target_comp)
  also have "... =
      pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) (i @ j) f \<acute> x"
    by (rule sym, rule pp_b_arrow_lift_apply[OF x])
    finally show
        "pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
          (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f) \<acute> x =
         pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) (i @ j) f \<acute> x" .
  qed
  show ?thesis
    by (rule pp_b_function_ext[OF lhs_fun rhs_fun pointwise])
qed

lemma pp_b_arrow_action_lift:
  assumes sigma: "pp_b_mset_structure \<sigma>"
    and tau: "pp_b_mset_structure \<tau>"
    and f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
      (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f) = f"
proof (rule pp_b_function_ext)
  have lifted:
      "Elem (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f)
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_arrow_lift_closed[OF sigma tau f])
  have recovered:
      "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
        (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f))
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_arrow_action_closed[OF sigma tau lifted])
  show "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
      (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f))
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF recovered])
  show "Elem f (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF f])
  fix x
  assume x: "Elem x (pp_b_domain \<sigma>)"
  have lift_x: "Elem (pp_b_lift \<sigma> i x) (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_lift_closed[OF sigma x])
  have lower_recovery: "pp_b_action \<sigma> i (pp_b_lift \<sigma> i x) = x"
    by (rule pp_b_structure_action_lift[OF sigma x])
  have fx: "Elem (f \<acute> x) (pp_b_domain \<tau>)"
    by (rule pp_b_app_closed[OF f x])
  have target_recovery: "pp_b_action \<tau> i (pp_b_lift \<tau> i (f \<acute> x)) = f \<acute> x"
    by (rule pp_b_structure_action_lift[OF tau fx])
  show "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
      (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f) \<acute> x = f \<acute> x"
    using pp_b_arrow_action_apply[OF x, of \<tau> i
        "pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f"]
      pp_b_arrow_lift_apply[OF lift_x, of \<tau> i f]
      lower_recovery target_recovery
    by simp
qed

lemma pp_b_arrow_action_default:
  assumes sigma: "pp_b_mset_structure \<sigma>"
    and tau: "pp_b_mset_structure \<tau>"
  shows "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
      (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)) =
    pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
proof (rule pp_b_function_ext)
  have default_member:
      "Elem (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_default_in_domain)
  have action_member:
      "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
        (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)))
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_arrow_action_closed[OF sigma tau default_member])
  show "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
      (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)))
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF action_member])
  show "Elem (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF default_member])
  fix x
  assume x: "Elem x (pp_b_domain \<sigma>)"
  have lift_x: "Elem (pp_b_lift \<sigma> i x) (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_lift_closed[OF sigma x])
  have target_default:
      "pp_b_action \<tau> i (pp_b_default \<tau>) = pp_b_default \<tau>"
    by (rule pp_b_structure_action_default[OF tau])
  show "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
      (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<acute> x =
    pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<acute> x"
    using pp_b_arrow_action_apply[OF x, of \<tau> i
        "pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)"]
      target_default x lift_x
    by (simp add: Lambda_app)
qed

lemma pp_b_arrow_lift_default:
  assumes sigma: "pp_b_mset_structure \<sigma>"
    and tau: "pp_b_mset_structure \<tau>"
  shows "pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
      (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)) =
    pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
proof (rule pp_b_function_ext)
  have default_member:
      "Elem (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_default_in_domain)
  have lift_member:
      "Elem (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
        (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)))
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_arrow_lift_closed[OF sigma tau default_member])
  show "Elem (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
      (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)))
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF lift_member])
  show "Elem (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF default_member])
  fix x
  assume x: "Elem x (pp_b_domain \<sigma>)"
  have action_x: "Elem (pp_b_action \<sigma> i x) (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_action_closed[OF sigma x])
  have target_default:
      "pp_b_lift \<tau> i (pp_b_default \<tau>) = pp_b_default \<tau>"
    by (rule pp_b_structure_lift_default[OF tau])
  show "pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i
      (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<acute> x =
    pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<acute> x"
    using pp_b_arrow_lift_apply[OF x, of \<tau> i
        "pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)"]
      target_default x action_x
    by (simp add: Lambda_app)
qed

lemma pp_b_arrow_incomparable:
  assumes sigma: "pp_b_mset_structure \<sigma>"
    and tau: "pp_b_mset_structure \<tau>"
    and f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and not_ji: "\<nexists>k. j = k @ i"
    and not_ij: "\<nexists>k. i = k @ j"
  shows "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
      (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f) =
    pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
proof (rule pp_b_function_ext)
  have lifted:
      "Elem (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f)
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_arrow_lift_closed[OF sigma tau f])
  have lhs_member:
      "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
        (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f))
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_arrow_action_closed[OF sigma tau lifted])
  show "Elem (pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
      (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f))
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF lhs_member])
  have default_member:
      "Elem (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
        (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    by (rule pp_b_default_in_domain)
  show "Elem (pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>))
      (Fun (pp_b_domain \<sigma>) (pp_b_domain \<tau>))"
    by (rule pp_b_arrow_member_function[OF default_member])
  fix x
  assume x: "Elem x (pp_b_domain \<sigma>)"
  have lift_j: "Elem (pp_b_lift \<sigma> j x) (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_lift_closed[OF sigma x])
  have action_i_lift_j:
      "Elem (pp_b_action \<sigma> i (pp_b_lift \<sigma> j x))
        (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_action_closed[OF sigma lift_j])
  have f_value:
      "Elem (f \<acute> pp_b_action \<sigma> i (pp_b_lift \<sigma> j x))
        (pp_b_domain \<tau>)"
    by (rule pp_b_app_closed[OF f action_i_lift_j])
  have collapse:
      "pp_b_action \<tau> j
        (pp_b_lift \<tau> i
          (f \<acute> pp_b_action \<sigma> i (pp_b_lift \<sigma> j x))) =
       pp_b_default \<tau>"
    by (rule pp_b_structure_incomparable[OF tau f_value not_ji not_ij])
  show "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) j
      (pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f) \<acute> x =
    pp_b_default (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<acute> x"
    using pp_b_arrow_action_apply[OF x, of \<tau> j
        "pp_b_lift (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f"]
      pp_b_arrow_lift_apply[OF lift_j, of \<tau> i f]
      collapse x
    by (simp add: Lambda_app)
qed

lemma pp_b_mset_structure_Arr:
  assumes sigma: "pp_b_mset_structure \<sigma>"
    and tau: "pp_b_mset_structure \<tau>"
  shows "pp_b_mset_structure (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
  unfolding pp_b_mset_structure_def pp_b_action_closed_at_def
    pp_b_lift_closed_at_def pp_b_action_one_at_def
    pp_b_action_comp_at_def pp_b_action_lift_at_def
    pp_b_lift_one_at_def pp_b_lift_comp_at_def
    pp_b_action_default_at_def pp_b_lift_default_at_def
    pp_b_incomparable_at_def
  apply (intro conjI allI impI)
  subgoal using pp_b_arrow_action_closed[OF sigma tau] by blast
  subgoal using pp_b_arrow_lift_closed[OF sigma tau] by blast
  subgoal using pp_b_arrow_action_one[OF sigma tau] by blast
  subgoal using pp_b_arrow_action_comp[OF sigma tau] by blast
  subgoal using pp_b_arrow_action_lift[OF sigma tau] by blast
  subgoal using pp_b_arrow_lift_one[OF sigma tau] by blast
  subgoal using pp_b_arrow_lift_comp[OF sigma tau] by blast
  subgoal using pp_b_arrow_action_default[OF sigma tau] by blast
  subgoal using pp_b_arrow_lift_default[OF sigma tau] by blast
  subgoal using pp_b_arrow_incomparable[OF sigma tau] by blast
  done

theorem pp_b_mset_structure_all:
  "pp_b_mset_structure \<sigma>"
proof (induction \<sigma>)
  case Ind
  show ?case by (rule pp_b_mset_structure_Ind)
next
  case Prop
  show ?case by (rule pp_b_mset_structure_Prop)
next
  case (Arr \<sigma> \<tau>)
  show ?case by (rule pp_b_mset_structure_Arr[OF Arr.IH(1) Arr.IH(2)])
qed

subsection \<open>Explicit base cases\<close>

lemma pp_b_individual_member_iff:
  "Elem x (pp_b_domain Ind) \<longleftrightarrow> x = Empty"
  by (simp add: Singleton)

lemma pp_b_individual_action_closed:
  assumes "Elem x (pp_b_domain Ind)"
  shows "Elem (pp_b_action Ind i x) (pp_b_domain Ind)"
  using assms by simp

lemma pp_b_individual_action_lift:
  assumes "Elem x (pp_b_domain Ind)"
  shows "pp_b_action Ind i (pp_b_lift Ind i x) = x"
  using assms by simp

lemma pp_b_proposition_action_closed:
  assumes "Elem P (pp_b_domain Prop)"
  shows "Elem (pp_b_action Prop i P) (pp_b_domain Prop)"
  using pp_n_prop_action_in_domain by simp

lemma pp_b_proposition_lift_closed:
  assumes "Elem P (pp_b_domain Prop)"
  shows "Elem (pp_b_lift Prop i P) (pp_b_domain Prop)"
  using pp_n_prop_lift_in_domain by simp

lemma pp_b_proposition_action_lift:
  assumes "Elem P (pp_b_domain Prop)"
  shows "pp_b_action Prop i (pp_b_lift Prop i P) = P"
  using pp_n_prop_action_lift[of P i] assms by simp

subsection \<open>Bacon's Definition 7.1 and Proposition 8\<close>

definition pp_b_surjective_mset_at :: "otype \<Rightarrow> bool" where
  "pp_b_surjective_mset_at \<sigma> \<longleftrightarrow>
    (\<forall>i x. Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      Elem (pp_b_action \<sigma> i x) (pp_b_domain \<sigma>)) \<and>
    (\<forall>x. Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      pp_b_action \<sigma> [] x = x) \<and>
    (\<forall>i j x. Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      pp_b_action \<sigma> i (pp_b_action \<sigma> j x) =
        pp_b_action \<sigma> (i @ j) x) \<and>
    (\<forall>i x. Elem x (pp_b_domain \<sigma>) \<longrightarrow>
      (\<exists>y. Elem y (pp_b_domain \<sigma>) \<and>
        pp_b_action \<sigma> i y = x))"

lemma pp_b_action_closed_all:
  assumes x: "Elem x (pp_b_domain \<sigma>)"
  shows "Elem (pp_b_action \<sigma> i x) (pp_b_domain \<sigma>)"
  by (rule pp_b_structure_action_closed[OF pp_b_mset_structure_all x])

lemma pp_b_action_one_all:
  assumes x: "Elem x (pp_b_domain \<sigma>)"
  shows "pp_b_action \<sigma> [] x = x"
  by (rule pp_b_structure_action_one[OF pp_b_mset_structure_all x])

lemma pp_b_action_comp_all:
  assumes x: "Elem x (pp_b_domain \<sigma>)"
  shows "pp_b_action \<sigma> i (pp_b_action \<sigma> j x) =
    pp_b_action \<sigma> (i @ j) x"
  by (rule pp_b_structure_action_comp[OF pp_b_mset_structure_all x])

lemma pp_b_action_surjective_all:
  assumes x: "Elem x (pp_b_domain \<sigma>)"
  shows "\<exists>y. Elem y (pp_b_domain \<sigma>) \<and>
    pp_b_action \<sigma> i y = x"
proof -
  have lift_member:
      "Elem (pp_b_lift \<sigma> i x) (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_lift_closed[OF pp_b_mset_structure_all x])
  have recovery: "pp_b_action \<sigma> i (pp_b_lift \<sigma> i x) = x"
    by (rule pp_b_structure_action_lift[OF pp_b_mset_structure_all x])
  show ?thesis using lift_member recovery by blast
qed

theorem bacon_surjective_mset_at_every_type_exact_hol_zf:
  "pp_b_surjective_mset_at \<sigma>"
  unfolding pp_b_surjective_mset_at_def
  using pp_b_action_closed_all pp_b_action_one_all
    pp_b_action_comp_all pp_b_action_surjective_all
  by blast

theorem bacon_proposition_8_exact_hol_zf:
  assumes f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
  shows "\<exists>g. Elem g (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>)) \<and>
    pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i g = f"
  by (rule pp_b_action_surjective_all[OF f])

theorem pp_b_arrow_action_preimage_independent:
  assumes f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and a: "Elem a (pp_b_domain \<sigma>)"
    and b: "Elem b (pp_b_domain \<sigma>)"
    and preimage: "pp_b_action \<sigma> i b = a"
  shows "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f \<acute> a =
    pp_b_action \<tau> i (f \<acute> b)"
proof -
  have lift_a: "Elem (pp_b_lift \<sigma> i a) (pp_b_domain \<sigma>)"
    by (rule pp_b_structure_lift_closed[OF pp_b_mset_structure_all a])
  have canonical_preimage:
      "pp_b_action \<sigma> i (pp_b_lift \<sigma> i a) = a"
    by (rule pp_b_structure_action_lift[OF pp_b_mset_structure_all a])
  have same_image:
      "pp_b_action \<sigma> i (pp_b_lift \<sigma> i a) =
       pp_b_action \<sigma> i b"
    using canonical_preimage preimage by simp
  have respects:
      "pp_b_action \<tau> i (f \<acute> pp_b_lift \<sigma> i a) =
       pp_b_action \<tau> i (f \<acute> b)"
    by (rule pp_b_arrow_member_respects[OF f lift_a b same_image])
  show ?thesis
    using pp_b_arrow_action_apply[OF a, of \<tau> i f] respects by simp
qed

theorem pp_b_application_substitution_exact:
  assumes f: "Elem f (pp_b_domain (\<sigma> \<rightarrow>\<^sub>o \<tau>))"
    and a: "Elem a (pp_b_domain \<sigma>)"
  shows "pp_b_action (\<sigma> \<rightarrow>\<^sub>o \<tau>) i f \<acute>
      pp_b_action \<sigma> i a =
    pp_b_action \<tau> i (f \<acute> a)"
proof -
  have action_a:
      "Elem (pp_b_action \<sigma> i a) (pp_b_domain \<sigma>)"
    by (rule pp_b_action_closed_all[OF a])
  show ?thesis
    by (rule pp_b_arrow_action_preimage_independent[OF f action_a a]) simp
qed

text \<open>
  The witness in Proposition 8 is the recursively defined canonical lift.
  At an arrow type it sends an argument \<open>a\<close> to a chosen preimage in
  the codomain of \<open>f (i a)\<close>, exactly as in Bacon's footnote 73.
  The theorem \<open>pp_b_arrow_action_preimage_independent\<close> additionally
  verifies Bacon's claim that the action in Definition 7.2 is independent of
  which preimage is used.
\<close>

end
