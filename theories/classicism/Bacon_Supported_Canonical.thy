theory Bacon_Supported_Canonical
  imports
    Bacon_Intended_Quotient
    "HOL-Library.Countable_Set"
begin

section \<open>The global-name defect in the unrestricted identity diagram\<close>

text \<open>
  This theory repairs a language-reserve defect in the preceding quotient
  construction.  The unrestricted diagram mentions every constant name,
  including through reflexive identities, so it cannot leave a fresh name
  for Henkin extension.  We instead preserve only identities between terms
  supported by a specified set of names.

  In \<open>CEV_supported_world K C \<Gamma> T\<close>, \<open>K\<close> is a designated initial
  vocabulary, \<open>C\<close> is the current vocabulary, and infinitely many names
  remain outside \<open>C\<close>.  The restriction applies to representatives in
  the local domains and diagrams; \<open>T\<close> is still an ambient global-language
  theory.  A successor adds an infinite witness block \<open>D\<close> to \<open>C\<close>
  while retaining a further infinite reserve.  The counterworld theorem
  chooses a finite nonempty \<open>K\<close> containing the formula's constants.

  Compare Bacon, Definition 18.8 and Proposition 18.3 (p. 399), and
  Bacon--Dorr's diagram argument in footnote 73 (pp. 51--52).  Our supported
  arrows preserve identities; identifying them with a canonical modal
  accessibility relation and constructing the source's profile semantics
  remain separate obligations.
\<close>

lemma CEV_identity_diagram_consts_UNIV:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> S"
  shows "consts_of_set (CEV_identity_diagram \<Gamma> S) = UNIV"
proof
  show "consts_of_set (CEV_identity_diagram \<Gamma> S) \<subseteq> UNIV"
    by simp
  show "UNIV \<subseteq> consts_of_set (CEV_identity_diagram \<Gamma> S)"
  proof
    fix c
    have c_type: "\<Gamma> \<turnstile> Const c Prop : Prop"
      by auto
    have refl: "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop (Const c Prop) (Const c Prop)"
      using c_type
      by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.Ref)
    have refl_in: "Eq Prop (Const c Prop) (Const c Prop) \<in> S"
      using henkin refl by (rule CEV_clean_Henkin_contains_theorems)
    have diagram_in:
        "Eq Prop (Const c Prop) (Const c Prop)
          \<in> CEV_identity_diagram \<Gamma> S"
      unfolding CEV_identity_diagram_iff
      using c_type refl_in by blast
    show "c \<in> consts_of_set (CEV_identity_diagram \<Gamma> S)"
    proof (rule consts_of_setI[OF diagram_in])
      show "c \<in> consts_of
          (Eq Prop (Const c Prop) (Const c Prop))"
        by simp
    qed
  qed
qed

corollary CEV_identity_separator_not_fresh_extendible:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> S"
  shows "\<not> CEV_fresh_extendible_base
    (insert (Neg A) (CEV_identity_diagram \<Gamma> S))"
proof
  let ?B = "insert (Neg A) (CEV_identity_diagram \<Gamma> S)"
  assume reserve: "CEV_fresh_extendible_base ?B"
  have reserve_rule:
      "\<forall>T A. ?B \<subseteq> T \<longrightarrow> finite (T - ?B) \<longrightarrow>
        (\<exists>c. fresh_const_for c T A)"
    using reserve unfolding CEV_fresh_extendible_base_def .
  have fresh_ex: "\<exists>c. fresh_const_for c ?B A"
    using reserve_rule[rule_format, of ?B A] by simp
  obtain c where fresh: "fresh_const_for c ?B A"
    using fresh_ex by blast
  have all_consts: "consts_of_set (CEV_identity_diagram \<Gamma> S) = UNIV"
    using henkin by (rule CEV_identity_diagram_consts_UNIV)
  have c_diagram: "c \<in> consts_of_set (CEV_identity_diagram \<Gamma> S)"
    using all_consts by simp
  obtain E where E_diagram: "E \<in> CEV_identity_diagram \<Gamma> S"
    and c_E: "c \<in> consts_of E"
    using c_diagram by (rule consts_of_setD)
  have E_B: "E \<in> ?B"
    using E_diagram by simp
  have c_B: "c \<in> consts_of_set ?B"
    using E_B c_E by (rule consts_of_setI)
  have c_not_B: "c \<notin> consts_of_set ?B"
    using fresh unfolding fresh_const_for_def by (rule conjunct1)
  show False
    using c_not_B c_B by contradiction
qed

section \<open>Supported local languages and worlds\<close>

definition CEV_supported_term :: "string set \<Rightarrow> oterm \<Rightarrow> bool" where
  "CEV_supported_term C M \<longleftrightarrow> consts_of M \<subseteq> C"

definition CEV_supported_identity_diagram ::
    "string set \<Rightarrow> ctx \<Rightarrow> oterm set \<Rightarrow> oterm set" where
  "CEV_supported_identity_diagram C \<Gamma> S =
    {Eq \<sigma> M N | \<sigma> M N.
      \<Gamma> \<turnstile> M : \<sigma> \<and> \<Gamma> \<turnstile> N : \<sigma> \<and>
      CEV_supported_term C M \<and> CEV_supported_term C N \<and>
      Eq \<sigma> M N \<in> S}"

definition CEV_Henkin_witnessed_in ::
    "string set \<Rightarrow> ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_Henkin_witnessed_in C \<Gamma> T \<longleftrightarrow>
    (\<forall>\<sigma> A. \<sigma> # \<Gamma> \<turnstile> A : Prop \<longrightarrow> Exists \<sigma> A \<in> T \<longrightarrow>
      (\<exists>c \<in> C. subst0 (Const c \<sigma>) A \<in> T))"

definition CEV_supported_world ::
    "string set \<Rightarrow> string set \<Rightarrow> ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_supported_world K C \<Gamma> T \<longleftrightarrow>
    K \<subseteq> C \<and> C \<noteq> {} \<and> infinite (UNIV - C) \<and>
    CEV_clean_Henkin_theory \<Gamma> T \<and>
    CEV_Henkin_witnessed_in C \<Gamma> T"

definition CEV_supported_domain ::
    "string set \<Rightarrow> ctx \<Rightarrow> oterm set \<Rightarrow> otype \<Rightarrow> oterm set set" where
  "CEV_supported_domain C \<Gamma> T \<sigma> =
    {CEV_local_term_class \<Gamma> T \<sigma> M | M.
      \<Gamma> \<turnstile> M : \<sigma> \<and> CEV_supported_term C M}"

lemma CEV_supported_domain_nonempty:
  assumes "C \<noteq> {}"
  shows "CEV_supported_domain C \<Gamma> T \<sigma> \<noteq> {}"
proof -
  obtain c where "c \<in> C"
    using assms by blast
  then have
      "CEV_local_term_class \<Gamma> T \<sigma> (Const c \<sigma>)
        \<in> CEV_supported_domain C \<Gamma> T \<sigma>"
    unfolding CEV_supported_domain_def CEV_supported_term_def by auto
  then show ?thesis
    by blast
qed

lemma CEV_supported_local_app_closed:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
    and X_dom: "X \<in> CEV_supported_domain C \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and Y_dom: "Y \<in> CEV_supported_domain C \<Gamma> T \<sigma>"
  shows "CEV_local_app \<Gamma> T \<sigma> \<tau> X Y
    \<in> CEV_supported_domain C \<Gamma> T \<tau>"
proof -
  obtain F where F_type: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and F_support: "CEV_supported_term C F"
    and X_def:
      "X = CEV_local_term_class \<Gamma> T (\<sigma> \<rightarrow>\<^sub>o \<tau>) F"
    using X_dom unfolding CEV_supported_domain_def by blast
  obtain A where A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and A_support: "CEV_supported_term C A"
    and Y_def: "Y = CEV_local_term_class \<Gamma> T \<sigma> A"
    using Y_dom unfolding CEV_supported_domain_def by blast
  have app_type: "\<Gamma> \<turnstile> App F A : \<tau>"
    using F_type A_type by auto
  have app_support: "CEV_supported_term C (App F A)"
    using F_support A_support unfolding CEV_supported_term_def by auto
  have app_eq:
      "CEV_local_app \<Gamma> T \<sigma> \<tau> X Y =
        CEV_local_term_class \<Gamma> T \<tau> (App F A)"
    unfolding X_def Y_def
    using henkin F_type A_type by (rule CEV_local_app_class)
  show ?thesis
    unfolding app_eq CEV_supported_domain_def
    using app_type app_support by blast
qed

section \<open>Supported quotient arrows and their maps\<close>

definition CEV_supported_quotient_arrow ::
    "string set \<Rightarrow> string set \<Rightarrow>
      ctx \<Rightarrow> oterm set \<Rightarrow> ctx \<Rightarrow> oterm set \<Rightarrow>
      oterm env \<Rightarrow> bool" where
  "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s \<longleftrightarrow>
    CEV_clean_Henkin_theory \<Delta> S \<and>
    CEV_clean_Henkin_theory \<Gamma> T \<and>
    C \<subseteq> D \<and>
    term_subst_typed \<Delta> \<Gamma> s \<and>
    (\<forall>n. consts_of (s n) \<subseteq> D) \<and>
    (\<forall>\<sigma> M N.
      \<Delta> \<turnstile> M : \<sigma> \<longrightarrow> \<Delta> \<turnstile> N : \<sigma> \<longrightarrow>
      CEV_supported_term C M \<longrightarrow> CEV_supported_term C N \<longrightarrow>
      Eq \<sigma> M N \<in> S \<longrightarrow>
      Eq \<sigma> (subst s M) (subst s N) \<in> T)"

lemma CEV_supported_quotient_arrow_source:
  assumes "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
  shows "CEV_clean_Henkin_theory \<Delta> S"
  using assms unfolding CEV_supported_quotient_arrow_def by blast

lemma CEV_supported_quotient_arrow_target:
  assumes "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
  shows "CEV_clean_Henkin_theory \<Gamma> T"
  using assms unfolding CEV_supported_quotient_arrow_def by blast

lemma CEV_supported_quotient_arrow_supports:
  assumes "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
  shows "C \<subseteq> D"
  using assms unfolding CEV_supported_quotient_arrow_def by blast

lemma CEV_supported_quotient_arrow_typed:
  assumes "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
  shows "term_subst_typed \<Delta> \<Gamma> s"
  using assms unfolding CEV_supported_quotient_arrow_def by blast

lemma CEV_supported_quotient_arrow_image_support:
  assumes "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
  shows "consts_of (s n) \<subseteq> D"
  using assms unfolding CEV_supported_quotient_arrow_def by blast

lemma CEV_supported_subst:
  assumes arrow: "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
    and support: "CEV_supported_term C M"
  shows "CEV_supported_term D (subst s M)"
proof -
  have images: "\<And>n. consts_of (s n) \<subseteq> D"
    using arrow unfolding CEV_supported_quotient_arrow_def by blast
  have sub_consts: "consts_of (subst s M) \<subseteq> consts_of M \<union> D"
    using images by (rule consts_of_subst_subset)
  have source_target: "C \<subseteq> D"
    using arrow by (rule CEV_supported_quotient_arrow_supports)
  show ?thesis
    using sub_consts support source_target
    unfolding CEV_supported_term_def by blast
qed

lemma CEV_supported_quotient_arrow_preserves_equiv:
  assumes arrow: "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
    and M_support: "CEV_supported_term C M"
    and N_support: "CEV_supported_term C N"
    and MN: "CEV_local_term_equiv \<Delta> S \<sigma> M N"
  shows "CEV_local_term_equiv \<Gamma> T \<sigma> (subst s M) (subst s N)"
proof -
  have M_type: "\<Delta> \<turnstile> M : \<sigma>"
    and N_type: "\<Delta> \<turnstile> N : \<sigma>"
    and eq_in: "Eq \<sigma> M N \<in> S"
    using MN unfolding CEV_local_term_equiv_def by auto
  have s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    using arrow by (rule CEV_supported_quotient_arrow_typed)
  have sub_M_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
    using M_type s_typed by (rule term_subst_preserves_typing)
  have sub_N_type: "\<Gamma> \<turnstile> subst s N : \<sigma>"
    using N_type s_typed by (rule term_subst_preserves_typing)
  have eq_sub_in: "Eq \<sigma> (subst s M) (subst s N) \<in> T"
    using arrow M_type N_type M_support N_support eq_in
    unfolding CEV_supported_quotient_arrow_def by blast
  show ?thesis
    unfolding CEV_local_term_equiv_def
    using sub_M_type sub_N_type eq_sub_in by blast
qed

lemma CEV_supported_quotient_arrow_id:
  assumes henkin: "CEV_clean_Henkin_theory \<Gamma> T"
  shows "CEV_supported_quotient_arrow C C \<Gamma> T \<Gamma> T Var"
  unfolding CEV_supported_quotient_arrow_def CEV_supported_term_def
  using henkin term_subst_typed_Var by simp

lemma CEV_supported_quotient_arrow_comp:
  assumes s_arrow: "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
    and t_arrow: "CEV_supported_quotient_arrow D E \<Gamma> T \<Lambda> U t"
  shows "CEV_supported_quotient_arrow C E \<Delta> S \<Lambda> U
    (\<lambda>n. subst t (s n))"
proof -
  have source: "CEV_clean_Henkin_theory \<Delta> S"
    using s_arrow by (rule CEV_supported_quotient_arrow_source)
  have target: "CEV_clean_Henkin_theory \<Lambda> U"
    using t_arrow by (rule CEV_supported_quotient_arrow_target)
  have CD: "C \<subseteq> D"
    using s_arrow by (rule CEV_supported_quotient_arrow_supports)
  have DE: "D \<subseteq> E"
    using t_arrow by (rule CEV_supported_quotient_arrow_supports)
  have CE: "C \<subseteq> E"
    using CD DE by blast
  have s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    using s_arrow by (rule CEV_supported_quotient_arrow_typed)
  have t_typed: "term_subst_typed \<Gamma> \<Lambda> t"
    using t_arrow by (rule CEV_supported_quotient_arrow_typed)
  have comp_typed:
      "term_subst_typed \<Delta> \<Lambda> (\<lambda>n. subst t (s n))"
    using s_typed t_typed by (rule term_subst_typed_comp)
  have comp_support: "\<forall>n. consts_of (subst t (s n)) \<subseteq> E"
  proof
    fix n
    have s_support: "CEV_supported_term D (s n)"
      using s_arrow unfolding CEV_supported_quotient_arrow_def
        CEV_supported_term_def by blast
    show "consts_of (subst t (s n)) \<subseteq> E"
      using CEV_supported_subst[OF t_arrow s_support]
      unfolding CEV_supported_term_def .
  qed
  have preserves:
      "\<And>\<sigma> M N.
        \<Delta> \<turnstile> M : \<sigma> \<Longrightarrow> \<Delta> \<turnstile> N : \<sigma> \<Longrightarrow>
        CEV_supported_term C M \<Longrightarrow> CEV_supported_term C N \<Longrightarrow>
        Eq \<sigma> M N \<in> S \<Longrightarrow>
        Eq \<sigma> (subst (\<lambda>n. subst t (s n)) M)
          (subst (\<lambda>n. subst t (s n)) N) \<in> U"
  proof -
    fix \<sigma> M N
    assume M_type: "\<Delta> \<turnstile> M : \<sigma>"
      and N_type: "\<Delta> \<turnstile> N : \<sigma>"
      and M_support: "CEV_supported_term C M"
      and N_support: "CEV_supported_term C N"
      and eq_in: "Eq \<sigma> M N \<in> S"
    have eq_s_in: "Eq \<sigma> (subst s M) (subst s N) \<in> T"
      using s_arrow M_type N_type M_support N_support eq_in
      unfolding CEV_supported_quotient_arrow_def by blast
    have sub_M_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
      using M_type s_typed by (rule term_subst_preserves_typing)
    have sub_N_type: "\<Gamma> \<turnstile> subst s N : \<sigma>"
      using N_type s_typed by (rule term_subst_preserves_typing)
    have sub_M_support: "CEV_supported_term D (subst s M)"
      using s_arrow M_support by (rule CEV_supported_subst)
    have sub_N_support: "CEV_supported_term D (subst s N)"
      using s_arrow N_support by (rule CEV_supported_subst)
    have eq_t_in:
        "Eq \<sigma> (subst t (subst s M)) (subst t (subst s N)) \<in> U"
      using t_arrow sub_M_type sub_N_type sub_M_support sub_N_support eq_s_in
      unfolding CEV_supported_quotient_arrow_def by blast
    show "Eq \<sigma> (subst (\<lambda>n. subst t (s n)) M)
        (subst (\<lambda>n. subst t (s n)) N) \<in> U"
      using eq_t_in by (simp add: subst_comp)
  qed
  show ?thesis
    unfolding CEV_supported_quotient_arrow_def
    using source target CE comp_typed comp_support preserves by blast
qed

definition CEV_supported_map_rel where
  "CEV_supported_map_rel C D \<Delta> S \<Gamma> T s \<sigma> X Y \<longleftrightarrow>
    (\<exists>M. \<Delta> \<turnstile> M : \<sigma> \<and> CEV_supported_term C M \<and>
      X = CEV_local_term_class \<Delta> S \<sigma> M \<and>
      Y = CEV_local_term_class \<Gamma> T \<sigma> (subst s M))"

definition CEV_supported_map where
  "CEV_supported_map C D \<Delta> S \<Gamma> T s \<sigma> X =
    (THE Y. CEV_supported_map_rel C D \<Delta> S \<Gamma> T s \<sigma> X Y)"

lemma CEV_supported_map_rel_exists:
  assumes "X \<in> CEV_supported_domain C \<Delta> S \<sigma>"
  shows "\<exists>Y. CEV_supported_map_rel C D \<Delta> S \<Gamma> T s \<sigma> X Y"
  using assms
  unfolding CEV_supported_domain_def CEV_supported_map_rel_def by blast

lemma CEV_supported_map_rel_unique:
  assumes arrow: "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
    and rel_Y: "CEV_supported_map_rel C D \<Delta> S \<Gamma> T s \<sigma> X Y"
    and rel_Z: "CEV_supported_map_rel C D \<Delta> S \<Gamma> T s \<sigma> X Z"
  shows "Y = Z"
proof -
  obtain M where M_type: "\<Delta> \<turnstile> M : \<sigma>"
    and M_support: "CEV_supported_term C M"
    and X_M: "X = CEV_local_term_class \<Delta> S \<sigma> M"
    and Y_def: "Y = CEV_local_term_class \<Gamma> T \<sigma> (subst s M)"
    using rel_Y unfolding CEV_supported_map_rel_def by blast
  obtain N where N_type: "\<Delta> \<turnstile> N : \<sigma>"
    and N_support: "CEV_supported_term C N"
    and X_N: "X = CEV_local_term_class \<Delta> S \<sigma> N"
    and Z_def: "Z = CEV_local_term_class \<Gamma> T \<sigma> (subst s N)"
    using rel_Z unfolding CEV_supported_map_rel_def by blast
  have source: "CEV_clean_Henkin_theory \<Delta> S"
    using arrow by (rule CEV_supported_quotient_arrow_source)
  have target: "CEV_clean_Henkin_theory \<Gamma> T"
    using arrow by (rule CEV_supported_quotient_arrow_target)
  have classes_MN:
      "CEV_local_term_class \<Delta> S \<sigma> M =
        CEV_local_term_class \<Delta> S \<sigma> N"
    using X_M X_N by simp
  have MN: "CEV_local_term_equiv \<Delta> S \<sigma> M N"
    using CEV_local_term_class_eq[OF source M_type N_type] classes_MN
    by blast
  have sub_equiv:
      "CEV_local_term_equiv \<Gamma> T \<sigma> (subst s M) (subst s N)"
    using arrow M_support N_support MN
    by (rule CEV_supported_quotient_arrow_preserves_equiv)
  have s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    using arrow by (rule CEV_supported_quotient_arrow_typed)
  have sub_M_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
    using M_type s_typed by (rule term_subst_preserves_typing)
  have sub_N_type: "\<Gamma> \<turnstile> subst s N : \<sigma>"
    using N_type s_typed by (rule term_subst_preserves_typing)
  have classes_sub:
      "CEV_local_term_class \<Gamma> T \<sigma> (subst s M) =
        CEV_local_term_class \<Gamma> T \<sigma> (subst s N)"
    using CEV_local_term_class_eq[
      OF target sub_M_type sub_N_type] sub_equiv by blast
  show "Y = Z"
    using Y_def Z_def classes_sub by simp
qed

lemma CEV_supported_map_class:
  assumes arrow: "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
    and M_type: "\<Delta> \<turnstile> M : \<sigma>"
    and M_support: "CEV_supported_term C M"
  shows "CEV_supported_map C D \<Delta> S \<Gamma> T s \<sigma>
      (CEV_local_term_class \<Delta> S \<sigma> M) =
    CEV_local_term_class \<Gamma> T \<sigma> (subst s M)"
proof -
  let ?X = "CEV_local_term_class \<Delta> S \<sigma> M"
  let ?Y = "CEV_local_term_class \<Gamma> T \<sigma> (subst s M)"
  have rel: "CEV_supported_map_rel C D \<Delta> S \<Gamma> T s \<sigma> ?X ?Y"
    unfolding CEV_supported_map_rel_def
    using M_type M_support by blast
  have unique:
      "\<And>Z. CEV_supported_map_rel C D \<Delta> S \<Gamma> T s \<sigma> ?X Z
        \<Longrightarrow> Z = ?Y"
  proof -
    fix Z
    assume rel_Z:
      "CEV_supported_map_rel C D \<Delta> S \<Gamma> T s \<sigma> ?X Z"
    have "?Y = Z"
      using arrow rel rel_Z by (rule CEV_supported_map_rel_unique)
    then show "Z = ?Y"
      by simp
  qed
  show ?thesis
    unfolding CEV_supported_map_def
    using rel unique by (rule the_equality)
qed

lemma CEV_supported_map_closed:
  assumes arrow: "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
    and X_dom: "X \<in> CEV_supported_domain C \<Delta> S \<sigma>"
  shows "CEV_supported_map C D \<Delta> S \<Gamma> T s \<sigma> X
    \<in> CEV_supported_domain D \<Gamma> T \<sigma>"
proof -
  obtain M where M_type: "\<Delta> \<turnstile> M : \<sigma>"
    and M_support: "CEV_supported_term C M"
    and X_def: "X = CEV_local_term_class \<Delta> S \<sigma> M"
    using X_dom unfolding CEV_supported_domain_def by blast
  have s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    using arrow by (rule CEV_supported_quotient_arrow_typed)
  have sub_type: "\<Gamma> \<turnstile> subst s M : \<sigma>"
    using M_type s_typed by (rule term_subst_preserves_typing)
  have sub_support: "CEV_supported_term D (subst s M)"
    using arrow M_support by (rule CEV_supported_subst)
  have map_eq:
      "CEV_supported_map C D \<Delta> S \<Gamma> T s \<sigma> X =
        CEV_local_term_class \<Gamma> T \<sigma> (subst s M)"
    unfolding X_def
    using arrow M_type M_support by (rule CEV_supported_map_class)
  show ?thesis
    unfolding map_eq CEV_supported_domain_def
    using sub_type sub_support by blast
qed

lemma CEV_supported_map_const:
  assumes arrow: "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
    and c_support: "c \<in> C"
  shows "CEV_supported_map C D \<Delta> S \<Gamma> T s \<sigma>
      (CEV_local_term_class \<Delta> S \<sigma> (Const c \<sigma>)) =
    CEV_local_term_class \<Gamma> T \<sigma> (Const c \<sigma>)"
proof -
  have const_type: "\<Delta> \<turnstile> Const c \<sigma> : \<sigma>"
    by auto
  have const_support: "CEV_supported_term C (Const c \<sigma>)"
    using c_support unfolding CEV_supported_term_def by simp
  show ?thesis
    using CEV_supported_map_class[
      OF arrow const_type const_support] by simp
qed

lemma CEV_supported_map_preserves_app:
  assumes arrow: "CEV_supported_quotient_arrow C D \<Delta> S \<Gamma> T s"
    and F_type: "\<Delta> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    and A_type: "\<Delta> \<turnstile> A : \<sigma>"
    and F_support: "CEV_supported_term C F"
    and A_support: "CEV_supported_term C A"
  shows "CEV_supported_map C D \<Delta> S \<Gamma> T s \<tau>
      (CEV_local_app \<Delta> S \<sigma> \<tau>
        (CEV_local_term_class \<Delta> S (\<sigma> \<rightarrow>\<^sub>o \<tau>) F)
        (CEV_local_term_class \<Delta> S \<sigma> A)) =
    CEV_local_app \<Gamma> T \<sigma> \<tau>
      (CEV_supported_map C D \<Delta> S \<Gamma> T s
        (\<sigma> \<rightarrow>\<^sub>o \<tau>)
        (CEV_local_term_class \<Delta> S (\<sigma> \<rightarrow>\<^sub>o \<tau>) F))
      (CEV_supported_map C D \<Delta> S \<Gamma> T s \<sigma>
        (CEV_local_term_class \<Delta> S \<sigma> A))"
proof -
  have source: "CEV_clean_Henkin_theory \<Delta> S"
    using arrow by (rule CEV_supported_quotient_arrow_source)
  have target: "CEV_clean_Henkin_theory \<Gamma> T"
    using arrow by (rule CEV_supported_quotient_arrow_target)
  have s_typed: "term_subst_typed \<Delta> \<Gamma> s"
    using arrow by (rule CEV_supported_quotient_arrow_typed)
  have sub_F_type: "\<Gamma> \<turnstile> subst s F : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using F_type s_typed by (rule term_subst_preserves_typing)
  have sub_A_type: "\<Gamma> \<turnstile> subst s A : \<sigma>"
    using A_type s_typed by (rule term_subst_preserves_typing)
  have app_type: "\<Delta> \<turnstile> App F A : \<tau>"
    using F_type A_type by auto
  have app_support: "CEV_supported_term C (App F A)"
    using F_support A_support unfolding CEV_supported_term_def by auto
  show ?thesis
    using CEV_local_app_class[OF source F_type A_type]
      CEV_supported_map_class[OF arrow app_type app_support]
      CEV_supported_map_class[OF arrow F_type F_support]
      CEV_supported_map_class[OF arrow A_type A_support]
      CEV_local_app_class[OF target sub_F_type sub_A_type]
    by simp
qed

lemma CEV_supported_identity_diagram_typed:
  "typed_theory \<Gamma> (CEV_supported_identity_diagram C \<Gamma> S)"
  unfolding typed_theory_def CEV_supported_identity_diagram_def
  by auto

lemma CEV_supported_identity_diagram_subset:
  "CEV_supported_identity_diagram C \<Gamma> S
    \<subseteq> CEV_identity_diagram \<Gamma> S"
proof
  fix E
  assume E_in: "E \<in> CEV_supported_identity_diagram C \<Gamma> S"
  obtain \<sigma> M N where E_def: "E = Eq \<sigma> M N"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and eq_in: "Eq \<sigma> M N \<in> S"
    using E_in unfolding CEV_supported_identity_diagram_def by blast
  show "E \<in> CEV_identity_diagram \<Gamma> S"
    unfolding CEV_identity_diagram_iff
    using E_def M_type N_type eq_in by blast
qed

lemma CEV_supported_identity_diagram_consts:
  "consts_of_set (CEV_supported_identity_diagram C \<Gamma> S) \<subseteq> C"
proof
  fix c
  assume c_in:
    "c \<in> consts_of_set (CEV_supported_identity_diagram C \<Gamma> S)"
  obtain E where E_in: "E \<in> CEV_supported_identity_diagram C \<Gamma> S"
    and c_E: "c \<in> consts_of E"
    using c_in by (rule consts_of_setD)
  obtain \<sigma> M N where E_def: "E = Eq \<sigma> M N"
    and M_support: "CEV_supported_term C M"
    and N_support: "CEV_supported_term C N"
    using E_in unfolding CEV_supported_identity_diagram_def by blast
  show "c \<in> C"
    using c_E M_support N_support
    unfolding E_def CEV_supported_term_def by auto
qed

lemma CEV_supported_identity_diagram_subset_gives_arrow:
  assumes source: "CEV_clean_Henkin_theory \<Gamma> S"
    and target: "CEV_clean_Henkin_theory \<Gamma> T"
    and CD: "C \<subseteq> D"
    and diagram: "CEV_supported_identity_diagram C \<Gamma> S \<subseteq> T"
  shows "CEV_supported_quotient_arrow C D \<Gamma> S \<Gamma> T Var"
proof -
  have preserves:
      "\<And>\<sigma> M N.
        \<Gamma> \<turnstile> M : \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> N : \<sigma> \<Longrightarrow>
        CEV_supported_term C M \<Longrightarrow> CEV_supported_term C N \<Longrightarrow>
        Eq \<sigma> M N \<in> S \<Longrightarrow> Eq \<sigma> M N \<in> T"
  proof -
    fix \<sigma> M N
    assume M_type: "\<Gamma> \<turnstile> M : \<sigma>"
      and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
      and M_support: "CEV_supported_term C M"
      and N_support: "CEV_supported_term C N"
      and eq_in: "Eq \<sigma> M N \<in> S"
    have "Eq \<sigma> M N \<in> CEV_supported_identity_diagram C \<Gamma> S"
      unfolding CEV_supported_identity_diagram_def
      using M_type N_type M_support N_support eq_in by blast
    then show "Eq \<sigma> M N \<in> T"
      using diagram by blast
  qed
  show ?thesis
    unfolding CEV_supported_quotient_arrow_def
    using source target CD term_subst_typed_Var preserves by simp
qed

section \<open>Henkin extension from a designated witness block\<close>

definition CEV_block_fresh_const ::
    "string set \<Rightarrow> oterm set \<Rightarrow> oterm \<Rightarrow> string" where
  "CEV_block_fresh_const D T A =
    (SOME c. c \<in> D \<and> fresh_const_for c T A)"

definition CEV_block_henkin_step ::
    "ctx \<Rightarrow> string set \<Rightarrow> otype \<times> oterm \<Rightarrow>
      oterm set \<Rightarrow> oterm set" where
  "CEV_block_henkin_step \<Gamma> D spec T =
    (case spec of (\<sigma>, A) \<Rightarrow>
      if \<sigma> # \<Gamma> \<turnstile> A : Prop
      then insert
        (henkin_witness_axiom (CEV_block_fresh_const D T A) \<sigma> A) T
      else T)"

primrec CEV_block_henkin_chain ::
    "ctx \<Rightarrow> string set \<Rightarrow> oterm set \<Rightarrow>
      (nat \<Rightarrow> otype \<times> oterm) \<Rightarrow> nat \<Rightarrow> oterm set" where
  "CEV_block_henkin_chain \<Gamma> D B enum 0 = B"
| "CEV_block_henkin_chain \<Gamma> D B enum (Suc n) =
    CEV_block_henkin_step \<Gamma> D (enum n)
      (CEV_block_henkin_chain \<Gamma> D B enum n)"

definition CEV_block_henkin_extension ::
    "ctx \<Rightarrow> string set \<Rightarrow> oterm set \<Rightarrow>
      (nat \<Rightarrow> otype \<times> oterm) \<Rightarrow> oterm set" where
  "CEV_block_henkin_extension \<Gamma> D B enum =
    (\<Union>n. CEV_block_henkin_chain \<Gamma> D B enum n)"

definition CEV_Henkin_witness_axioms_available_in ::
    "string set \<Rightarrow> ctx \<Rightarrow> oterm set \<Rightarrow> bool" where
  "CEV_Henkin_witness_axioms_available_in D \<Gamma> T \<longleftrightarrow>
    (\<forall>\<sigma> A. \<sigma> # \<Gamma> \<turnstile> A : Prop \<longrightarrow>
      (\<exists>c \<in> D. henkin_witness_axiom c \<sigma> A \<in> T))"

lemma CEV_block_fresh_exists:
  assumes D_infinite: "infinite D"
    and D_base: "D \<inter> consts_of_set B = {}"
    and base_sub: "B \<subseteq> T"
    and finite_extra: "finite (T - B)"
  shows "\<exists>c. c \<in> D \<and> fresh_const_for c T A"
proof -
  have finite_extra_consts: "finite (consts_of_set (T - B))"
    using finite_extra by (rule finite_consts_of_set)
  have finite_forbidden:
      "finite (consts_of_set (T - B) \<union> consts_of A)"
    using finite_extra_consts by simp
  have not_subset:
      "\<not> D \<subseteq> consts_of_set (T - B) \<union> consts_of A"
  proof
    assume subset:
      "D \<subseteq> consts_of_set (T - B) \<union> consts_of A"
    have "finite D"
      by (rule finite_subset[OF subset finite_forbidden])
    then show False
      using D_infinite by contradiction
  qed
  obtain c where c_D: "c \<in> D"
    and c_extra: "c \<notin> consts_of_set (T - B)"
    and c_A: "c \<notin> consts_of A"
    using not_subset by blast
  have c_base: "c \<notin> consts_of_set B"
    using c_D D_base by blast
  have cover:
      "consts_of_set T \<subseteq>
        consts_of_set B \<union> consts_of_set (T - B)"
    unfolding consts_of_set_def using base_sub by blast
  have c_T: "c \<notin> consts_of_set T"
    using cover c_base c_extra by blast
  have fresh: "fresh_const_for c T A"
    using c_T c_A unfolding fresh_const_for_def by simp
  show ?thesis
    using c_D fresh by blast
qed

lemma CEV_block_fresh_const:
  assumes D_infinite: "infinite D"
    and D_base: "D \<inter> consts_of_set B = {}"
    and base_sub: "B \<subseteq> T"
    and finite_extra: "finite (T - B)"
  shows "CEV_block_fresh_const D T A \<in> D"
    and "fresh_const_for (CEV_block_fresh_const D T A) T A"
proof -
  have exists:
      "\<exists>c. c \<in> D \<and> fresh_const_for c T A"
    using assms by (rule CEV_block_fresh_exists)
  have chosen:
      "CEV_block_fresh_const D T A \<in> D \<and>
        fresh_const_for (CEV_block_fresh_const D T A) T A"
    unfolding CEV_block_fresh_const_def
    using exists by (rule someI_ex)
  then show "CEV_block_fresh_const D T A \<in> D"
    by (rule conjunct1)
  from chosen show
      "fresh_const_for (CEV_block_fresh_const D T A) T A"
    by (rule conjunct2)
qed

lemma CEV_block_henkin_step_extends:
  "T \<subseteq> CEV_block_henkin_step \<Gamma> D spec T"
  unfolding CEV_block_henkin_step_def
  by (cases spec) auto

lemma CEV_block_henkin_step_typed:
  assumes "typed_theory \<Gamma> T"
  shows "typed_theory \<Gamma> (CEV_block_henkin_step \<Gamma> D spec T)"
  using assms unfolding CEV_block_henkin_step_def
  by (cases spec)
    (auto intro: typed_theory_insert_henkin_witness_axiom)

lemma CEV_block_henkin_step_adds:
  assumes "spec = (\<sigma>, A)"
    and "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  shows "henkin_witness_axiom (CEV_block_fresh_const D T A) \<sigma> A
    \<in> CEV_block_henkin_step \<Gamma> D spec T"
  using assms unfolding CEV_block_henkin_step_def by simp

lemma CEV_block_henkin_chain_step:
  "CEV_block_henkin_chain \<Gamma> D B enum n \<subseteq>
    CEV_block_henkin_chain \<Gamma> D B enum (Suc n)"
  using CEV_block_henkin_step_extends[
    of "CEV_block_henkin_chain \<Gamma> D B enum n" \<Gamma> D "enum n"]
  by simp

lemma CEV_block_henkin_chain_extends_base:
  "B \<subseteq> CEV_block_henkin_chain \<Gamma> D B enum n"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have step:
      "CEV_block_henkin_chain \<Gamma> D B enum n \<subseteq>
        CEV_block_henkin_chain \<Gamma> D B enum (Suc n)"
    by (rule CEV_block_henkin_chain_step)
  show ?case
    using Suc.IH step by blast
qed

lemma CEV_block_henkin_chain_finite_over_base:
  "finite (CEV_block_henkin_chain \<Gamma> D B enum n - B)"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  obtain \<sigma> A where spec: "enum n = (\<sigma>, A)"
    by (cases "enum n") auto
  let ?T = "CEV_block_henkin_chain \<Gamma> D B enum n"
  let ?W =
    "henkin_witness_axiom (CEV_block_fresh_const D ?T A) \<sigma> A"
  have finite_insert: "finite (insert ?W (?T - B))"
    using Suc.IH by simp
  have subset: "insert ?W ?T - B \<subseteq> insert ?W (?T - B)"
    by blast
  have finite_step: "finite (insert ?W ?T - B)"
    by (rule finite_subset[OF subset finite_insert])
  show ?case
    using Suc.IH finite_step
    by (simp add: CEV_block_henkin_step_def spec)
qed

lemma CEV_block_henkin_chain_typed:
  assumes "typed_theory \<Gamma> B"
  shows "typed_theory \<Gamma> (CEV_block_henkin_chain \<Gamma> D B enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have typed_n:
      "typed_theory \<Gamma> (CEV_block_henkin_chain \<Gamma> D B enum n)"
    using Suc.IH Suc.prems by blast
  show ?case
    using typed_n by (simp add: CEV_block_henkin_step_typed)
qed

lemma CEV_block_henkin_extension_extends:
  "B \<subseteq> CEV_block_henkin_extension \<Gamma> D B enum"
proof
  fix A
  assume "A \<in> B"
  then have
      "A \<in> CEV_block_henkin_chain \<Gamma> D B enum 0"
    by simp
  then show "A \<in> CEV_block_henkin_extension \<Gamma> D B enum"
    unfolding CEV_block_henkin_extension_def by blast
qed

lemma CEV_block_henkin_extension_typed:
  assumes "typed_theory \<Gamma> B"
  shows "typed_theory \<Gamma> (CEV_block_henkin_extension \<Gamma> D B enum)"
proof -
  have "\<And>n. typed_theory \<Gamma>
      (CEV_block_henkin_chain \<Gamma> D B enum n)"
    using assms by (rule CEV_block_henkin_chain_typed)
  then show ?thesis
    unfolding CEV_block_henkin_extension_def
    by (rule typed_theory_nat_union)
qed

lemma CEV_block_henkin_step_consistent:
  assumes D_infinite: "infinite D"
    and D_base: "D \<inter> consts_of_set B = {}"
    and base_sub: "B \<subseteq> T"
    and finite_extra: "finite (T - B)"
    and typed: "typed_theory \<Gamma> T"
    and consistent: "CEV_consistent \<Gamma> T"
  shows "CEV_consistent \<Gamma> (CEV_block_henkin_step \<Gamma> D spec T)"
proof -
  obtain \<sigma> A where spec_def: "spec = (\<sigma>, A)"
    by (cases spec) auto
  show ?thesis
  proof (cases "\<sigma> # \<Gamma> \<turnstile> A : Prop")
    case True
    have fresh:
        "fresh_const_for (CEV_block_fresh_const D T A) T A"
      using assms(1-4) by (rule CEV_block_fresh_const(2))
    have fresh_T:
        "CEV_block_fresh_const D T A \<notin> consts_of_set T"
      using fresh unfolding fresh_const_for_def by (rule conjunct1)
    have fresh_A:
        "CEV_block_fresh_const D T A \<notin> consts_of A"
      using fresh unfolding fresh_const_for_def by (rule conjunct2)
    have insert_consistent:
        "CEV_consistent \<Gamma>
          (insert
            (henkin_witness_axiom
              (CEV_block_fresh_const D T A) \<sigma> A) T)"
      using typed consistent fresh_T fresh_A True
      by (rule CEV_consistent_insert_fresh_witness_axiom_clean)
    show ?thesis
      unfolding CEV_block_henkin_step_def spec_def
      using True insert_consistent by simp
  next
    case False
    then show ?thesis
      unfolding CEV_block_henkin_step_def spec_def
      using consistent by simp
  qed
qed

lemma CEV_block_henkin_chain_consistent:
  assumes D_infinite: "infinite D"
    and D_base: "D \<inter> consts_of_set B = {}"
    and typed: "typed_theory \<Gamma> B"
    and consistent: "CEV_consistent \<Gamma> B"
  shows "CEV_consistent \<Gamma>
    (CEV_block_henkin_chain \<Gamma> D B enum n)"
  using assms
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  let ?T = "CEV_block_henkin_chain \<Gamma> D B enum n"
  have base_sub: "B \<subseteq> ?T"
    by (rule CEV_block_henkin_chain_extends_base)
  have finite_extra: "finite (?T - B)"
    by (rule CEV_block_henkin_chain_finite_over_base)
  have typed_T: "typed_theory \<Gamma> ?T"
    using Suc.prems(3) by (rule CEV_block_henkin_chain_typed)
  have consistent_T: "CEV_consistent \<Gamma> ?T"
    using Suc.prems by (rule Suc.IH)
  show ?case
    using Suc.prems(1,2) base_sub finite_extra typed_T consistent_T
    by (simp add: CEV_block_henkin_step_consistent)
qed

lemma CEV_block_henkin_extension_consistent:
  assumes D_infinite: "infinite D"
    and D_base: "D \<inter> consts_of_set B = {}"
    and typed: "typed_theory \<Gamma> B"
    and consistent: "CEV_consistent \<Gamma> B"
  shows "CEV_consistent \<Gamma>
    (CEV_block_henkin_extension \<Gamma> D B enum)"
proof (unfold CEV_consistent_def, intro notI)
  assume d_false:
      "\<Gamma> ; CEV_block_henkin_extension \<Gamma> D B enum
        \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  obtain U where finite_U: "finite U"
    and U_sub: "U \<subseteq> CEV_block_henkin_extension \<Gamma> D B enum"
    and d_U: "\<Gamma> ; U \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using d_false by (rule CEV_set_derivable_finite_support)
  have U_sub_union:
      "U \<subseteq> (\<Union>n. CEV_block_henkin_chain \<Gamma> D B enum n)"
    using U_sub unfolding CEV_block_henkin_extension_def .
  have step:
      "\<And>n. CEV_block_henkin_chain \<Gamma> D B enum n \<subseteq>
        CEV_block_henkin_chain \<Gamma> D B enum (Suc n)"
    by (rule CEV_block_henkin_chain_step)
  obtain n where U_sub_chain:
      "U \<subseteq> CEV_block_henkin_chain \<Gamma> D B enum n"
    using finite_U U_sub_union step finite_subset_nat_chain by blast
  have d_chain:
      "\<Gamma> ; CEV_block_henkin_chain \<Gamma> D B enum n
        \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
    using d_U U_sub_chain by (rule CEV_set_derivable_mono)
  have chain_consistent:
      "CEV_consistent \<Gamma> (CEV_block_henkin_chain \<Gamma> D B enum n)"
    using assms by (rule CEV_block_henkin_chain_consistent)
  show False
    using d_chain chain_consistent
    unfolding CEV_consistent_def by contradiction
qed

lemma CEV_block_henkin_extension_witness_axioms_available_in:
  assumes body_enum: "enumerates_witness_bodies \<Gamma> enum"
    and D_infinite: "infinite D"
    and D_base: "D \<inter> consts_of_set B = {}"
  shows "CEV_Henkin_witness_axioms_available_in D \<Gamma>
    (CEV_block_henkin_extension \<Gamma> D B enum)"
proof (unfold CEV_Henkin_witness_axioms_available_in_def,
    intro allI impI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
  obtain n where enum_n: "enum n = (\<sigma>, A)"
    using body_enum A_type
    unfolding enumerates_witness_bodies_def by blast
  let ?T = "CEV_block_henkin_chain \<Gamma> D B enum n"
  let ?c = "CEV_block_fresh_const D ?T A"
  have base_sub: "B \<subseteq> ?T"
    by (rule CEV_block_henkin_chain_extends_base)
  have finite_extra: "finite (?T - B)"
    by (rule CEV_block_henkin_chain_finite_over_base)
  have c_D: "?c \<in> D"
    using D_infinite D_base base_sub finite_extra
    by (rule CEV_block_fresh_const(1))
  have ax_step:
      "henkin_witness_axiom ?c \<sigma> A
        \<in> CEV_block_henkin_chain \<Gamma> D B enum (Suc n)"
  proof -
    have "henkin_witness_axiom ?c \<sigma> A
        \<in> CEV_block_henkin_step \<Gamma> D (enum n) ?T"
      using enum_n A_type by (rule CEV_block_henkin_step_adds)
    then show ?thesis
      by simp
  qed
  have ax_ext:
      "henkin_witness_axiom ?c \<sigma> A
        \<in> CEV_block_henkin_extension \<Gamma> D B enum"
    using ax_step unfolding CEV_block_henkin_extension_def by blast
  show "\<exists>c \<in> D.
      henkin_witness_axiom c \<sigma> A
        \<in> CEV_block_henkin_extension \<Gamma> D B enum"
    using c_D ax_ext by blast
qed

lemma CEV_Henkin_witness_axioms_available_in_mono:
  assumes available: "CEV_Henkin_witness_axioms_available_in D \<Gamma> T"
    and subset: "T \<subseteq> U"
  shows "CEV_Henkin_witness_axioms_available_in D \<Gamma> U"
  using available subset
  unfolding CEV_Henkin_witness_axioms_available_in_def by blast

lemma CEV_Henkin_witnessed_in_of_local_available:
  assumes local: "CEV_locally_maximal_consistent \<Gamma> T"
    and available: "CEV_Henkin_witness_axioms_available_in D \<Gamma> T"
  shows "CEV_Henkin_witnessed_in D \<Gamma> T"
proof (unfold CEV_Henkin_witnessed_in_def, intro allI impI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and exists_in: "Exists \<sigma> A \<in> T"
  obtain c where c_D: "c \<in> D"
    and ax_in: "henkin_witness_axiom c \<sigma> A \<in> T"
    using available A_type
    unfolding CEV_Henkin_witness_axioms_available_in_def by blast
  have exists_type: "\<Gamma> \<turnstile> Exists \<sigma> A : Prop"
    using A_type by auto
  have ax_type: "\<Gamma> \<turnstile> henkin_witness_axiom c \<sigma> A : Prop"
    using A_type by (rule henkin_witness_axiom_typed)
  have d_exists: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s Exists \<sigma> A"
    using exists_in exists_type by (rule CEV_set_derivable.Assumption)
  have d_ax_raw:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s henkin_witness_axiom c \<sigma> A"
    using ax_in ax_type by (rule CEV_set_derivable.Assumption)
  have d_ax:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s
        Imp (Exists \<sigma> A) (subst0 (Const c \<sigma>) A)"
    using d_ax_raw unfolding henkin_witness_axiom_def by simp
  have d_inst:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s subst0 (Const c \<sigma>) A"
    using d_exists d_ax by (rule CEV_set_derivable.Derive_MP)
  have inst_in: "subst0 (Const c \<sigma>) A \<in> T"
    using local d_inst
    by (rule CEV_locally_maximal_consistent_deductively_closed)
  show "\<exists>c \<in> D. subst0 (Const c \<sigma>) A \<in> T"
    using c_D inst_in by blast
qed

lemma CEV_Henkin_witnessed_in_imp_Henkin_witnessed:
  assumes "CEV_Henkin_witnessed_in D \<Gamma> T"
  shows "Henkin_witnessed \<Gamma> T"
proof (unfold Henkin_witnessed_def, intro allI impI)
  fix \<sigma> A
  assume A_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and exists_in: "Exists \<sigma> A \<in> T"
  obtain c where inst_in: "subst0 (Const c \<sigma>) A \<in> T"
    using assms A_type exists_in
    unfolding CEV_Henkin_witnessed_in_def by blast
  show "\<exists>W. \<Gamma> \<turnstile> W : \<sigma> \<and> subst0 W A \<in> T"
    using inst_in by (intro exI[of _ "Const c \<sigma>"]) auto
qed

lemma CEV_Henkin_witnessed_in_mono:
  assumes "D \<subseteq> E"
    and "CEV_Henkin_witnessed_in D \<Gamma> T"
  shows "CEV_Henkin_witnessed_in E \<Gamma> T"
  using assms unfolding CEV_Henkin_witnessed_in_def by blast

lemma CEV_Henkin_witnessed_in_not_theory_mono:
  "\<not> (\<forall>D \<Gamma> T U.
    CEV_Henkin_witnessed_in D \<Gamma> T \<longrightarrow> T \<subseteq> U \<longrightarrow>
    CEV_Henkin_witnessed_in D \<Gamma> U)"
proof
  assume mono:
    "\<forall>D \<Gamma> T U.
      CEV_Henkin_witnessed_in D \<Gamma> T \<longrightarrow> T \<subseteq> U \<longrightarrow>
      CEV_Henkin_witnessed_in D \<Gamma> U"
  let ?A = "Eq Ind (Var 0) (Var 0)"
  let ?U = "{Exists Ind ?A}"
  have A_type: "Ind # [] \<turnstile> ?A : Prop"
    by auto
  have empty_w: "CEV_Henkin_witnessed_in UNIV [] {}"
    unfolding CEV_Henkin_witnessed_in_def by simp
  have U_w: "CEV_Henkin_witnessed_in UNIV [] ?U"
    using mono empty_w by blast
  have exists_in: "Exists Ind ?A \<in> ?U"
    by simp
  obtain c where inst_in: "subst0 (Const c Ind) ?A \<in> ?U"
    using U_w A_type exists_in
    unfolding CEV_Henkin_witnessed_in_def by blast
  have inst_eq:
      "subst0 (Const c Ind) ?A =
        Eq Ind (Const c Ind) (Const c Ind)"
    unfolding subst0_def by simp
  show False
    using inst_in inst_eq by simp
qed

theorem CEV_clean_Henkin_extension_from_block:
  assumes typed: "typed_theory \<Gamma> B"
    and consistent: "CEV_consistent \<Gamma> B"
    and D_infinite: "infinite D"
    and D_base: "D \<inter> consts_of_set B = {}"
  obtains T where "CEV_clean_Henkin_theory \<Gamma> T"
    and "B \<subseteq> T"
    and "CEV_Henkin_witnessed_in D \<Gamma> T"
proof -
  obtain body_enum where
      body_enum: "enumerates_witness_bodies \<Gamma> body_enum"
    using enumerates_witness_bodies_exists by blast
  let ?S = "CEV_block_henkin_extension \<Gamma> D B body_enum"
  have B_sub_S: "B \<subseteq> ?S"
    by (rule CEV_block_henkin_extension_extends)
  have typed_S: "typed_theory \<Gamma> ?S"
    using typed by (rule CEV_block_henkin_extension_typed)
  have consistent_S: "CEV_consistent \<Gamma> ?S"
    using D_infinite D_base typed consistent
    by (rule CEV_block_henkin_extension_consistent)
  have available_S:
      "CEV_Henkin_witness_axioms_available_in D \<Gamma> ?S"
    using body_enum D_infinite D_base
    by (rule CEV_block_henkin_extension_witness_axioms_available_in)
  obtain formula_enum where
      formula_enum: "enumerates_formulas \<Gamma> formula_enum"
    using enumerates_formulas_exists by blast
  let ?T = "CEV_lindenbaum_extension \<Gamma> ?S formula_enum"
  have S_sub_T: "?S \<subseteq> ?T"
    by (rule CEV_lindenbaum_extension_extends)
  have local_T: "CEV_locally_maximal_consistent \<Gamma> ?T"
    using typed_S consistent_S formula_enum
    by (rule CEV_lindenbaum_extension_locally_maximal_consistent)
  have available_T:
      "CEV_Henkin_witness_axioms_available_in D \<Gamma> ?T"
    using available_S S_sub_T
    by (rule CEV_Henkin_witness_axioms_available_in_mono)
  have witnessed_in_T: "CEV_Henkin_witnessed_in D \<Gamma> ?T"
    using local_T available_T
    by (rule CEV_Henkin_witnessed_in_of_local_available)
  have witnessed_T: "Henkin_witnessed \<Gamma> ?T"
    using witnessed_in_T
    by (rule CEV_Henkin_witnessed_in_imp_Henkin_witnessed)
  have henkin_T: "CEV_clean_Henkin_theory \<Gamma> ?T"
    using local_T witnessed_T
    unfolding CEV_clean_Henkin_theory_def by blast
  have B_sub_T: "B \<subseteq> ?T"
    using B_sub_S S_sub_T by blast
  show ?thesis
    using that[OF henkin_T B_sub_T witnessed_in_T] .
qed

section \<open>Supported canonical roots and successors\<close>

lemma consts_of_set_insert:
  "consts_of_set (insert A T) = consts_of A \<union> consts_of_set T"
  unfolding consts_of_set_def by auto

lemma consts_of_set_mono:
  assumes "T \<subseteq> U"
  shows "consts_of_set T \<subseteq> consts_of_set U"
  using assms unfolding consts_of_set_def by blast

theorem CEV_supported_counterworld:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and not_proves: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  obtains K C T where
    "finite K"
    and "K \<noteq> {}"
    and "consts_of A \<subseteq> K"
    and "CEV_supported_world K C \<Gamma> T"
    and "Neg A \<in> T"
    and "A \<notin> T"
proof -
  let ?K = "insert ([] :: string) (consts_of A)"
  let ?X = "UNIV - ?K"
  have finite_K: "finite ?K"
    by simp
  have nonempty_K: "?K \<noteq> {}"
    by simp
  have support_A: "consts_of A \<subseteq> ?K"
    by blast
  have inf_UNIV: "infinite (UNIV :: string set)"
    by (simp add: infinite_UNIV_listI)
  have inf_X: "infinite ?X"
    using finite_K inf_UNIV by simp
  obtain D R where
      D_X: "D \<subseteq> ?X"
    and R_X: "R \<subseteq> ?X"
    and inf_D: "infinite D"
    and inf_R: "infinite R"
    and disjoint: "D \<inter> R = {}"
    using inf_X by (rule infinite_split)
  let ?B = "{Neg A}"
  have typed_B: "typed_theory \<Gamma> ?B"
    using A_type unfolding typed_theory_def by auto
  have consistent_B: "CEV_consistent \<Gamma> ?B"
    using A_type not_proves
    by (rule CEV_consistent_singleton_neg_of_not_proves)
  have consts_B: "consts_of_set ?B = consts_of A"
    unfolding consts_of_set_def by auto
  have D_B: "D \<inter> consts_of_set ?B = {}"
    using D_X support_A unfolding consts_B by blast
  obtain T where
      target: "CEV_clean_Henkin_theory \<Gamma> T"
    and B_T: "?B \<subseteq> T"
    and witnessed_D: "CEV_Henkin_witnessed_in D \<Gamma> T"
    using typed_B consistent_B inf_D D_B
    by (rule CEV_clean_Henkin_extension_from_block)
  let ?C = "?K \<union> D"
  have K_C: "?K \<subseteq> ?C"
    by blast
  have nonempty_C: "?C \<noteq> {}"
    using nonempty_K by blast
  have R_compl: "R \<subseteq> UNIV - ?C"
    using R_X disjoint by blast
  have inf_compl: "infinite (UNIV - ?C)"
    using R_compl inf_R by (rule infinite_super)
  have D_C: "D \<subseteq> ?C"
    by blast
  have witnessed_C: "CEV_Henkin_witnessed_in ?C \<Gamma> T"
    using D_C witnessed_D by (rule CEV_Henkin_witnessed_in_mono)
  have world: "CEV_supported_world ?K ?C \<Gamma> T"
    unfolding CEV_supported_world_def
    using K_C nonempty_C inf_compl target witnessed_C by blast
  have neg_in: "Neg A \<in> T"
    using B_T by simp
  have A_absent: "A \<notin> T"
    using target A_type neg_in
    by (rule CEV_clean_Henkin_formula_absent_of_neg_in)
  show ?thesis
    using that[OF finite_K nonempty_K support_A world neg_in A_absent] .
qed

theorem CEV_supported_modal_successor:
  assumes world: "CEV_supported_world K C \<Gamma> S"
    and A_type: "\<Gamma> \<turnstile> A : Prop"
    and A_support: "consts_of A \<subseteq> C"
    and box_absent: "\<box>\<^sub>o A \<notin> S"
  obtains D T where
    "D \<subseteq> UNIV - C"
    and "infinite D"
    and "CEV_supported_world K (C \<union> D) \<Gamma> T"
    and "CEV_Henkin_witnessed_in D \<Gamma> T"
    and "CEV_supported_quotient_arrow C (C \<union> D) \<Gamma> S \<Gamma> T Var"
    and "Neg A \<in> T"
    and "A \<notin> T"
proof -
  have K_C: "K \<subseteq> C"
    and nonempty_C: "C \<noteq> {}"
    and inf_X: "infinite (UNIV - C)"
    and source: "CEV_clean_Henkin_theory \<Gamma> S"
    using world unfolding CEV_supported_world_def by blast+
  obtain D R where
      D_X: "D \<subseteq> UNIV - C"
    and R_X: "R \<subseteq> UNIV - C"
    and inf_D: "infinite D"
    and inf_R: "infinite R"
    and disjoint: "D \<inter> R = {}"
    using inf_X by (rule infinite_split)
  let ?I = "CEV_supported_identity_diagram C \<Gamma> S"
  let ?B = "insert (Neg A) ?I"
  have typed_B: "typed_theory \<Gamma> ?B"
    using A_type CEV_supported_identity_diagram_typed
    unfolding typed_theory_def by auto
  have full_consistent:
      "CEV_consistent \<Gamma>
        (insert (Neg A) (CEV_identity_diagram \<Gamma> S))"
    using source A_type box_absent
    by (rule CEV_identity_separator_consistent)
  have B_full:
      "?B \<subseteq> insert (Neg A) (CEV_identity_diagram \<Gamma> S)"
    using CEV_supported_identity_diagram_subset by blast
  have consistent_B: "CEV_consistent \<Gamma> ?B"
    using full_consistent B_full by (rule CEV_consistent_mono)
  have consts_B_C: "consts_of_set ?B \<subseteq> C"
  proof -
    have neg_consts: "consts_of (Neg A) \<subseteq> C"
      using A_support by simp
    have diagram_consts: "consts_of_set ?I \<subseteq> C"
      by (rule CEV_supported_identity_diagram_consts)
    show ?thesis
      unfolding consts_of_set_insert
      using neg_consts diagram_consts by blast
  qed
  have D_B: "D \<inter> consts_of_set ?B = {}"
    using D_X consts_B_C by blast
  obtain T where
      target: "CEV_clean_Henkin_theory \<Gamma> T"
    and B_T: "?B \<subseteq> T"
    and witnessed_D: "CEV_Henkin_witnessed_in D \<Gamma> T"
    using typed_B consistent_B inf_D D_B
    by (rule CEV_clean_Henkin_extension_from_block)
  have diagram_T: "?I \<subseteq> T"
    using B_T by blast
  have arrow:
      "CEV_supported_quotient_arrow C (C \<union> D)
        \<Gamma> S \<Gamma> T Var"
    using source target _ diagram_T
    by (rule CEV_supported_identity_diagram_subset_gives_arrow) blast
  have R_compl: "R \<subseteq> UNIV - (C \<union> D)"
    using R_X disjoint by blast
  have inf_compl: "infinite (UNIV - (C \<union> D))"
    using R_compl inf_R by (rule infinite_super)
  have K_CD: "K \<subseteq> C \<union> D"
    using K_C by blast
  have nonempty_CD: "C \<union> D \<noteq> {}"
    using nonempty_C by blast
  have D_CD: "D \<subseteq> C \<union> D"
    by blast
  have witnessed_CD: "CEV_Henkin_witnessed_in (C \<union> D) \<Gamma> T"
    using D_CD witnessed_D by (rule CEV_Henkin_witnessed_in_mono)
  have target_world: "CEV_supported_world K (C \<union> D) \<Gamma> T"
    unfolding CEV_supported_world_def
    using K_CD nonempty_CD inf_compl target witnessed_CD by blast
  have neg_in: "Neg A \<in> T"
    using B_T by simp
  have A_absent: "A \<notin> T"
    using target A_type neg_in
    by (rule CEV_clean_Henkin_formula_absent_of_neg_in)
  show ?thesis
    using that[OF D_X inf_D target_world witnessed_D arrow neg_in A_absent] .
qed

text \<open>
  The following result preserves an unequal pair of source classes at a
  target with an enlarged witness language.  Its conclusion is inequality
  of target classes, not disagreement in truth value or in application to
  an argument.  Thus it is not by itself the quasi-Fregean or quasi-functional
  profile separation of Bacon--Dorr Definition 3.11 (pp. 50--51).  In
  particular, the identity arrow already preserves unequal classes; the
  additional content here is the supported witness-language extension.
\<close>

theorem CEV_supported_arrow_separates_unequal_classes:
  assumes world: "CEV_supported_world K C \<Gamma> S"
    and M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and M_support: "CEV_supported_term C M"
    and N_support: "CEV_supported_term C N"
    and unequal: "Eq \<sigma> M N \<notin> S"
  obtains D T where
    "D \<subseteq> UNIV - C"
    and "infinite D"
    and "CEV_supported_world K (C \<union> D) \<Gamma> T"
    and "CEV_supported_quotient_arrow C (C \<union> D) \<Gamma> S \<Gamma> T Var"
    and
      "CEV_supported_map C (C \<union> D) \<Gamma> S \<Gamma> T Var \<sigma>
          (CEV_local_term_class \<Gamma> S \<sigma> M)
        \<noteq>
       CEV_supported_map C (C \<union> D) \<Gamma> S \<Gamma> T Var \<sigma>
          (CEV_local_term_class \<Gamma> S \<sigma> N)"
proof -
  let ?E = "Eq \<sigma> M N"
  have source: "CEV_clean_Henkin_theory \<Gamma> S"
    using world unfolding CEV_supported_world_def by blast
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using M_type N_type by auto
  have E_support: "consts_of ?E \<subseteq> C"
    using M_support N_support
    unfolding CEV_supported_term_def by auto
  have box_absent: "\<box>\<^sub>o ?E \<notin> S"
    using source E_type unequal by (rule CEV_box_absent_of_formula_absent)
  obtain D T where
      D_X: "D \<subseteq> UNIV - C"
    and inf_D: "infinite D"
    and target_world: "CEV_supported_world K (C \<union> D) \<Gamma> T"
    and witnessed_D: "CEV_Henkin_witnessed_in D \<Gamma> T"
    and arrow:
      "CEV_supported_quotient_arrow C (C \<union> D)
        \<Gamma> S \<Gamma> T Var"
    and neg_in: "Neg ?E \<in> T"
    and E_absent: "?E \<notin> T"
    using world E_type E_support box_absent
    by (rule CEV_supported_modal_successor)
  have target: "CEV_clean_Henkin_theory \<Gamma> T"
    using target_world unfolding CEV_supported_world_def by blast
  have classes_neq:
      "CEV_local_term_class \<Gamma> T \<sigma> M
        \<noteq> CEV_local_term_class \<Gamma> T \<sigma> N"
  proof
    assume classes_eq:
      "CEV_local_term_class \<Gamma> T \<sigma> M =
        CEV_local_term_class \<Gamma> T \<sigma> N"
    have equiv: "CEV_local_term_equiv \<Gamma> T \<sigma> M N"
      using CEV_local_term_class_eq[
        OF target M_type N_type] classes_eq by blast
    have "?E \<in> T"
      using equiv unfolding CEV_local_term_equiv_def by blast
    then show False
      using E_absent by contradiction
  qed
  have map_M:
      "CEV_supported_map C (C \<union> D) \<Gamma> S \<Gamma> T Var \<sigma>
          (CEV_local_term_class \<Gamma> S \<sigma> M) =
        CEV_local_term_class \<Gamma> T \<sigma> M"
    using CEV_supported_map_class[OF arrow M_type M_support] by simp
  have map_N:
      "CEV_supported_map C (C \<union> D) \<Gamma> S \<Gamma> T Var \<sigma>
          (CEV_local_term_class \<Gamma> S \<sigma> N) =
        CEV_local_term_class \<Gamma> T \<sigma> N"
    using CEV_supported_map_class[OF arrow N_type N_support] by simp
  have separated:
      "CEV_supported_map C (C \<union> D) \<Gamma> S \<Gamma> T Var \<sigma>
          (CEV_local_term_class \<Gamma> S \<sigma> M)
        \<noteq>
       CEV_supported_map C (C \<union> D) \<Gamma> S \<Gamma> T Var \<sigma>
          (CEV_local_term_class \<Gamma> S \<sigma> N)"
    using map_M map_N classes_neq by simp
  show ?thesis
    using that[OF D_X inf_D target_world arrow separated] .
qed

section \<open>Anti-vacuity for the supported successor\<close>

lemma consts_of_ObjTrue[simp]:
  "consts_of ObjTrue = {}"
  unfolding ObjTrue_def by simp

lemma consts_of_ObjBox[simp]:
  "consts_of (\<box>\<^sub>o A) = consts_of A"
  unfolding ObjBox_def by simp

corollary CEV_supported_modal_successor_applicable:
  assumes B_type: "\<Gamma> \<turnstile> B : Prop"
    and not_proves: "\<not> \<Gamma> \<turnstile>\<^sub>CEV \<box>\<^sub>o B"
  obtains K C S D T where
    "finite K"
    and "K \<noteq> {}"
    and "CEV_supported_world K C \<Gamma> S"
    and "\<box>\<^sub>o B \<notin> S"
    and "D \<subseteq> UNIV - C"
    and "infinite D"
    and "CEV_supported_world K (C \<union> D) \<Gamma> T"
    and
      "CEV_supported_quotient_arrow C (C \<union> D)
        \<Gamma> S \<Gamma> T Var"
    and "Neg B \<in> T"
    and "B \<notin> T"
proof -
  have box_type: "\<Gamma> \<turnstile> \<box>\<^sub>o B : Prop"
    using B_type by (rule typed_ObjBox)
  obtain K C S where
      finite_K: "finite K"
    and nonempty_K: "K \<noteq> {}"
    and support_box: "consts_of (\<box>\<^sub>o B) \<subseteq> K"
    and world: "CEV_supported_world K C \<Gamma> S"
    and neg_box_in: "Neg (\<box>\<^sub>o B) \<in> S"
    and box_absent: "\<box>\<^sub>o B \<notin> S"
    using box_type not_proves by (rule CEV_supported_counterworld)
  have K_C: "K \<subseteq> C"
    using world unfolding CEV_supported_world_def by blast
  have B_support: "consts_of B \<subseteq> C"
    using support_box K_C by simp
  obtain D T where
      D_compl: "D \<subseteq> UNIV - C"
    and inf_D: "infinite D"
    and target_world: "CEV_supported_world K (C \<union> D) \<Gamma> T"
    and witnessed_D: "CEV_Henkin_witnessed_in D \<Gamma> T"
    and arrow:
      "CEV_supported_quotient_arrow C (C \<union> D)
        \<Gamma> S \<Gamma> T Var"
    and neg_in: "Neg B \<in> T"
    and B_absent: "B \<notin> T"
    using world B_type B_support box_absent
    by (rule CEV_supported_modal_successor)
  show ?thesis
    using that[OF finite_K nonempty_K world box_absent D_compl inf_D
      target_world arrow neg_in B_absent] .
qed

end
