theory Bacon_PP_Goodman_T8_Growth
  imports 
    "Goodman_Legacy_T8_Base.Bacon_PP_Goodman_T8_Base_Kinds"
begin

section \<open>Goodman T8c: the finite growth construction\<close>

subsection \<open>Purity of every generated kind property\<close>

lemma pp_T8_base_operator_consts_empty:
  assumes "B \<in> set pp_T8_base_operators"
  shows "consts_of B = {}"
  using assms
  by (auto simp add: pp_T8_base_operators_def
    pp_identity_operator_def gd_box_op_def
    pp_T8_diamond_operator_def gd_true_op_def gd_false_op_def
    ObjTrue_def ObjFalse_def)

lemma consts_of_pp_T8_kind_atom:
  assumes "consts_of B = {}"
  shows "consts_of (pp_T8_kind_atom B) = {pp_pure_name}"
  using assms
  by (simp add: pp_T8_kind_atom_def pp_fun_prime_def
    pp_pure_def pp_Pure_def shift_by_def shift_ren_def)

lemma consts_of_pp_T8_disjoin:
  assumes "\<And>A. A \<in> set As \<Longrightarrow>
    consts_of A \<subseteq> {pp_pure_name}"
  shows "consts_of (pp_T8_disjoin As) \<subseteq> {pp_pure_name}"
  using assms
proof (induction As rule: pp_T8_disjoin.induct)
  case 1
  then show ?case
    by (simp add: ObjFalse_def ObjTrue_def)
next
  case (2 A)
  then show ?case by simp
next
  case (3 A B As)
  then show ?case by simp
qed

lemma consts_of_pp_T8_kind_property:
  assumes Bs: "set Bs \<subseteq> set pp_T8_base_operators"
  shows "consts_of (pp_T8_kind_property Bs)
    \<subseteq> {pp_pure_name}"
proof -
  have atoms:
    "\<And>A. A \<in> set (map pp_T8_kind_atom Bs)
      \<Longrightarrow> consts_of A \<subseteq> {pp_pure_name}"
  proof -
    fix A
    assume "A \<in> set (map pp_T8_kind_atom Bs)"
    then obtain B where
      B: "B \<in> set Bs" "A = pp_T8_kind_atom B"
      by auto
    have "consts_of B = {}"
      using Bs B(1) pp_T8_base_operator_consts_empty by blast
    then show "consts_of A \<subseteq> {pp_pure_name}"
      unfolding B(2)
      using consts_of_pp_T8_kind_atom by blast
  qed
  show ?thesis
  proof -
    have bounded:
      "consts_of
        (pp_T8_disjoin (map pp_T8_kind_atom Bs))
        \<subseteq> {pp_pure_name}"
      by (rule consts_of_pp_T8_disjoin) (use atoms in blast)
    show ?thesis
      unfolding pp_T8_kind_property_def using bounded by simp
  qed
qed

definition pp_T8_purity_builder :: "oterm \<Rightarrow> oterm" where
  "pp_T8_purity_builder M =
    Lam (pp_unary_ty \<rightarrow>\<^sub>o Prop)
      (abstract_const pp_pure_name
        (pp_unary_ty \<rightarrow>\<^sub>o Prop) M)"

definition pp_T8_purity_instance :: "oterm \<Rightarrow> oterm" where
  "pp_T8_purity_instance M =
    App (pp_T8_purity_builder M) (pp_Pure pp_unary_ty)"

lemma typed_pp_T8_purity_builder:
  assumes M_type: "\<Gamma> \<turnstile> M : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_T8_purity_builder M :
    (pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty"
proof -
  have body:
    "(pp_unary_ty \<rightarrow>\<^sub>o Prop) # \<Gamma>
      \<turnstile> abstract_const pp_pure_name
        (pp_unary_ty \<rightarrow>\<^sub>o Prop) M : pp_unary_ty"
    using M_type by (rule abstract_const_preserves_typing)
  show ?thesis
    unfolding pp_T8_purity_builder_def
    using body by (rule has_type.Lam)
qed

lemma typed_pp_T8_purity_instance:
  assumes M_type: "\<Gamma> \<turnstile> M : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_T8_purity_instance M : pp_unary_ty"
  unfolding pp_T8_purity_instance_def
  using typed_pp_T8_purity_builder[OF M_type]
    typed_pp_Pure[of \<Gamma> pp_unary_ty]
  by (rule has_type.App)

lemma pp_T8_purity_builder_constant_free:
  assumes empty:
    "consts_of
      (abstract_const pp_pure_name
        (pp_unary_ty \<rightarrow>\<^sub>o Prop) M) = {}"
  shows "consts_of (pp_T8_purity_builder M) = {}"
  using empty by (simp add: pp_T8_purity_builder_def)

lemma pp_T8_kind_property_abstract_constant_free:
  assumes Bs: "Bs \<in> set pp_T8_nonempty_subsets"
  shows "consts_of
      (abstract_const pp_pure_name
        (pp_unary_ty \<rightarrow>\<^sub>o Prop)
        (pp_T8_kind_property Bs)) = {}"
  using Bs
  by (auto simp add: pp_T8_nonempty_subsets_def
    pp_T8_base_operators_def pp_T8_kind_property_def
    pp_T8_kind_atom_def pp_fun_prime_def pp_pure_def pp_Pure_def
    pp_identity_operator_def gd_box_op_def
    pp_T8_diamond_operator_def gd_true_op_def gd_false_op_def
    abstract_const_def shift_def shift_by_def shift_ren_def
    ObjTrue_def ObjFalse_def)

lemma pp_T8_purity_instance_beta:
  "beta_contract (pp_T8_purity_instance M) M"
proof -
  have step:
    "beta_contract
      (App
        (Lam (pp_unary_ty \<rightarrow>\<^sub>o Prop)
          (abstract_const pp_pure_name
            (pp_unary_ty \<rightarrow>\<^sub>o Prop) M))
        (pp_Pure pp_unary_ty))
      (subst0 (pp_Pure pp_unary_ty)
        (abstract_const pp_pure_name
          (pp_unary_ty \<rightarrow>\<^sub>o Prop) M))"
    by (rule beta_contract.beta)
  have recover:
    "subst0 (pp_Pure pp_unary_ty)
      (abstract_const pp_pure_name
        (pp_unary_ty \<rightarrow>\<^sub>o Prop) M) = M"
    unfolding pp_Pure_def by (rule subst0_abstract_const)
  show ?thesis
    unfolding pp_T8_purity_instance_def
      pp_T8_purity_builder_def
    using step recover by simp
qed

lemma CEV_pp_T8_purity_instance_eq:
  assumes M_type: "\<Gamma> \<turnstile> M : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty (pp_T8_purity_instance M) M"
proof (rule CEV_unary_eq_of_beta_step)
  show "\<Gamma> \<turnstile> pp_T8_purity_instance M : pp_unary_ty"
    using M_type by (rule typed_pp_T8_purity_instance)
  show "\<Gamma> \<turnstile> M : pp_unary_ty"
    by (rule M_type)
  show "compatible_step beta_contract
      (pp_T8_purity_instance M) M"
    using pp_T8_purity_instance_beta
    by (rule compatible_step.root)
qed

lemma pp_T8_purity_builder_axiom:
  assumes M_type: "[] \<turnstile> M : pp_unary_ty"
    and builder_empty:
      "consts_of
        (abstract_const pp_pure_name
          (pp_unary_ty \<rightarrow>\<^sub>o Prop) M) = {}"
  shows "pp_pure
      ((pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty)
      (pp_T8_purity_builder M)
    \<in> pp_T6_core_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
proof (intro UnI1 CollectI exI conjI)
  show "[] \<turnstile> pp_T8_purity_builder M :
      (pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty"
    using M_type by (rule typed_pp_T8_purity_builder)
  show "consts_of (pp_T8_purity_builder M) = {}"
    using builder_empty by (rule pp_T8_purity_builder_constant_free)
  show "pp_pure
      ((pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty)
      (pp_T8_purity_builder M) =
    pp_pure
      ((pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty)
      (pp_T8_purity_builder M)"
    by simp
qed

lemma pp_T8_nonempty_subset_is_base_subset:
  assumes "Bs \<in> set pp_T8_nonempty_subsets"
  shows "set Bs \<subseteq> set pp_T8_base_operators"
proof -
  have member:
    "set Bs \<in> set ` set (subseqs pp_T8_base_operators)"
    using assms unfolding pp_T8_nonempty_subsets_def by auto
  then show ?thesis
    by (simp add: subseqs_powset)
qed

lemma CEVs_pure_pp_T8_kind_property:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and Bs_member: "Bs \<in> set pp_T8_nonempty_subsets"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_unary_ty (pp_T8_kind_property Bs)"
proof -
  let ?M = "pp_T8_kind_property Bs"
  have Bs: "set Bs \<subseteq> set pp_T8_base_operators"
    using Bs_member by (rule pp_T8_nonempty_subset_is_base_subset)
  have M_closed: "[] \<turnstile> ?M : pp_unary_ty"
  proof (rule typed_pp_T8_kind_property)
    fix B \<Delta>
    assume "B \<in> set Bs"
    with Bs have "B \<in> set pp_T8_base_operators" by blast
    then show "\<Delta> \<turnstile> B : pp_unary_ty"
      by (rule typed_pp_T8_base_operators)
  qed
  have M_type: "\<Gamma> \<turnstile> ?M : pp_unary_ty"
  proof (rule typed_pp_T8_kind_property)
    fix B \<Delta>
    assume "B \<in> set Bs"
    with Bs have "B \<in> set pp_T8_base_operators" by blast
    then show "\<Delta> \<turnstile> B : pp_unary_ty"
      by (rule typed_pp_T8_base_operators)
  qed
  have builder_type:
    "\<Gamma> \<turnstile> pp_T8_purity_builder ?M :
      (pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty"
    using M_type by (rule typed_pp_T8_purity_builder)
  have instance_type:
    "\<Gamma> \<turnstile> pp_T8_purity_instance ?M : pp_unary_ty"
    using M_type by (rule typed_pp_T8_purity_instance)
  have builder_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure
        ((pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty)
        (pp_T8_purity_builder ?M)"
  proof (rule CEV_axiom_from.Theorem)
    have ax:
      "pp_pure
        ((pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty)
        (pp_T8_purity_builder ?M)
        \<in> T"
      using pp_T8_purity_builder_axiom[
        OF M_closed
          pp_T8_kind_property_abstract_constant_free[OF Bs_member]]
        core by blast
    show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure
        ((pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty)
        (pp_T8_purity_builder ?M)"
      using ax typed_pp_pure[OF builder_type]
      by (rule CEV_axiom_proves.Axiom)
  qed
  have Pure_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure (pp_unary_ty \<rightarrow>\<^sub>o Prop)
        (pp_Pure pp_unary_ty)"
  proof (rule CEV_axiom_from.Theorem)
    have target_in: "pp_target_PP \<in> T"
      using core pp_T6_target_axiom by blast
    have target_type: "\<Gamma> \<turnstile> pp_target_PP : Prop"
      by (rule infer_type_sound)
        (simp add: pp_target_PP_def pp_purity_of_pure_def
          pp_pure_def pp_Pure_def pp_unary_ty_def lookup_def)
    have target:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_target_PP"
      using target_in target_type
      by (rule CEV_axiom_proves.Axiom)
    show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure (pp_unary_ty \<rightarrow>\<^sub>o Prop)
        (pp_Pure pp_unary_ty)"
      using target
      by (simp add: pp_target_PP_def pp_purity_of_pure_def
        pp_unary_ty_def)
  qed
  have closure: "pp_application_closure
      (pp_unary_ty \<rightarrow>\<^sub>o Prop) pp_unary_ty \<in> T"
    using core pp_T6_application_closure_axiom by blast
  have instance_pure:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty (pp_T8_purity_instance ?M)"
    unfolding pp_T8_purity_instance_def
    using closure builder_type
      typed_pp_Pure[of \<Gamma> pp_unary_ty]
      builder_pure Pure_pure
    by (rule pp_axiom_application_closed_from)
  have eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq pp_unary_ty (pp_T8_purity_instance ?M) ?M"
    using CEV_pp_T8_purity_instance_eq[OF M_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis
    using instance_type M_type instance_pure eq
    by (rule CEV_axiom_from_pure_eq_transport)
qed

lemma CEVs_pure_pp_T8_growth_operator:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and X: "X \<in> set pp_T8_growth_operators"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_pure pp_unary_ty X"
proof -
  obtain Bs where Bs:
      "Bs \<in> set pp_T8_nonempty_subsets"
      "X = pp_T8_kind_property Bs"
    using X unfolding pp_T8_growth_operators_def by auto
  have subset:
    "set Bs \<subseteq> set pp_T8_base_operators"
    using Bs(1) by (rule pp_T8_nonempty_subset_is_base_subset)
  show ?thesis
    unfolding Bs(2)
    using core Bs(1) by (rule CEVs_pure_pp_T8_kind_property)
qed

lemma distinct_pp_T8_base_operators:
  "distinct pp_T8_base_operators"
  by (simp add: pp_T8_base_operators_def
    pp_identity_operator_def gd_box_op_def
    pp_T8_diamond_operator_def gd_true_op_def gd_false_op_def
    ObjTrue_def ObjFalse_def)

lemma distinct_pp_T8_nonempty_subsets:
  "distinct pp_T8_nonempty_subsets"
proof -
  have distinct_sets:
    "distinct
      (map set (subseqs pp_T8_base_operators))"
    using distinct_pp_T8_base_operators
    by (rule distinct_set_subseqs)
  have "distinct (subseqs pp_T8_base_operators)"
    using distinct_sets by (simp add: distinct_map)
  then show ?thesis
    unfolding pp_T8_nonempty_subsets_def by simp
qed

subsection \<open>The generated predicates realize their selected base kinds\<close>

definition pp_T8_kind_atom_at ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_T8_kind_atom_at p B =
    Exists Prop
      (Conj
        (pp_fun_prime (Var 0))
        (Eq Prop
          (shift p)
          (App (shift B) (Var 0))))"

definition pp_T8_disjoin_at ::
    "oterm \<Rightarrow> oterm list \<Rightarrow> oterm" where
  "pp_T8_disjoin_at p Bs =
    pp_T8_disjoin (map (pp_T8_kind_atom_at p) Bs)"

lemma typed_pp_T8_kind_atom_at:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_T8_kind_atom_at p B : Prop"
proof -
  have p_shift: "Prop # \<Gamma> \<turnstile> shift p : Prop"
    using p_type by (rule typed_shift_ctx)
  have B_shift:
    "Prop # \<Gamma> \<turnstile> shift B : pp_unary_ty"
    using B_type by (rule typed_shift_ctx)
  have q_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have Bq_type:
    "Prop # \<Gamma> \<turnstile> App (shift B) (Var 0) : Prop"
    using B_shift q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_T8_kind_atom_at_def
    using typed_pp_fun_prime[OF q_type] p_shift Bq_type
    by (intro has_type.Exists has_type.Conj has_type.Eq)
qed

lemma typed_pp_T8_disjoin_at:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and Bs_type:
      "\<And>B. B \<in> set Bs \<Longrightarrow> \<Gamma> \<turnstile> B : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_T8_disjoin_at p Bs : Prop"
  unfolding pp_T8_disjoin_at_def
proof (rule typed_pp_T8_disjoin)
  fix A
  assume "A \<in> set (map (pp_T8_kind_atom_at p) Bs)"
  then obtain B where
    "B \<in> set Bs" "A = pp_T8_kind_atom_at p B"
    by auto
  then show "\<Gamma> \<turnstile> A : Prop"
    using p_type Bs_type by (auto intro: typed_pp_T8_kind_atom_at)
qed

lemma CEVs_T8_exists_intro:
  assumes body_type: "\<sigma> # \<Gamma> \<turnstile> A : Prop"
    and q_type: "\<Gamma> \<turnstile> q : \<sigma>"
    and d_instance:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s subst0 q A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Exists \<sigma> A"
proof -
  have eg:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (subst0 q A) (Exists \<sigma> A)"
    using body_type q_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.EG)
  show ?thesis
    using d_instance
      CEV_axiom_from.Theorem[
        OF CEV_axiom_proves.Base[OF eg]]
    by (rule CEV_axiom_from.MP)
qed

lemma CEVs_T8_kind_atom_at_intro:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
    and fun_q:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime q"
    and eq:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Eq Prop p (App B q)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_T8_kind_atom_at p B"
proof -
  let ?A =
    "Conj
      (pp_fun_prime (Var 0))
      (Eq Prop
        (shift p)
        (App (shift B) (Var 0)))"
  have body_type: "Prop # \<Gamma> \<turnstile> ?A : Prop"
  proof -
    have ps: "Prop # \<Gamma> \<turnstile> shift p : Prop"
      using p_type by (rule typed_shift_ctx)
    have Bs: "Prop # \<Gamma> \<turnstile> shift B : pp_unary_ty"
      using B_type by (rule typed_shift_ctx)
    have qv: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
    have Bq:
      "Prop # \<Gamma> \<turnstile> App (shift B) (Var 0) : Prop"
      using Bs qv unfolding pp_unary_ty_def by (rule has_type.App)
    show ?thesis
      using typed_pp_fun_prime[OF qv] ps Bq
      by (intro has_type.Conj has_type.Eq)
  qed
  have pair:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj (pp_fun_prime q) (Eq Prop p (App B q))"
    using fun_q eq by (rule CEV_axiom_from_conj_intro)
  have d_instance:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s subst0 q ?A"
    using pair
    by (simp add: subst0_def shift_by_def shift_ren_def
      rename_comp comp_def eval_nat_numeral)
  show ?thesis
    unfolding pp_T8_kind_atom_at_def
    using body_type q_type d_instance by (rule CEVs_T8_exists_intro)
qed

lemma CEVs_T8_disjoin_intro:
  assumes member: "A \<in> set As"
    and types: "\<And>B. B \<in> set As \<Longrightarrow> \<Gamma> \<turnstile> B : Prop"
    and d_A: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_T8_disjoin As"
  using member types
proof (induction As rule: pp_T8_disjoin.induct)
  case 1
  then show ?case by simp
next
  case (2 B)
  then show ?case
    using d_A by simp
next
  case (3 B C Cs)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using "3.prems" by simp
  have tail_type:
    "\<Gamma> \<turnstile> pp_T8_disjoin (C # Cs) : Prop"
    by (rule typed_pp_T8_disjoin)
      (use "3.prems" in auto)
  show ?case
  proof (cases "A = B")
    case True
    have d_B:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s B"
      using d_A unfolding True .
    show ?thesis
      using B_type tail_type d_B
      by (simp add: CEV_axiom_from_disj_left_intro)
  next
    case False
    have member_tail: "A \<in> set (C # Cs)"
      using "3.prems" False by simp
    have types_tail:
      "\<And>D. D \<in> set (C # Cs) \<Longrightarrow> \<Gamma> \<turnstile> D : Prop"
      using "3.prems" by simp
    have d_tail:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        pp_T8_disjoin (C # Cs)"
      using "3.IH"[OF member_tail types_tail] .
    show ?thesis
      using B_type tail_type d_tail
      by (simp add: CEV_axiom_from_disj_right_intro)
  qed
qed

lemma pp_T8_kind_property_beta:
  assumes Bs: "Bs \<in> set pp_T8_nonempty_subsets"
  shows "compatible_step beta_contract
    (App (pp_T8_kind_property Bs) p)
    (pp_T8_disjoin_at p Bs)"
proof (rule compatible_step.root)
  have step:
    "beta_contract
      (App
        (Lam Prop
          (pp_T8_disjoin (map pp_T8_kind_atom Bs)))
        p)
      (subst0 p
        (pp_T8_disjoin (map pp_T8_kind_atom Bs)))"
    by (rule beta_contract.beta)
  show "beta_contract
      (App (pp_T8_kind_property Bs) p)
      (pp_T8_disjoin_at p Bs)"
    using Bs step
    by (auto simp add: pp_T8_nonempty_subsets_def
      pp_T8_base_operators_def pp_T8_kind_property_def
      pp_T8_disjoin_at_def pp_T8_kind_atom_def
      pp_T8_kind_atom_at_def pp_fun_prime_def pp_pure_def pp_Pure_def
      pp_identity_operator_def gd_box_op_def
      pp_T8_diamond_operator_def gd_true_op_def gd_false_op_def
      subst0_def shift_def shift_by_def shift_ren_def
      rename_comp comp_def eval_nat_numeral
      ObjTrue_def ObjFalse_def)
qed

lemma CEVs_T8_selected_kind_property_true:
  assumes Bs_member: "Bs \<in> set pp_T8_nonempty_subsets"
    and B_member: "B \<in> set Bs"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and fun_r:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime r"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    App (pp_T8_kind_property Bs) (App B r)"
proof -
  have subset:
    "set Bs \<subseteq> set pp_T8_base_operators"
    using Bs_member by (rule pp_T8_nonempty_subset_is_base_subset)
  have B_base: "B \<in> set pp_T8_base_operators"
    using subset B_member by blast
  have B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    using B_base by (rule typed_pp_T8_base_operators)
  have Br_type: "\<Gamma> \<turnstile> App B r : Prop"
    using B_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have refl:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App B r) (App B r)"
    using Br_type by (rule CEVs_eq_refl)
  have atom:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T8_kind_atom_at (App B r) B"
    using Br_type B_type r_type fun_r refl
    by (rule CEVs_T8_kind_atom_at_intro)
  have atom_member:
    "pp_T8_kind_atom_at (App B r) B
      \<in> set (map (pp_T8_kind_atom_at (App B r)) Bs)"
    using B_member by simp
  have atom_types:
    "\<And>A. A \<in> set (map (pp_T8_kind_atom_at (App B r)) Bs)
      \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  proof -
    fix A
    assume "A \<in> set
      (map (pp_T8_kind_atom_at (App B r)) Bs)"
    then obtain C where
      C: "C \<in> set Bs"
        "A = pp_T8_kind_atom_at (App B r) C"
      by auto
    have C_base: "C \<in> set pp_T8_base_operators"
      using subset C(1) by blast
    show "\<Gamma> \<turnstile> A : Prop"
      unfolding C(2)
      using Br_type typed_pp_T8_base_operators[OF C_base]
      by (rule typed_pp_T8_kind_atom_at)
  qed
  have disj:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T8_disjoin_at (App B r) Bs"
    unfolding pp_T8_disjoin_at_def
    using atom_member atom_types atom
    by (rule CEVs_T8_disjoin_intro)
  have property_type:
    "\<Gamma> \<turnstile> pp_T8_kind_property Bs : pp_unary_ty"
    using typed_pp_T8_growth_operator[
      of "pp_T8_kind_property Bs" \<Gamma>]
      Bs_member
    unfolding pp_T8_growth_operators_def by auto
  have app_type:
    "\<Gamma> \<turnstile> App (pp_T8_kind_property Bs) (App B r) : Prop"
    using property_type Br_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have disj_type:
    "\<Gamma> \<turnstile> pp_T8_disjoin_at (App B r) Bs : Prop"
    unfolding pp_T8_disjoin_at_def
    using atom_types by (rule typed_pp_T8_disjoin)
  have beta_eq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop
        (App (pp_T8_kind_property Bs) (App B r))
        (pp_T8_disjoin_at (App B r) Bs)"
    using app_type disj_type
      pp_T8_kind_property_beta[OF Bs_member]
    by (rule CEVs_eq_of_beta)
  show ?thesis
    using app_type disj_type beta_eq disj
    by (rule CEVs_T8_eq_truth_left)
qed

subsection \<open>Excluding an omitted base kind\<close>

lemma CEV_T8_excluded_kind_atom_from_collision:
  assumes r_type: "\<Gamma> \<turnstile> r : Prop"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and C_type: "\<Gamma> \<turnstile> C : pp_unary_ty"
    and B_shift[simp]: "shift B = B"
    and C_shift[simp]: "shift C = C"
    and pure_B:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty B"
    and pure_C:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty C"
    and K_type: "Prop # \<Gamma> \<turnstile> K : Prop"
    and collision_rule:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (Conj
            (pp_T8_representation
              (App B (shift r)) B (shift r))
            (pp_T8_representation
              (App B (shift r)) C (Var 0)))
          K"
    and not_same:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (pp_fun_prime (shift r))
          (Neg K)"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg (pp_T8_kind_atom_at (App B r) C))"
proof -
  let ?F = "pp_fun_prime r"
  let ?A =
    "Conj
      (pp_fun_prime (Var 0))
      (Eq Prop
        (shift (App B r))
        (App (shift C) (Var 0)))"
  let ?E = "Exists Prop ?A"
  have B_type': "Prop # \<Gamma> \<turnstile> B : pp_unary_ty"
    using typed_shift_ctx[OF B_type] by simp
  have C_type': "Prop # \<Gamma> \<turnstile> C : pp_unary_ty"
    using typed_shift_ctx[OF C_type] by simp
  have r_type': "Prop # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have q_type': "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have Br_type: "\<Gamma> \<turnstile> App B r : Prop"
    using B_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Br_type':
    "Prop # \<Gamma> \<turnstile> App B (shift r) : Prop"
    using B_type' r_type' unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Cq_type':
    "Prop # \<Gamma> \<turnstile> App C (Var 0) : Prop"
    using C_type' q_type' unfolding pp_unary_ty_def
    by (rule has_type.App)
  have A_type: "Prop # \<Gamma> \<turnstile> ?A : Prop"
    using typed_pp_fun_prime[OF q_type'] Br_type' Cq_type'
    by (simp add: has_type.Conj has_type.Eq)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using A_type by (rule has_type.Exists)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  let ?S = "{?A, shift ?F}"
  have d_A:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?A"
    using A_type by (intro CEV_axiom_from.Assumption) simp
  have d_F:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s shift ?F"
    using typed_shift_ctx[OF F_type]
    by (intro CEV_axiom_from.Assumption) simp
  have d_fun_r:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_fun_prime (shift r)"
    using d_F by simp
  have d_fun_q:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_fun_prime (Var 0)"
    using d_A by (rule CEV_axiom_from_conj_left)
  have d_eq:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App B (shift r)) (App C (Var 0))"
    using d_A by (simp add: CEV_axiom_from_conj_right)
  have d_pure_B:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty B"
    using pure_B by (rule CEV_axiom_from.Theorem)
  have d_pure_C:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty C"
    using pure_C by (rule CEV_axiom_from.Theorem)
  have d_refl:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App B (shift r)) (App B (shift r))"
    using Br_type' by (rule CEVs_eq_refl)
  have rep_B:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T8_representation
        (App B (shift r)) B (shift r)"
    unfolding pp_T8_representation_def
    using d_pure_B d_fun_r d_refl
    by (intro CEV_axiom_from_conj_intro)
  have rep_C:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T8_representation
        (App B (shift r)) C (Var 0)"
    unfolding pp_T8_representation_def
    using d_pure_C d_fun_q d_eq
    by (intro CEV_axiom_from_conj_intro)
  have reps:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Conj
        (pp_T8_representation
          (App B (shift r)) B (shift r))
        (pp_T8_representation
          (App B (shift r)) C (Var 0))"
    using rep_B rep_C by (rule CEV_axiom_from_conj_intro)
  have unique_rule:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (Conj
          (pp_T8_representation
            (App B (shift r)) B (shift r))
          (pp_T8_representation
            (App B (shift r)) C (Var 0)))
        K"
    using collision_rule by (rule CEV_axiom_from.Theorem)
  have d_same:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      K"
    using reps unique_rule by (rule CEV_axiom_from.MP)
  have d_not_same_rule:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (pp_fun_prime (shift r))
        (Neg K)"
    using not_same by (rule CEV_axiom_from.Theorem)
  have d_not_same:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg K"
    using d_fun_r d_not_same_rule by (rule CEV_axiom_from.MP)
  have d_false:
    "Prop # \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_same d_not_same by (rule CEV_axiom_from_contradiction)
  have F_shift_type:
    "Prop # \<Gamma> \<turnstile> shift ?F : Prop"
    using F_type by (rule typed_shift_ctx)
  have A_to_F_false:
    "Prop # \<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp ?A (Imp (shift ?F) ObjFalse)"
  proof -
    have d_false':
      "Prop # \<Gamma> ; T ; insert (shift ?F) {?A}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
      using d_false by (simp add: insert_commute)
    have under_A:
      "Prop # \<Gamma> ; T ; {?A} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp (shift ?F) ObjFalse"
      using F_shift_type d_false'
      by (rule CEV_axiom_from_deduction)
    show ?thesis
      using A_type under_A by (rule CEV_axiom_from_deduction)
  qed
  have bound:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?A (shift (Imp ?F ObjFalse))"
    using A_to_F_false
    by (simp add: CEV_axiom_from_empty_iff)
  have eliminated:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?E (Imp ?F ObjFalse)"
    using A_type has_type.Imp[OF F_type typed_ObjFalse] bound
    by (rule CEV_axiom_proves.Inst)
  have swapped:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (Imp ?E ObjFalse)"
  proof -
    have swap:
      "\<Gamma> \<turnstile>\<^sub>CEV
        Imp
          (Imp ?E (Imp ?F ObjFalse))
          (Imp ?F (Imp ?E ObjFalse))"
    proof (rule CEV_prop_tautology)
      show "prop_tautology \<Gamma>
        (Imp
          (Imp ?E (Imp ?F ObjFalse))
          (Imp ?F (Imp ?E ObjFalse)))"
        using E_type F_type typed_ObjFalse
        by (rule prop_tautology_swap_imp)
    qed
    show ?thesis
      using eliminated CEV_axiom_proves.Base[OF swap]
      by (rule CEV_axiom_proves.MP)
  qed
  have to_neg:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp ?E ObjFalse) (Neg ?E)"
    using CEV_proves_imp_false_to_neg[OF E_type]
    by (intro CEV_axiom_proves.Base)
  have result:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (Neg ?E)"
    using F_type
      has_type.Imp[OF E_type typed_ObjFalse]
      has_type.Neg[OF E_type]
  proof (rule CEV_axiom_imp_trans_plus)
    show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (Imp ?E ObjFalse)"
      by (rule swapped)
    show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Imp ?E ObjFalse) (Neg ?E)"
      by (rule to_neg)
  qed
  show ?thesis
    using result
    by (simp add: pp_T8_kind_atom_at_def)
qed

lemma CEV_T8_excluded_kind_atom:
  assumes L2_in: "pp_L2 \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and C_type: "\<Gamma> \<turnstile> C : pp_unary_ty"
    and B_shift[simp]: "shift B = B"
    and C_shift[simp]: "shift C = C"
    and pure_B:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty B"
    and pure_C:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty C"
    and not_same:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (pp_fun_prime (shift r))
          (Neg (pp_same_kind B C))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg (pp_T8_kind_atom_at (App B r) C))"
proof (rule CEV_T8_excluded_kind_atom_from_collision[
    where K="pp_same_kind B C"])
  show "\<Gamma> \<turnstile> r : Prop" by (rule r_type)
  show "\<Gamma> \<turnstile> B : pp_unary_ty" by (rule B_type)
  show "\<Gamma> \<turnstile> C : pp_unary_ty" by (rule C_type)
  show "shift B = B" by (rule B_shift)
  show "shift C = C" by (rule C_shift)
  show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty B" by (rule pure_B)
  show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty C" by (rule pure_C)
  have B_type': "Prop # \<Gamma> \<turnstile> B : pp_unary_ty"
    using typed_shift_ctx[OF B_type] by simp
  have C_type': "Prop # \<Gamma> \<turnstile> C : pp_unary_ty"
    using typed_shift_ctx[OF C_type] by simp
  have r_type': "Prop # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have q_type': "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have Br_type':
    "Prop # \<Gamma> \<turnstile> App B (shift r) : Prop"
    using B_type' r_type' unfolding pp_unary_ty_def
    by (rule has_type.App)
  show "Prop # \<Gamma> \<turnstile> pp_same_kind B C : Prop"
    using B_type' C_type' by (rule typed_pp_same_kind)
  show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_T8_representation
          (App B (shift r)) B (shift r))
        (pp_T8_representation
          (App B (shift r)) C (Var 0)))
      (pp_same_kind B C)"
    using CEV_Goodman_T8_kind_uniqueness[
      OF L2_in Br_type' B_type' r_type' C_type' q_type'] .
  show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime (shift r))
      (Neg (pp_same_kind B C))"
    by (rule not_same)
qed

lemma CEV_T8_excluded_kind_atom_reverse:
  assumes L2_in: "pp_L2 \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and C_type: "\<Gamma> \<turnstile> C : pp_unary_ty"
    and B_shift[simp]: "shift B = B"
    and C_shift[simp]: "shift C = C"
    and pure_B:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty B"
    and pure_C:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        pp_pure pp_unary_ty C"
    and not_same:
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (pp_fun_prime (shift r))
          (Neg (pp_same_kind C B))"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg (pp_T8_kind_atom_at (App B r) C))"
proof (rule CEV_T8_excluded_kind_atom_from_collision[
    where K="pp_same_kind C B"])
  show "\<Gamma> \<turnstile> r : Prop" by (rule r_type)
  show "\<Gamma> \<turnstile> B : pp_unary_ty" by (rule B_type)
  show "\<Gamma> \<turnstile> C : pp_unary_ty" by (rule C_type)
  show "shift B = B" by (rule B_shift)
  show "shift C = C" by (rule C_shift)
  show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty B" by (rule pure_B)
  show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty C" by (rule pure_C)
  have B_type': "Prop # \<Gamma> \<turnstile> B : pp_unary_ty"
    using typed_shift_ctx[OF B_type] by simp
  have C_type': "Prop # \<Gamma> \<turnstile> C : pp_unary_ty"
    using typed_shift_ctx[OF C_type] by simp
  have r_type': "Prop # \<Gamma> \<turnstile> shift r : Prop"
    using r_type by (rule typed_shift_ctx)
  have q_type': "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have Br_type':
    "Prop # \<Gamma> \<turnstile> App B (shift r) : Prop"
    using B_type' r_type' unfolding pp_unary_ty_def
    by (rule has_type.App)
  let ?RB =
    "pp_T8_representation
      (App B (shift r)) B (shift r)"
  let ?RC =
    "pp_T8_representation
      (App B (shift r)) C (Var 0)"
  have RB_type: "Prop # \<Gamma> \<turnstile> ?RB : Prop"
    using Br_type' B_type' r_type'
    by (rule typed_pp_T8_representation)
  have RC_type: "Prop # \<Gamma> \<turnstile> ?RC : Prop"
    using Br_type' C_type' q_type'
    by (rule typed_pp_T8_representation)
  have reorder:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj ?RB ?RC) (Conj ?RC ?RB)"
  proof (intro CEV_axiom_proves.Base CEV_prop_tautology)
    show "prop_tautology (Prop # \<Gamma>)
      (Imp (Conj ?RB ?RC) (Conj ?RC ?RB))"
      unfolding prop_tautology_def
    proof (intro conjI)
      show "Prop # \<Gamma> \<turnstile>
        Imp (Conj ?RB ?RC) (Conj ?RC ?RB) : Prop"
        using RB_type RC_type
        by (intro has_type.Imp has_type.Conj)
      show "\<forall>v.
        prop_eval v (Imp (Conj ?RB ?RC) (Conj ?RC ?RB))"
        by simp
    qed
  qed
  have reverse_unique:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Conj ?RC ?RB) (pp_same_kind C B)"
    using CEV_Goodman_T8_kind_uniqueness[
      OF L2_in Br_type' C_type' q_type' B_type' r_type'] .
  show "Prop # \<Gamma> \<turnstile> pp_same_kind C B : Prop"
    using C_type' B_type' by (rule typed_pp_same_kind)
  show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (Conj
        (pp_T8_representation
          (App B (shift r)) B (shift r))
        (pp_T8_representation
          (App B (shift r)) C (Var 0)))
      (pp_same_kind C B)"
    using has_type.Conj[OF RB_type RC_type]
      has_type.Conj[OF RC_type RB_type]
      typed_pp_same_kind[OF C_type' B_type']
      reorder reverse_unique
    by (rule CEV_axiom_imp_trans_plus)
  show "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime (shift r))
      (Neg (pp_same_kind C B))"
    by (rule not_same)
qed

lemma shift_pp_T8_base_operator:
  assumes "B \<in> set pp_T8_base_operators"
  shows "shift B = B"
proof -
  have id_shift:
    "shift pp_identity_operator = pp_identity_operator"
    by (simp add: pp_identity_operator_def shift_def)
  show ?thesis
    using assms id_shift
    by (auto simp add: pp_T8_base_operators_def)
qed

lemma CEV_T8_pure_base_operator:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and member: "B \<in> set pp_T8_base_operators"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty B"
proof -
  have local:
    "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty B"
    using member
  proof (auto simp add: pp_T8_base_operators_def)
    show "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty pp_identity_operator"
      using core by (rule pure_Id)
    show "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty gd_box_op"
      using core by (rule pure_Box)
    show "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty pp_T8_diamond_operator"
      using core pp_T8_diamond_operator_purity_axiom
        typed_pp_T8_diamond_operator
      by (rule CEVs_pure_op)
    show "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty gd_true_op"
      using core by (rule pure_Ktop)
    show "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty gd_false_op"
      using core by (rule pure_Kbot)
  qed
  show ?thesis
    using local CEV_axiom_from_empty_iff by simp
qed

lemma CEV_T8_base_not_same_comparable:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and B_member: "B \<in> set pp_T8_base_operators"
    and C_member: "C \<in> set pp_T8_base_operators"
    and distinct: "B \<noteq> C"
  shows
    "(\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (pp_fun_prime r) (Neg (pp_same_kind B C)))
      \<or>
     (\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (pp_fun_prime r) (Neg (pp_same_kind C B)))"
  using B_member C_member distinct
    CEV_Goodman_T8a_Id_Box[OF core r_type]
    CEV_Goodman_T8a_Id_Diamond[OF core r_type]
    CEV_Goodman_T8a_Box_Diamond[OF core r_type]
    CEV_Goodman_T8a_Id_Ktop[OF r_type]
    CEV_Goodman_T8a_Box_Ktop[OF r_type]
    CEV_Goodman_T8a_Diamond_Ktop[OF r_type]
    CEV_Goodman_T8a_Id_Kbot[OF r_type]
    CEV_Goodman_T8a_Box_Kbot[OF r_type]
    CEV_Goodman_T8a_Diamond_Kbot[OF r_type]
    CEV_Goodman_T8a_Ktop_Kbot[OF r_type]
  by (auto simp add: pp_T8_base_operators_def)

lemma CEV_T8_base_excluded_kind_atom:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and L2_in: "pp_L2 \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and B_member: "B \<in> set pp_T8_base_operators"
    and C_member: "C \<in> set pp_T8_base_operators"
    and distinct: "B \<noteq> C"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg (pp_T8_kind_atom_at (App B r) C))"
proof -
  have B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    using B_member by (rule typed_pp_T8_base_operators)
  have C_type: "\<Gamma> \<turnstile> C : pp_unary_ty"
    using C_member by (rule typed_pp_T8_base_operators)
  have B_shift: "shift B = B"
    using B_member by (rule shift_pp_T8_base_operator)
  have C_shift: "shift C = C"
    using C_member by (rule shift_pp_T8_base_operator)
  have pure_B:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty B"
    using core B_member by (rule CEV_T8_pure_base_operator)
  have pure_C:
    "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty C"
    using core C_member by (rule CEV_T8_pure_base_operator)
  consider
    (forward)
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (pp_fun_prime (shift r))
          (Neg (pp_same_kind B C))"
    | (reverse)
      "Prop # \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp
          (pp_fun_prime (shift r))
          (Neg (pp_same_kind C B))"
    using CEV_T8_base_not_same_comparable[
      OF core typed_shift_ctx[OF r_type] B_member C_member distinct]
    by blast
  then show ?thesis
  proof cases
    case forward
    show ?thesis
      using L2_in r_type B_type C_type B_shift C_shift
        pure_B pure_C forward
      by (rule CEV_T8_excluded_kind_atom)
  next
    case reverse
    show ?thesis
      using L2_in r_type B_type C_type B_shift C_shift
        pure_B pure_C reverse
      by (rule CEV_T8_excluded_kind_atom_reverse)
  qed
qed

lemma CEVs_T8_disj_neg_intro:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and not_A:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg A"
    and not_B:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Disj A B)"
proof -
  have taut:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Neg A) (Imp (Neg B) (Neg (Disj A B)))"
  proof (rule CEV_prop_tautology)
    show "prop_tautology \<Gamma>
      (Imp (Neg A) (Imp (Neg B) (Neg (Disj A B))))"
      unfolding prop_tautology_def
    proof (intro conjI)
      show "\<Gamma> \<turnstile>
        Imp (Neg A) (Imp (Neg B) (Neg (Disj A B))) : Prop"
        using A_type B_type
        by (intro has_type.Imp has_type.Neg has_type.Disj)
      show "\<forall>v.
        prop_eval v
          (Imp (Neg A) (Imp (Neg B) (Neg (Disj A B))))"
        by simp
    qed
  qed
  have rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Neg A) (Imp (Neg B) (Neg (Disj A B)))"
    using taut
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have step:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Neg B) (Neg (Disj A B))"
    using not_A rule by (rule CEV_axiom_from.MP)
  show ?thesis
    using not_B step by (rule CEV_axiom_from.MP)
qed

lemma CEVs_T8_disjoin_neg:
  assumes types:
      "\<And>A. A \<in> set As \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
    and negs:
      "\<And>A. A \<in> set As \<Longrightarrow>
        \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Neg (pp_T8_disjoin As)"
  using types negs
proof (induction As rule: pp_T8_disjoin.induct)
  case 1
  then show ?case
    using CEVs_not_ObjFalse by simp
next
  case (2 A)
  then show ?case by simp
next
  case (3 A B As)
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using "3.prems" by simp
  have tail_type:
    "\<Gamma> \<turnstile> pp_T8_disjoin (B # As) : Prop"
    by (rule typed_pp_T8_disjoin)
      (use "3.prems" in auto)
  have not_A:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg A"
    using "3.prems" by simp
  have not_tail:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (pp_T8_disjoin (B # As))"
    using "3.IH" "3.prems" by auto
  show ?case
    using A_type tail_type not_A not_tail
    by (simp add: CEVs_T8_disj_neg_intro)
qed

lemma CEV_Goodman_T8_omitted_kind_property_false:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and L2_in: "pp_L2 \<in> T"
    and Cs_member: "Cs \<in> set pp_T8_nonempty_subsets"
    and B_base: "B \<in> set pp_T8_base_operators"
    and B_omitted: "B \<notin> set Cs"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg
        (App (pp_T8_kind_property Cs) (App B r)))"
proof -
  let ?F = "pp_fun_prime r"
  let ?S = "{?F}"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have d_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have Cs_subset:
    "set Cs \<subseteq> set pp_T8_base_operators"
    using Cs_member by (rule pp_T8_nonempty_subset_is_base_subset)
  have B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    using B_base by (rule typed_pp_T8_base_operators)
  have Br_type: "\<Gamma> \<turnstile> App B r : Prop"
    using B_type r_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have atom_types:
    "\<And>A. A \<in> set
        (map (pp_T8_kind_atom_at (App B r)) Cs)
      \<Longrightarrow> \<Gamma> \<turnstile> A : Prop"
  proof -
    fix A
    assume "A \<in> set
      (map (pp_T8_kind_atom_at (App B r)) Cs)"
    then obtain C where C:
      "C \<in> set Cs"
      "A = pp_T8_kind_atom_at (App B r) C"
      by auto
    have C_base: "C \<in> set pp_T8_base_operators"
      using Cs_subset C(1) by blast
    show "\<Gamma> \<turnstile> A : Prop"
      unfolding C(2)
      using Br_type typed_pp_T8_base_operators[OF C_base]
      by (rule typed_pp_T8_kind_atom_at)
  qed
  have atom_negs:
    "\<And>A. A \<in> set
        (map (pp_T8_kind_atom_at (App B r)) Cs)
      \<Longrightarrow>
        \<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg A"
  proof -
    fix A
    assume "A \<in> set
      (map (pp_T8_kind_atom_at (App B r)) Cs)"
    then obtain C where C:
      "C \<in> set Cs"
      "A = pp_T8_kind_atom_at (App B r) C"
      by auto
    have C_base: "C \<in> set pp_T8_base_operators"
      using Cs_subset C(1) by blast
    have BC: "B \<noteq> C"
      using B_omitted C(1) by blast
    have rule:
      "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp
          ?F
          (Neg (pp_T8_kind_atom_at (App B r) C))"
      using CEV_T8_base_excluded_kind_atom[
        OF core L2_in r_type B_base C_base BC]
      by (rule CEV_axiom_from.Theorem)
    show "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg A"
      unfolding C(2)
      using d_F rule by (rule CEV_axiom_from.MP)
  qed
  have not_disj:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (pp_T8_disjoin_at (App B r) Cs)"
    unfolding pp_T8_disjoin_at_def
    using atom_types atom_negs by (rule CEVs_T8_disjoin_neg)
  have property_type:
    "\<Gamma> \<turnstile> pp_T8_kind_property Cs : pp_unary_ty"
    using typed_pp_T8_growth_operator[
      of "pp_T8_kind_property Cs" \<Gamma>]
      Cs_member
    unfolding pp_T8_growth_operators_def by auto
  have disj_type:
    "\<Gamma> \<turnstile> pp_T8_disjoin_at (App B r) Cs : Prop"
    unfolding pp_T8_disjoin_at_def
    using atom_types by (rule typed_pp_T8_disjoin)
  have not_property:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (App (pp_T8_kind_property Cs) (App B r))"
    using property_type Br_type disj_type
      pp_T8_kind_property_beta[OF Cs_member] not_disj
    by (rule CEVs_app_false)
  show ?thesis
    using F_type not_property
    by (rule CEV_axiom_from_singleton_imp)
qed

lemma pp_T8_nonempty_subsets_set_injective:
  assumes Bs_member: "Bs \<in> set pp_T8_nonempty_subsets"
    and Cs_member: "Cs \<in> set pp_T8_nonempty_subsets"
    and same_set: "set Bs = set Cs"
  shows "Bs = Cs"
proof -
  have Bs_subseq:
    "Bs \<in> set (subseqs pp_T8_base_operators)"
    using Bs_member
    unfolding pp_T8_nonempty_subsets_def by auto
  have Cs_subseq:
    "Cs \<in> set (subseqs pp_T8_base_operators)"
    using Cs_member
    unfolding pp_T8_nonempty_subsets_def by auto
  have distinct_sets:
    "distinct
      (map set (subseqs pp_T8_base_operators))"
    using distinct_pp_T8_base_operators
    by (rule distinct_set_subseqs)
  then have injective:
    "inj_on set (set (subseqs pp_T8_base_operators))"
    unfolding distinct_map by blast
  show ?thesis
    using injective Bs_subseq Cs_subseq same_set
    unfolding inj_on_def by blast
qed

lemma CEV_Goodman_T8_growth_operator_distinct:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and L2_in: "pp_L2 \<in> T"
    and Bs_member: "Bs \<in> set pp_T8_nonempty_subsets"
    and Cs_member: "Cs \<in> set pp_T8_nonempty_subsets"
    and distinct: "Bs \<noteq> Cs"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp
      (pp_fun_prime r)
      (Neg
        (Eq pp_unary_ty
          (pp_T8_kind_property Bs)
          (pp_T8_kind_property Cs)))"
proof -
  let ?F = "pp_fun_prime r"
  let ?PB = "pp_T8_kind_property Bs"
  let ?PC = "pp_T8_kind_property Cs"
  let ?S = "{?F}"
  have sets_distinct: "set Bs \<noteq> set Cs"
    using distinct pp_T8_nonempty_subsets_set_injective[
      OF Bs_member Cs_member] by blast
  then obtain B where split:
      "(B \<in> set Bs \<and> B \<notin> set Cs)
        \<or> (B \<in> set Cs \<and> B \<notin> set Bs)"
    by blast
  have Bs_subset:
    "set Bs \<subseteq> set pp_T8_base_operators"
    using Bs_member by (rule pp_T8_nonempty_subset_is_base_subset)
  have Cs_subset:
    "set Cs \<subseteq> set pp_T8_base_operators"
    using Cs_member by (rule pp_T8_nonempty_subset_is_base_subset)
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have d_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have PB_type: "\<Gamma> \<turnstile> ?PB : pp_unary_ty"
    using typed_pp_T8_growth_operator[
      of ?PB \<Gamma>] Bs_member
    unfolding pp_T8_growth_operators_def by auto
  have PC_type: "\<Gamma> \<turnstile> ?PC : pp_unary_ty"
    using typed_pp_T8_growth_operator[
      of ?PC \<Gamma>] Cs_member
    unfolding pp_T8_growth_operators_def by auto
  have neq:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq pp_unary_ty ?PB ?PC)"
  proof (rule disjE[OF split])
    assume left:
      "B \<in> set Bs \<and> B \<notin> set Cs"
    have B_base: "B \<in> set pp_T8_base_operators"
      using Bs_subset left by blast
    have B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
      using B_base by (rule typed_pp_T8_base_operators)
    have Br_type: "\<Gamma> \<turnstile> App B r : Prop"
      using B_type r_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have true_B:
      "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        App ?PB (App B r)"
      using Bs_member conjunct1[OF left] r_type d_F
      by (rule CEVs_T8_selected_kind_property_true)
    have false_rule:
      "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?F (Neg (App ?PC (App B r)))"
      using CEV_Goodman_T8_omitted_kind_property_false[
        OF core L2_in Cs_member B_base _ r_type]
        left by (intro CEV_axiom_from.Theorem) auto
    have false_C:
      "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App ?PC (App B r))"
      using d_F false_rule by (rule CEV_axiom_from.MP)
    show ?thesis
      using PB_type PC_type Br_type true_B false_C
      by (rule CEVs_operator_neq_via_witness)
  next
    assume right:
      "B \<in> set Cs \<and> B \<notin> set Bs"
    have B_base: "B \<in> set pp_T8_base_operators"
      using Cs_subset right by blast
    have B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
      using B_base by (rule typed_pp_T8_base_operators)
    have Br_type: "\<Gamma> \<turnstile> App B r : Prop"
      using B_type r_type unfolding pp_unary_ty_def
      by (rule has_type.App)
    have true_C:
      "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        App ?PC (App B r)"
      using Cs_member conjunct1[OF right] r_type d_F
      by (rule CEVs_T8_selected_kind_property_true)
    have false_rule:
      "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Imp ?F (Neg (App ?PB (App B r)))"
      using CEV_Goodman_T8_omitted_kind_property_false[
        OF core L2_in Bs_member B_base _ r_type]
        right by (intro CEV_axiom_from.Theorem) auto
    have false_B:
      "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (App ?PB (App B r))"
      using d_F false_rule by (rule CEV_axiom_from.MP)
    have reverse_neq:
      "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
        Neg (Eq pp_unary_ty ?PC ?PB)"
      using PC_type PB_type Br_type true_C false_B
      by (rule CEVs_operator_neq_via_witness)
    show ?thesis
      using PC_type PB_type reverse_neq by (rule CEVs_neq_sym)
  qed
  show ?thesis
    using F_type neq by (rule CEV_axiom_from_singleton_imp)
qed

fun pp_T8_flatten_disjoin :: "oterm \<Rightarrow> oterm list" where
  "pp_T8_flatten_disjoin (Disj A B) =
    A # pp_T8_flatten_disjoin B"
| "pp_T8_flatten_disjoin A = [A]"

lemma pp_T8_flatten_disjoin_kind_atoms:
  assumes "Bs \<noteq> []"
  shows
    "pp_T8_flatten_disjoin
      (pp_T8_disjoin (map pp_T8_kind_atom Bs)) =
      map pp_T8_kind_atom Bs"
  using assms
proof (induction Bs rule: pp_T8_disjoin.induct)
  case 1
  then show ?case by simp
next
  case (2 A)
  then show ?case
    by (simp add: pp_T8_kind_atom_def)
next
  case (3 A B As)
  then show ?case by simp
qed

lemma inj_pp_T8_kind_atom:
  "inj pp_T8_kind_atom"
  unfolding pp_T8_kind_atom_def
  by (rule injI) simp

lemma pp_T8_kind_property_injective_nonempty:
  assumes Bs_nonempty: "Bs \<noteq> []"
    and Cs_nonempty: "Cs \<noteq> []"
    and same: "pp_T8_kind_property Bs =
      pp_T8_kind_property Cs"
  shows "Bs = Cs"
proof -
  have body_same:
    "pp_T8_disjoin (map pp_T8_kind_atom Bs) =
      pp_T8_disjoin (map pp_T8_kind_atom Cs)"
    using same unfolding pp_T8_kind_property_def by simp
  have atoms_same:
    "map pp_T8_kind_atom Bs =
      map pp_T8_kind_atom Cs"
    using arg_cong[
        where f=pp_T8_flatten_disjoin,
        OF body_same]
      pp_T8_flatten_disjoin_kind_atoms[OF Bs_nonempty]
      pp_T8_flatten_disjoin_kind_atoms[OF Cs_nonempty]
    by simp
  show ?thesis
    using atoms_same inj_pp_T8_kind_atom by simp
qed

lemma distinct_pp_T8_growth_operators:
  "distinct pp_T8_growth_operators"
proof -
  have injective:
    "inj_on pp_T8_kind_property
      (set pp_T8_nonempty_subsets)"
  proof (rule inj_onI)
    fix Bs Cs
    assume Bs_member:
      "Bs \<in> set pp_T8_nonempty_subsets"
      and Cs_member:
      "Cs \<in> set pp_T8_nonempty_subsets"
      and same:
      "pp_T8_kind_property Bs =
        pp_T8_kind_property Cs"
    have Bs_nonempty: "Bs \<noteq> []"
      using Bs_member
      unfolding pp_T8_nonempty_subsets_def by auto
    have Cs_nonempty: "Cs \<noteq> []"
      using Cs_member
      unfolding pp_T8_nonempty_subsets_def by auto
    show "Bs = Cs"
      using Bs_nonempty Cs_nonempty same
      by (rule pp_T8_kind_property_injective_nonempty)
  qed
  show ?thesis
    unfolding pp_T8_growth_operators_def distinct_map
    using distinct_pp_T8_nonempty_subsets injective by blast
qed

lemma CEVs_T8_neq_all_intro:
  assumes A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    and Bs_type:
      "\<And>B. B \<in> set Bs \<Longrightarrow> \<Gamma> \<turnstile> B : \<sigma>"
    and neqs:
      "\<And>B. B \<in> set Bs \<Longrightarrow>
        \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq \<sigma> A B)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_T8_neq_all \<sigma> A Bs"
  using Bs_type neqs
proof (induction Bs)
  case Nil
  then show ?case
    using CEVs_ObjTrue by simp
next
  case (Cons B Bs)
  have head:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq \<sigma> A B)"
    using Cons.prems by simp
  have tail:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T8_neq_all \<sigma> A Bs"
    using Cons.IH Cons.prems by simp
  show ?case
    using head tail
    by (simp add: CEV_axiom_from_conj_intro)
qed

lemma CEVs_T8_pairwise_distinct_intro:
  assumes distinct: "distinct As"
    and types:
      "\<And>A. A \<in> set As \<Longrightarrow> \<Gamma> \<turnstile> A : \<sigma>"
    and neqs:
      "\<And>A B. A \<in> set As \<Longrightarrow> B \<in> set As
        \<Longrightarrow> A \<noteq> B
        \<Longrightarrow>
        \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq \<sigma> A B)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_T8_pairwise_distinct \<sigma> As"
  using distinct types neqs
proof (induction As)
  case Nil
  then show ?case
    using CEVs_ObjTrue by simp
next
  case (Cons A As)
  have A_type: "\<Gamma> \<turnstile> A : \<sigma>"
    using Cons.prems by simp
  have A_notin: "A \<notin> set As"
    using Cons.prems by simp
  have As_type:
    "\<And>B. B \<in> set As \<Longrightarrow> \<Gamma> \<turnstile> B : \<sigma>"
    using Cons.prems by simp
  have head:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T8_neq_all \<sigma> A As"
  proof (rule CEVs_T8_neq_all_intro[OF A_type As_type])
    fix B
    assume B: "B \<in> set As"
    have "A \<noteq> B"
      using A_notin B by blast
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq \<sigma> A B)"
      using Cons.prems B \<open>A \<noteq> B\<close> by simp
  qed
  have tail:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T8_pairwise_distinct \<sigma> As"
  proof (rule Cons.IH)
    show "distinct As"
      using Cons.prems by simp
    show "\<And>B. B \<in> set As \<Longrightarrow> \<Gamma> \<turnstile> B : \<sigma>"
      by (rule As_type)
    show "\<And>B C. B \<in> set As \<Longrightarrow> C \<in> set As
      \<Longrightarrow> B \<noteq> C
      \<Longrightarrow>
      \<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq \<sigma> B C)"
      using Cons.prems by simp
  qed
  show ?case
    using head tail
    by (simp add: CEV_axiom_from_conj_intro)
qed

lemma CEVs_Goodman_T8_growth_operators_pairwise:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and L2_in: "pp_L2 \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and d_F:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime r"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_T8_pairwise_distinct pp_unary_ty pp_T8_growth_operators"
proof (rule CEVs_T8_pairwise_distinct_intro)
  show "distinct pp_T8_growth_operators"
    by (rule distinct_pp_T8_growth_operators)
  show "\<And>X. X \<in> set pp_T8_growth_operators
    \<Longrightarrow> \<Gamma> \<turnstile> X : pp_unary_ty"
    by (rule typed_pp_T8_growth_operator)
  fix X Y
  assume X: "X \<in> set pp_T8_growth_operators"
    and Y: "Y \<in> set pp_T8_growth_operators"
    and XY: "X \<noteq> Y"
  obtain Bs Cs where BC:
      "Bs \<in> set pp_T8_nonempty_subsets"
      "X = pp_T8_kind_property Bs"
      "Cs \<in> set pp_T8_nonempty_subsets"
      "Y = pp_T8_kind_property Cs"
    using X Y unfolding pp_T8_growth_operators_def by auto
  have BsCs: "Bs \<noteq> Cs"
    using XY BC by blast
  have rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (pp_fun_prime r)
        (Neg
          (Eq pp_unary_ty
            (pp_T8_kind_property Bs)
            (pp_T8_kind_property Cs)))"
    using CEV_Goodman_T8_growth_operator_distinct[
      OF core L2_in BC(1) BC(3) BsCs r_type]
    by (rule CEV_axiom_from.Theorem)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Neg (Eq pp_unary_ty X Y)"
    unfolding BC(2,4)
    using d_F rule by (rule CEV_axiom_from.MP)
qed

lemma distinct_pp_T8_growth_values:
  "distinct
    (map (\<lambda>X. App X r) pp_T8_growth_operators)"
  using distinct_pp_T8_growth_operators
  unfolding distinct_map inj_on_def by auto

lemma CEVs_Goodman_T8_growth_values_pairwise:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and L2_in: "pp_L2 \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and d_F:
      "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime r"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    pp_T8_pairwise_distinct Prop
      (map (\<lambda>X. App X r) pp_T8_growth_operators)"
proof (rule CEVs_T8_pairwise_distinct_intro)
  show "distinct
    (map (\<lambda>X. App X r) pp_T8_growth_operators)"
    by (rule distinct_pp_T8_growth_values)
  show "\<And>P. P \<in> set
      (map (\<lambda>X. App X r) pp_T8_growth_operators)
    \<Longrightarrow> \<Gamma> \<turnstile> P : Prop"
  proof -
    fix P
    assume "P \<in> set
      (map (\<lambda>X. App X r) pp_T8_growth_operators)"
    then obtain X where X:
      "X \<in> set pp_T8_growth_operators"
      "P = App X r"
      by auto
    show "\<Gamma> \<turnstile> P : Prop"
      unfolding X(2)
      using typed_pp_T8_growth_operator[OF X(1)] r_type
      unfolding pp_unary_ty_def by (rule has_type.App)
  qed
  fix P Q
  assume P:
      "P \<in> set
        (map (\<lambda>X. App X r) pp_T8_growth_operators)"
    and Q:
      "Q \<in> set
        (map (\<lambda>X. App X r) pp_T8_growth_operators)"
    and PQ: "P \<noteq> Q"
  obtain X Y where XY:
      "X \<in> set pp_T8_growth_operators"
      "P = App X r"
      "Y \<in> set pp_T8_growth_operators"
      "Q = App Y r"
    using P Q by auto
  have X_neq_Y: "X \<noteq> Y"
    using PQ XY by blast
  obtain Bs Cs where BC:
      "Bs \<in> set pp_T8_nonempty_subsets"
      "X = pp_T8_kind_property Bs"
      "Cs \<in> set pp_T8_nonempty_subsets"
      "Y = pp_T8_kind_property Cs"
    using XY unfolding pp_T8_growth_operators_def by auto
  have Bs_neq_Cs: "Bs \<noteq> Cs"
    using X_neq_Y BC by blast
  have X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    using XY(1) by (rule typed_pp_T8_growth_operator)
  have Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    using XY(3) by (rule typed_pp_T8_growth_operator)
  have pure_X:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty X"
    using core XY(1) by (rule CEVs_pure_pp_T8_growth_operator)
  have pure_Y:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_pure pp_unary_ty Y"
    using core XY(3) by (rule CEVs_pure_pp_T8_growth_operator)
  have op_rule:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp
        (pp_fun_prime r)
        (Neg (Eq pp_unary_ty X Y))"
    using CEV_Goodman_T8_growth_operator_distinct[
      OF core L2_in BC(1) BC(3) Bs_neq_Cs r_type]
    unfolding BC(2,4)
    by (rule CEV_axiom_from.Theorem)
  have op_neq:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq pp_unary_ty X Y)"
    using d_F op_rule by (rule CEV_axiom_from.MP)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Neg (Eq Prop P Q)"
    unfolding XY(2,4)
    using r_type X_type Y_type pure_X pure_Y op_neq d_F
    by (rule CEVs_fun_prime_separates)
qed

theorem CEV_Goodman_T8c:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and L2_in: "pp_L2 \<in> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (pp_T8_growth_claim r)"
proof -
  let ?F = "pp_fun_prime r"
  let ?S = "{?F}"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have d_F:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have operators:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T8_pairwise_distinct pp_unary_ty
        pp_T8_growth_operators"
    using core L2_in r_type d_F
    by (rule CEVs_Goodman_T8_growth_operators_pairwise)
  have d_values:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T8_pairwise_distinct Prop
        (map (\<lambda>X. App X r) pp_T8_growth_operators)"
    using core L2_in r_type d_F
    by (rule CEVs_Goodman_T8_growth_values_pairwise)
  have claim:
    "\<Gamma> ; T ; ?S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      pp_T8_growth_claim r"
    unfolding pp_T8_growth_claim_def
    using operators d_values by (rule CEV_axiom_from_conj_intro)
  show ?thesis
    using F_type claim by (rule CEV_axiom_from_singleton_imp)
qed

subsection \<open>The closed existential T8c theorem\<close>

definition pp_T8_axioms :: "oterm set" where
  "pp_T8_axioms = insert pp_L2 pp_T6_core_PP_axioms"

definition pp_T8_full_axioms :: "oterm set" where
  "pp_T8_full_axioms =
    insert pp_exists_fun_prime pp_T8_axioms"

definition pp_T8_growth_result :: oterm where
  "pp_T8_growth_result =
    Exists Prop
      (Conj
        (pp_fun_prime (Var 0))
        (pp_T8_growth_claim (Var 0)))"

lemma typed_pp_T8_growth_result:
  "[] \<turnstile> pp_T8_growth_result : Prop"
proof -
  have r_type: "[Prop] \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have F_type:
    "[Prop] \<turnstile> pp_fun_prime (Var 0) : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have claim_type:
    "[Prop] \<turnstile> pp_T8_growth_claim (Var 0) : Prop"
    using r_type by (rule typed_pp_T8_growth_claim)
  show ?thesis
    unfolding pp_T8_growth_result_def
    using F_type claim_type
    by (intro has_type.Exists has_type.Conj)
qed

theorem CEV_Goodman_T8c_closed:
  "[] ; pp_T8_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_T8_growth_result"
proof -
  let ?F = "pp_fun_prime (Var 0)"
  let ?C = "pp_T8_growth_claim (Var 0)"
  let ?B = "Conj ?F ?C"
  have r_type: "[Prop] \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have F_type: "[Prop] \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have C_type: "[Prop] \<turnstile> ?C : Prop"
    using r_type by (rule typed_pp_T8_growth_claim)
  have B_type: "[Prop] \<turnstile> ?B : Prop"
    using F_type C_type by (rule has_type.Conj)
  have core:
    "pp_T6_core_PP_axioms \<subseteq> pp_T8_full_axioms"
    unfolding pp_T8_full_axioms_def pp_T8_axioms_def by blast
  have L2_in: "pp_L2 \<in> pp_T8_full_axioms"
    unfolding pp_T8_full_axioms_def pp_T8_axioms_def by blast
  have conditional:
    "[Prop] ; pp_T8_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F ?C"
    using core L2_in r_type by (rule CEV_Goodman_T8c)
  have under_F:
    "[Prop] ; pp_T8_full_axioms ; {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?B"
  proof -
    have d_F:
      "[Prop] ; pp_T8_full_axioms ; {?F}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
      using F_type by (intro CEV_axiom_from.Assumption) simp
    have d_conditional:
      "[Prop] ; pp_T8_full_axioms ; {?F}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?F ?C"
      using conditional by (rule CEV_axiom_from.Theorem)
    have d_C:
      "[Prop] ; pp_T8_full_axioms ; {?F}
        \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?C"
      using d_F d_conditional by (rule CEV_axiom_from.MP)
    show ?thesis
      using d_F d_C by (rule CEV_axiom_from_conj_intro)
  qed
  have witness:
    "[Prop] ; pp_T8_full_axioms ; {?F}
      \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s shift pp_T8_growth_result"
    using CEV_axiom_from_exists_intro_var0[
      OF B_type under_F]
    unfolding pp_T8_growth_result_def .
  have witness_rule:
    "[Prop] ; pp_T8_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp ?F (shift pp_T8_growth_result)"
    using F_type witness by (rule CEV_axiom_from_singleton_imp)
  have exists_rule:
    "[] ; pp_T8_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp pp_exists_fun_prime pp_T8_growth_result"
  proof -
    have raw:
      "[] ; pp_T8_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Exists Prop ?F) pp_T8_growth_result"
    proof (rule CEV_axiom_proves.Inst)
      show "[Prop] \<turnstile> ?F : Prop" by (rule F_type)
      show "[] \<turnstile> pp_T8_growth_result : Prop"
        by (rule typed_pp_T8_growth_result)
      show "[Prop] ; pp_T8_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?F (shift pp_T8_growth_result)"
        by (rule witness_rule)
    qed
    show ?thesis
      using raw unfolding pp_exists_fun_prime_def .
  qed
  have exists_fun:
    "[] ; pp_T8_full_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_exists_fun_prime"
  proof (rule CEV_axiom_proves.Axiom)
    show "pp_exists_fun_prime \<in> pp_T8_full_axioms"
      unfolding pp_T8_full_axioms_def by blast
    show "[] \<turnstile> pp_exists_fun_prime : Prop"
      by (rule typed_pp_exists_fun_prime)
  qed
  show ?thesis
    using exists_fun exists_rule by (rule CEV_axiom_proves.MP)
qed

corollary CEV_Goodman_T8c_closed_mono:
  assumes "pp_T8_full_axioms \<subseteq> T"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sup>+
    pp_T8_growth_result"
  using CEV_Goodman_T8c_closed assms
  by (rule CEV_axiom_proves_mono)

end
