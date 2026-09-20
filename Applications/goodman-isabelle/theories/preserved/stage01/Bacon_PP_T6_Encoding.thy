theory Bacon_PP_T6_Encoding
  imports 
    "Goodman_Legacy_01.Bacon_PP_Modalized_Functionality_Derived"
begin

section \<open>Proposed object-language encoding of Goodman's T6 route\<close>

text \<open>
  This theory fixes the syntax of the first T6 target before proof search.
  It encodes Goodman's proposition-level \<open>fun\<acute>\<close>, the group \<open>G\<close> of pure
  reversible operators, sameness of kind, L2, Inv, and the liar operator
  \<open>D\<close>.  At this stage the claims are definitions plus typing certificates;
  no inconsistency theorem is asserted.
\<close>

subsection \<open>Evaluation-injectivity: \<open>fun\<acute>\<close>\<close>

definition pp_fun_prime :: "oterm \<Rightarrow> oterm" where
  "pp_fun_prime p =
    Forall pp_unary_ty
      (Forall pp_unary_ty
        (Imp
          (Conj
            (pp_pure pp_unary_ty (Var 1))
            (pp_pure pp_unary_ty (Var 0)))
          (Imp
            (Eq Prop
              (App (Var 1) (shift_by 2 p))
              (App (Var 0) (shift_by 2 p)))
            (Eq pp_unary_ty (Var 1) (Var 0)))))"

text \<open>
  In \<open>pp_fun_prime p\<close>, the two bound variables are pure unary operators.
  The free proposition \<open>p\<close> is shifted past both binders.  Thus this says that
  evaluation at \<open>p\<close> is injective on pure unary operators.
\<close>

lemma typed_pp_fun_prime:
  assumes "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile> pp_fun_prime p : Prop"
proof -
  let ?op = "pp_unary_ty"
  have p_shift:
      "?op # ?op # \<Gamma> \<turnstile> shift_by 2 p : Prop"
  proof -
    have "[?op, ?op] @ \<Gamma> \<turnstile>
        shift_by (length [?op, ?op]) p : Prop"
      using assms by (rule shift_by_preserves_typing)
    then show ?thesis by (simp add: numeral_2_eq_2)
  qed
  have X_type: "?op # ?op # \<Gamma> \<turnstile> Var 1 : ?op"
    by (rule has_type.Var) (simp add: lookup_def)
  have Y_type: "?op # ?op # \<Gamma> \<turnstile> Var 0 : ?op"
    by (rule has_type.Var) (simp add: lookup_def)
  have Xp_type:
      "?op # ?op # \<Gamma> \<turnstile> App (Var 1) (shift_by 2 p) : Prop"
    using X_type p_shift unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Yp_type:
      "?op # ?op # \<Gamma> \<turnstile> App (Var 0) (shift_by 2 p) : Prop"
    using Y_type p_shift unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_fun_prime_def
    using typed_pp_pure[OF X_type] typed_pp_pure[OF Y_type]
      Xp_type Yp_type X_type Y_type
    by (intro has_type.Forall has_type.Imp has_type.Conj has_type.Eq)
qed

definition pp_exists_fun_prime :: oterm where
  "pp_exists_fun_prime = Exists Prop (pp_fun_prime (Var 0))"

lemma typed_pp_exists_fun_prime:
  "[] \<turnstile> pp_exists_fun_prime : Prop"
  unfolding pp_exists_fun_prime_def
  using typed_pp_fun_prime[of "[Prop]" "Var 0"]
  by (intro has_type.Exists has_type.Var) (simp add: lookup_def)

subsection \<open>Pure reversible operators and kinds\<close>

definition pp_compose :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_compose F G =
    Lam Prop
      (App (shift F) (App (shift G) (Var 0)))"

lemma typed_pp_compose:
  assumes F: "\<Gamma> \<turnstile> F : pp_unary_ty"
    and G: "\<Gamma> \<turnstile> G : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_compose F G : pp_unary_ty"
proof -
  have F_shift: "Prop # \<Gamma> \<turnstile> shift F : pp_unary_ty"
    using F by (rule typed_shift_ctx)
  have G_shift: "Prop # \<Gamma> \<turnstile> shift G : pp_unary_ty"
    using G by (rule typed_shift_ctx)
  have x_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have Gx_type: "Prop # \<Gamma> \<turnstile> App (shift G) (Var 0) : Prop"
    using G_shift x_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have body_type:
      "Prop # \<Gamma> \<turnstile>
        App (shift F) (App (shift G) (Var 0)) : Prop"
    using F_shift Gx_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_compose_def pp_unary_ty_def
    using body_type by (rule has_type.Lam)
qed

definition pp_reversible :: "oterm \<Rightarrow> oterm" where
  "pp_reversible Z =
    Exists pp_unary_ty
      (Conj
        (pp_pure pp_unary_ty (Var 0))
        (Conj
          (Eq pp_unary_ty
            (pp_compose (shift Z) (Var 0))
            pp_identity_operator)
          (Eq pp_unary_ty
            (pp_compose (Var 0) (shift Z))
            pp_identity_operator)))"

definition pp_group_member :: "oterm \<Rightarrow> oterm" where
  "pp_group_member Z =
    Conj (pp_pure pp_unary_ty Z) (pp_reversible Z)"

lemma typed_pp_reversible:
  assumes "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_reversible Z : Prop"
proof -
  have Z_shift:
      "pp_unary_ty # \<Gamma> \<turnstile> shift Z : pp_unary_ty"
    using assms by (rule typed_shift_ctx)
  have V_type:
      "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
    by (rule has_type.Var) (simp add: lookup_def)
  have ZV_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_compose (shift Z) (Var 0) : pp_unary_ty"
    using Z_shift V_type by (rule typed_pp_compose)
  have VZ_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_compose (Var 0) (shift Z) : pp_unary_ty"
    using V_type Z_shift by (rule typed_pp_compose)
  have id_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_identity_operator : pp_unary_ty"
    by (rule typed_pp_identity_operator)
  show ?thesis
    unfolding pp_reversible_def
    using typed_pp_pure[OF V_type] ZV_type VZ_type id_type
    by (intro has_type.Exists has_type.Conj has_type.Eq)
qed

lemma typed_pp_group_member:
  assumes "\<Gamma> \<turnstile> Z : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_group_member Z : Prop"
  unfolding pp_group_member_def
  using typed_pp_pure[OF assms] typed_pp_reversible[OF assms]
  by (rule has_type.Conj)

definition pp_same_kind :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_same_kind X Y =
    Exists pp_unary_ty
      (Conj
        (pp_group_member (Var 0))
        (Eq pp_unary_ty
          (shift X)
          (pp_compose (shift Y) (Var 0))))"

lemma typed_pp_same_kind:
  assumes X: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y: "\<Gamma> \<turnstile> Y : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_same_kind X Y : Prop"
proof -
  have X_shift:
      "pp_unary_ty # \<Gamma> \<turnstile> shift X : pp_unary_ty"
    using X by (rule typed_shift_ctx)
  have Y_shift:
      "pp_unary_ty # \<Gamma> \<turnstile> shift Y : pp_unary_ty"
    using Y by (rule typed_shift_ctx)
  have Z_type:
      "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
    by (rule has_type.Var) (simp add: lookup_def)
  have GZ_type:
      "pp_unary_ty # \<Gamma> \<turnstile> pp_group_member (Var 0) : Prop"
    using Z_type by (rule typed_pp_group_member)
  have YZ_type:
      "pp_unary_ty # \<Gamma> \<turnstile>
        pp_compose (shift Y) (Var 0) : pp_unary_ty"
    using Y_shift Z_type by (rule typed_pp_compose)
  show ?thesis
    unfolding pp_same_kind_def
    using GZ_type X_shift YZ_type
    by (intro has_type.Exists has_type.Conj has_type.Eq)
qed

subsection \<open>L2 and Inv\<close>

definition pp_L2 :: oterm where
  "pp_L2 =
    Forall pp_unary_ty
      (Forall pp_unary_ty
        (Forall Prop
          (Forall Prop
            (Imp
              (Conj
                (pp_pure pp_unary_ty (Var 3))
                (Conj
                  (pp_pure pp_unary_ty (Var 2))
                  (Conj
                    (pp_fun_prime (Var 1))
                    (Conj
                      (pp_fun_prime (Var 0))
                      (Eq Prop
                        (App (Var 3) (Var 1))
                        (App (Var 2) (Var 0)))))))
              (pp_same_kind (Var 3) (Var 2))))))"

text \<open>
  Binder order in \<open>pp_L2\<close> is \<open>X,Y,p,q\<close>.  In the matrix, therefore,
  \<open>Var 3 = X\<close>, \<open>Var 2 = Y\<close>, \<open>Var 1 = p\<close>, and \<open>Var 0 = q\<close>.
  The conclusion expands to \<open>\<exists>Z\<in>G. X = Y \<circ> Z\<close>.
\<close>

lemma typed_pp_L2:
  "[] \<turnstile> pp_L2 : Prop"
  by (rule infer_type_sound)
    (simp add: pp_L2_def pp_fun_prime_def pp_same_kind_def
      pp_group_member_def pp_reversible_def pp_compose_def
      pp_identity_operator_def pp_unary_ty_def pp_pure_def pp_Pure_def
      shift_by_def shift_ren_def shift_def lookup_def)

definition pp_Inv :: oterm where
  "pp_Inv =
    Forall pp_unary_ty
      (pp_group_member (Var 0) \<longleftrightarrow>\<^sub>o
        Disj
          (Eq pp_unary_ty (Var 0) pp_identity_operator)
          (Eq pp_unary_ty (Var 0) pp_negation_operator))"

lemma typed_pp_Inv:
  "[] \<turnstile> pp_Inv : Prop"
  by (rule infer_type_sound)
    (simp add: pp_Inv_def pp_group_member_def pp_reversible_def
      pp_compose_def pp_identity_operator_def pp_negation_operator_def
      pp_unary_ty_def pp_pure_def pp_Pure_def shift_def lookup_def)

subsection \<open>The T6 liar operator\<close>

definition pp_T6_liar :: oterm where
  "pp_T6_liar =
    Lam Prop
      (Forall pp_unary_ty
        (Forall Prop
          (Imp
            (Conj
              (pp_pure pp_unary_ty (Var 1))
              (Conj
                (pp_fun_prime (Var 0))
                (Eq Prop
                  (Var 2)
                  (App (Var 1) (Var 0)))))
            (Neg (App (Var 1) (Var 2))))))"

text \<open>
  Under the three binders of \<open>pp_T6_liar\<close>, \<open>Var 2 = p\<close>,
  \<open>Var 1 = X\<close>, and \<open>Var 0 = q\<close>.  Hence the matrix is exactly
  \<open>Pure(X) \<and> fun\<acute>(q) \<and> p = Xq \<longrightarrow> \<not>X p\<close>.
\<close>

lemma typed_pp_T6_liar:
  "\<Gamma> \<turnstile> pp_T6_liar : pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_T6_liar_def pp_fun_prime_def pp_unary_ty_def
      pp_pure_def pp_Pure_def shift_by_def shift_ren_def lookup_def)

lemma consts_of_pp_T6_liar:
  "consts_of pp_T6_liar = {pp_pure_name}"
  by (simp add: pp_T6_liar_def pp_fun_prime_def pp_pure_def pp_Pure_def
      shift_by_def shift_ren_def)

text \<open>
  The preceding lemma is the syntactic PP hook: the liar contains exactly the
  nonlogical name \<open>Pure\<close>.  The following abstraction makes Bacon's
  abstract-the-constants device explicit.
\<close>

definition pp_T6_abstract_body :: oterm where
  "pp_T6_abstract_body =
    Lam Prop
      (Forall pp_unary_ty
        (Forall Prop
          (Imp
            (Conj
              (App (Var 3) (Var 1))
              (Conj
                (Forall pp_unary_ty
                  (Forall pp_unary_ty
                    (Imp
                      (Conj (App (Var 5) (Var 1)) (App (Var 5) (Var 0)))
                      (Imp
                        (Eq Prop
                          (App (Var 1) (Var 2))
                          (App (Var 0) (Var 2)))
                        (Eq pp_unary_ty (Var 1) (Var 0))))))
                (Eq Prop (Var 2) (App (Var 1) (Var 0)))))
            (Neg (App (Var 1) (Var 2))))))"

definition pp_T6_purity_builder :: oterm where
  "pp_T6_purity_builder =
    Lam (pp_unary_ty \<rightarrow>\<^sub>o Prop) pp_T6_abstract_body"

abbreviation pp_T6_purity_instance :: oterm where
  "pp_T6_purity_instance \<equiv>
    App pp_T6_purity_builder (pp_Pure pp_unary_ty)"

lemma pp_T6_purity_builder_constant_free:
  "consts_of pp_T6_purity_builder = {}"
  by (simp add: pp_T6_purity_builder_def pp_T6_abstract_body_def)

lemma typed_pp_T6_purity_builder:
  "\<Gamma> \<turnstile> pp_T6_purity_builder :
    (pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_T6_purity_builder_def pp_T6_abstract_body_def
      pp_unary_ty_def lookup_def)

lemma pp_T6_builder_substitution:
  "subst0 (pp_Pure pp_unary_ty) pp_T6_abstract_body = pp_T6_liar"
  by (simp add: pp_T6_abstract_body_def subst0_def pp_T6_liar_def
      pp_fun_prime_def pp_pure_def pp_Pure_def shift_by_def shift_ren_def
      eval_nat_numeral)

lemma typed_pp_T6_purity_instance:
  "\<Gamma> \<turnstile> pp_T6_purity_instance : pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_T6_purity_builder_def pp_T6_abstract_body_def pp_Pure_def
      pp_unary_ty_def lookup_def)

lemma shift_pp_T6_purity_instance:
  "shift pp_T6_purity_instance = pp_T6_purity_instance"
  by (simp add: shift_def pp_T6_purity_builder_def pp_T6_abstract_body_def
      pp_Pure_def eval_nat_numeral)

lemma shift_pp_T6_liar:
  "shift pp_T6_liar = pp_T6_liar"
  by (simp add: shift_def pp_T6_liar_def pp_fun_prime_def pp_pure_def
      pp_Pure_def shift_by_def shift_ren_def)

lemma pp_T6_purity_instance_beta:
  "beta_contract pp_T6_purity_instance pp_T6_liar"
proof -
  have "beta_contract
      (App
        (Lam (pp_unary_ty \<rightarrow>\<^sub>o Prop) pp_T6_abstract_body)
        (pp_Pure pp_unary_ty))
      (subst0 (pp_Pure pp_unary_ty) pp_T6_abstract_body)"
    by (rule beta_contract.beta)
  then show ?thesis
    by (simp add: pp_T6_purity_builder_def pp_T6_builder_substitution)
qed

lemma CEV_pp_T6_purity_instance_pointwise:
  "Prop # \<Gamma> \<turnstile>\<^sub>CEV
    (App (shift pp_T6_purity_instance) (Var 0) \<longleftrightarrow>\<^sub>o
      App (shift pp_T6_liar) (Var 0))"
proof -
  have v: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have a: "Prop # \<Gamma> \<turnstile> App pp_T6_purity_instance (Var 0) : Prop"
    using typed_pp_T6_purity_instance v
    unfolding pp_unary_ty_def by (rule has_type.App)
  have b: "Prop # \<Gamma> \<turnstile> App pp_T6_liar (Var 0) : Prop"
    using typed_pp_T6_liar v
    unfolding pp_unary_ty_def by (rule has_type.App)
  have step: "compatible_step beta_contract
      (App pp_T6_purity_instance (Var 0))
      (App pp_T6_liar (Var 0))"
    by (intro compatible_step.App_left compatible_step.root
        pp_T6_purity_instance_beta)
  show ?thesis
    using a b step
    by (simp add: shift_pp_T6_purity_instance shift_pp_T6_liar CEV_beta_step)
qed

theorem CEV_pp_T6_purity_instance_eq_liar:
  "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty pp_T6_purity_instance pp_T6_liar"
proof -
  have "\<Gamma> \<turnstile>\<^sub>CEV
      Eq (Prop \<rightarrow>\<^sub>o Prop) pp_T6_purity_instance pp_T6_liar"
  proof (rule CEV_unary_equivalence
      [OF _ _ CEV_pp_T6_purity_instance_pointwise])
    show "\<Gamma> \<turnstile> pp_T6_purity_instance : Prop \<rightarrow>\<^sub>o Prop"
      using typed_pp_T6_purity_instance by (simp add: pp_unary_ty_def)
    show "\<Gamma> \<turnstile> pp_T6_liar : Prop \<rightarrow>\<^sub>o Prop"
      using typed_pp_T6_liar by (simp add: pp_unary_ty_def)
  qed
  then show ?thesis by (simp add: pp_unary_ty_def)
qed

subsection \<open>The exact T6-Inv machine-referee target\<close>

definition pp_T6_core_PP_axioms :: "oterm set" where
  "pp_T6_core_PP_axioms =
    pp_purity_schema \<union> pp_application_closure_schema \<union> {pp_target_PP}"

definition pp_T6_Inv_axioms :: "oterm set" where
  "pp_T6_Inv_axioms =
    pp_T6_core_PP_axioms \<union> {pp_exists_fun_prime, pp_L2, pp_Inv}"

lemma pp_T6_Inv_axioms_typed:
  assumes "A \<in> pp_T6_Inv_axioms"
  shows "[] \<turnstile> A : Prop"
  using assms pp_purity_schema_typed pp_application_closure_schema_typed
    typed_pp_target_PP
    typed_pp_exists_fun_prime typed_pp_L2 typed_pp_Inv
  unfolding pp_T6_Inv_axioms_def pp_T6_core_PP_axioms_def by blast

lemma pp_T6_purity_builder_axiom:
  "pp_pure
      ((pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty)
      pp_T6_purity_builder \<in> pp_T6_core_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def pp_purity_schema_def
    pp_logical_vocabulary_def
proof (intro UnI1 CollectI exI conjI)
  show "[] \<turnstile> pp_T6_purity_builder :
      (pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty"
    by (rule typed_pp_T6_purity_builder)
  show "consts_of pp_T6_purity_builder = {}"
    by (rule pp_T6_purity_builder_constant_free)
qed simp

lemma pp_T6_application_closure_axiom:
  "pp_application_closure \<sigma> \<tau> \<in> pp_T6_core_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def pp_application_closure_schema_def
  by blast

lemma pp_T6_target_axiom:
  "pp_target_PP \<in> pp_T6_core_PP_axioms"
  unfolding pp_T6_core_PP_axioms_def by blast

theorem pp_T6_liar_pure:
  "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty pp_T6_liar"
proof -
  have builder_pure:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure
        ((pp_unary_ty \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o pp_unary_ty)
        pp_T6_purity_builder"
    using pp_T6_purity_builder_axiom
      typed_pp_pure[OF typed_pp_T6_purity_builder]
    by (rule CEV_axiom_proves.Axiom)
  have Pure_pure:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure (pp_unary_ty \<rightarrow>\<^sub>o Prop) (pp_Pure pp_unary_ty)"
  proof -
    have target_type: "\<Gamma> \<turnstile> pp_target_PP : Prop"
      by (rule infer_type_sound)
        (simp add: pp_target_PP_def pp_purity_of_pure_def pp_pure_def
          pp_Pure_def pp_unary_ty_def lookup_def)
    have "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+ pp_target_PP"
      using pp_T6_target_axiom target_type by (rule CEV_axiom_proves.Axiom)
    then show ?thesis
      by (simp add: pp_target_PP_def pp_purity_of_pure_def pp_unary_ty_def)
  qed
  have instance_pure:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      pp_pure pp_unary_ty pp_T6_purity_instance"
    using pp_T6_application_closure_axiom
      typed_pp_T6_purity_builder
      typed_pp_Pure[of \<Gamma> pp_unary_ty]
      builder_pure Pure_pure
    by (rule pp_axiom_application_closed)
  have ll: "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Eq pp_unary_ty pp_T6_purity_instance pp_T6_liar)
        (Imp
          (pp_pure pp_unary_ty pp_T6_purity_instance)
          (pp_pure pp_unary_ty pp_T6_liar))"
    using typed_pp_T6_purity_instance typed_pp_T6_liar typed_pp_Pure
    unfolding pp_pure_def
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.LL)
  have transfer:
    "\<Gamma> ; pp_T6_core_PP_axioms \<turnstile>\<^sub>CEV\<^sup>+
      Imp
        (pp_pure pp_unary_ty pp_T6_purity_instance)
        (pp_pure pp_unary_ty pp_T6_liar)"
    by (rule CEV_axiom_proves.MP
        [OF CEV_axiom_proves.Base[OF CEV_pp_T6_purity_instance_eq_liar]
            CEV_axiom_proves.Base[OF ll]])
  show ?thesis
    using instance_pure transfer by (rule CEV_axiom_proves.MP)
qed

corollary pp_T6_liar_pure_Inv:
  "\<Gamma> ; pp_T6_Inv_axioms \<turnstile>\<^sub>CEV\<^sup>+
    pp_pure pp_unary_ty pp_T6_liar"
  using pp_T6_liar_pure
  by (rule CEV_axiom_proves_mono)
    (auto simp: pp_T6_Inv_axioms_def)

definition pp_T6_Inv_inconsistency_target :: bool where
  "pp_T6_Inv_inconsistency_target \<longleftrightarrow>
    [] ; pp_T6_Inv_axioms \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"

text \<open>
  The proposed first formal T6 claim is
  \<open>pp_T6_Inv_inconsistency_target\<close>.  Its nonlogical axioms are exactly the
  purity schema, application closure, PP at \<open>t \<rightarrow> t\<close>, an explicit
  \<open>fun\<acute>\<close> witness, weak L2, and Inv.  Recombination, fundamentality
  assumptions, Exhaustion, Persistence, and Purity of Fun are absent.
\<close>

end
