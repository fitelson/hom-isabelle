theory Bacon_PP_Goodman_T6_RS_Encoding
  imports 
    "Goodman_Legacy_05.Bacon_PP_Goodman_T6_WI"
begin

section \<open>Goodman T6: strong L2 and rigid specification\<close>

subsection \<open>Strong L2\<close>

definition pp_strong_same_kind ::
    "oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm"
  where
  "pp_strong_same_kind X Y p q =
    Exists pp_unary_ty
      (Conj
        (pp_group_member (Var 0))
        (Conj
          (Eq pp_unary_ty
            (shift X)
            (pp_compose (shift Y) (Var 0)))
          (Eq Prop
            (shift q)
            (App (Var 0) (shift p)))))"

definition pp_strong_L2 :: oterm where
  "pp_strong_L2 =
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
              (pp_strong_same_kind
                (Var 3) (Var 2) (Var 1) (Var 0))))))"

lemma typed_pp_strong_same_kind:
  assumes X_type: "\<Gamma> \<turnstile> X : pp_unary_ty"
    and Y_type: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and p_type: "\<Gamma> \<turnstile> p : Prop"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> \<turnstile> pp_strong_same_kind X Y p q : Prop"
proof -
  have Z_type:
    "pp_unary_ty # \<Gamma> \<turnstile> Var 0 : pp_unary_ty"
    by (rule typed_var0)
  have Xs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift X : pp_unary_ty"
    using X_type by (rule typed_shift_ctx)
  have Ys_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift Y : pp_unary_ty"
    using Y_type by (rule typed_shift_ctx)
  have ps_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift p : Prop"
    using p_type by (rule typed_shift_ctx)
  have qs_type:
    "pp_unary_ty # \<Gamma> \<turnstile> shift q : Prop"
    using q_type by (rule typed_shift_ctx)
  have group_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      pp_group_member (Var 0) : Prop"
    using Z_type by (rule typed_pp_group_member)
  have compose_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      pp_compose (shift Y) (Var 0) : pp_unary_ty"
    using Ys_type Z_type by (rule typed_pp_compose)
  have Zp_type:
    "pp_unary_ty # \<Gamma> \<turnstile>
      App (Var 0) (shift p) : Prop"
    using Z_type ps_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_strong_same_kind_def
    using group_type Xs_type compose_type qs_type Zp_type
    by (intro has_type.Exists has_type.Conj has_type.Eq)
qed

lemma typed_pp_strong_L2:
  "\<Gamma> \<turnstile> pp_strong_L2 : Prop"
  by (rule infer_type_sound)
    (simp add: pp_strong_L2_def pp_strong_same_kind_def
      pp_fun_prime_def pp_group_member_def pp_reversible_def
      pp_compose_def pp_identity_operator_def pp_pure_def pp_Pure_def
      pp_unary_ty_def shift_by_def shift_ren_def shift_def lookup_def)

lemma subst_pp_strong_same_kind[simp]:
  "subst s (pp_strong_same_kind X Y p q) =
    pp_strong_same_kind
      (subst s X) (subst s Y) (subst s p) (subst s q)"
  by (simp add: pp_strong_same_kind_def subst_lift_shift)

subsection \<open>Rigid specifications\<close>

definition pp_spec_instantiated :: "oterm \<Rightarrow> oterm" where
  "pp_spec_instantiated R =
    Exists Prop (App (shift R) (Var 0))"

definition pp_spec_only_fun_prime :: "oterm \<Rightarrow> oterm" where
  "pp_spec_only_fun_prime R =
    Forall Prop
      (Imp
        (App (shift R) (Var 0))
        (pp_fun_prime (Var 0)))"

definition pp_spec_rigid :: "oterm \<Rightarrow> oterm" where
  "pp_spec_rigid R =
    Forall pp_unary_ty
      (Forall Prop
        (Forall Prop
          (Imp
            (Conj
              (pp_group_member (Var 2))
              (Conj
                (App (shift (shift (shift R))) (Var 1))
                (Conj
                  (App (shift (shift (shift R))) (Var 0))
                  (Eq Prop
                    (Var 0)
                    (App (Var 2) (Var 1))))))
            (Eq Prop (Var 1) (Var 0)))))"

definition pp_rigid_specification :: "oterm \<Rightarrow> oterm" where
  "pp_rigid_specification R =
    Conj
      (pp_pure pp_unary_ty R)
      (Conj
        (pp_spec_instantiated R)
        (Conj
          (pp_spec_only_fun_prime R)
          (pp_spec_rigid R)))"

definition pp_RS :: oterm where
  "pp_RS =
    Exists pp_unary_ty
      (pp_rigid_specification (Var 0))"

lemma typed_pp_spec_instantiated:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_spec_instantiated R : Prop"
proof -
  have Rs_type: "Prop # \<Gamma> \<turnstile> shift R : pp_unary_ty"
    using R_type by (rule typed_shift_ctx)
  have p_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have app_type: "Prop # \<Gamma> \<turnstile> App (shift R) (Var 0) : Prop"
    using Rs_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  show ?thesis
    unfolding pp_spec_instantiated_def
    using app_type by (rule has_type.Exists)
qed

lemma typed_pp_spec_only_fun_prime:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_spec_only_fun_prime R : Prop"
proof -
  have Rs_type: "Prop # \<Gamma> \<turnstile> shift R : pp_unary_ty"
    using R_type by (rule typed_shift_ctx)
  have p_type: "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have app_type: "Prop # \<Gamma> \<turnstile> App (shift R) (Var 0) : Prop"
    using Rs_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have fun_type:
    "Prop # \<Gamma> \<turnstile> pp_fun_prime (Var 0) : Prop"
    using p_type by (rule typed_pp_fun_prime)
  show ?thesis
    unfolding pp_spec_only_fun_prime_def
    using app_type fun_type
    by (intro has_type.Forall has_type.Imp)
qed

lemma typed_pp_spec_rigid:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_spec_rigid R : Prop"
proof -
  let ?\<Delta> = "Prop # Prop # pp_unary_ty # \<Gamma>"
  have Z_type: "?\<Delta> \<turnstile> Var 2 : pp_unary_ty"
    by (rule has_type.Var) (simp add: lookup_def)
  have p_type: "?\<Delta> \<turnstile> Var 1 : Prop"
    by (rule has_type.Var) (simp add: lookup_def)
  have q_type: "?\<Delta> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have R1: "pp_unary_ty # \<Gamma> \<turnstile> shift R : pp_unary_ty"
    using R_type by (rule typed_shift_ctx)
  have R2: "Prop # pp_unary_ty # \<Gamma> \<turnstile>
      shift (shift R) : pp_unary_ty"
    using R1 by (rule typed_shift_ctx)
  have R3: "?\<Delta> \<turnstile>
      shift (shift (shift R)) : pp_unary_ty"
    using R2 by (rule typed_shift_ctx)
  have Rp_type:
    "?\<Delta> \<turnstile>
      App (shift (shift (shift R))) (Var 1) : Prop"
    using R3 p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Rq_type:
    "?\<Delta> \<turnstile>
      App (shift (shift (shift R))) (Var 0) : Prop"
    using R3 q_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Zp_type: "?\<Delta> \<turnstile> App (Var 2) (Var 1) : Prop"
    using Z_type p_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have group_type: "?\<Delta> \<turnstile> pp_group_member (Var 2) : Prop"
    using Z_type by (rule typed_pp_group_member)
  show ?thesis
    unfolding pp_spec_rigid_def
    using group_type Rp_type Rq_type q_type Zp_type p_type
    by (intro has_type.Forall has_type.Imp has_type.Conj has_type.Eq)
qed

lemma typed_pp_rigid_specification:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_rigid_specification R : Prop"
  unfolding pp_rigid_specification_def
  using typed_pp_pure[OF R_type]
    typed_pp_spec_instantiated[OF R_type]
    typed_pp_spec_only_fun_prime[OF R_type]
    typed_pp_spec_rigid[OF R_type]
  by (intro has_type.Conj)

lemma typed_pp_RS:
  "\<Gamma> \<turnstile> pp_RS : Prop"
  unfolding pp_RS_def
  using typed_pp_rigid_specification[
      OF typed_var0[
        where \<sigma> = pp_unary_ty and \<Gamma> = "\<Gamma>"]]
  by (rule has_type.Exists)

lemma subst_pp_spec_instantiated[simp]:
  "subst s (pp_spec_instantiated R) =
    pp_spec_instantiated (subst s R)"
  by (simp add: pp_spec_instantiated_def subst_lift_shift)

lemma subst_pp_spec_only_fun_prime[simp]:
  "subst s (pp_spec_only_fun_prime R) =
    pp_spec_only_fun_prime (subst s R)"
  by (simp add: pp_spec_only_fun_prime_def subst_lift_shift)

lemma lift_subst_three_var2_RS[simp]:
  "lift_subst (lift_subst (lift_subst s)) 2 = Var 2"
  by (simp add: eval_nat_numeral)

lemma subst_pp_spec_rigid[simp]:
  "subst s (pp_spec_rigid R) =
    pp_spec_rigid (subst s R)"
  by (simp add: pp_spec_rigid_def subst_lift_shift)

lemma subst_pp_rigid_specification[simp]:
  "subst s (pp_rigid_specification R) =
    pp_rigid_specification (subst s R)"
  by (simp add: pp_rigid_specification_def)

lemma rename_pp_spec_instantiated_RS[simp]:
  "rename r (pp_spec_instantiated R) =
    pp_spec_instantiated (rename r R)"
  by (simp add: pp_spec_instantiated_def shift_rename_lift)

lemma rename_pp_spec_only_fun_prime_RS[simp]:
  "rename r (pp_spec_only_fun_prime R) =
    pp_spec_only_fun_prime (rename r R)"
  by (simp add: pp_spec_only_fun_prime_def pp_fun_prime_def
      pp_pure_def pp_Pure_def shift_by_def shift_ren_def
      shift_rename_lift rename_comp)

lemma rename_pp_spec_rigid_RS[simp]:
  "rename r (pp_spec_rigid R) =
    pp_spec_rigid (rename r R)"
  by (simp add: pp_spec_rigid_def shift_rename_lift)

lemma rename_pp_rigid_specification_RS[simp]:
  "rename r (pp_rigid_specification R) =
    pp_rigid_specification (rename r R)"
  by (simp add: pp_rigid_specification_def
      pp_pure_def pp_Pure_def)

lemma shift_pp_spec_instantiated_RS[simp]:
  "shift (pp_spec_instantiated R) =
    pp_spec_instantiated (shift R)"
  by (simp add: shift_def)

lemma shift_pp_spec_only_fun_prime_RS[simp]:
  "shift (pp_spec_only_fun_prime R) =
    pp_spec_only_fun_prime (shift R)"
  by (simp add: shift_def)

lemma shift_pp_spec_rigid_RS[simp]:
  "shift (pp_spec_rigid R) =
    pp_spec_rigid (shift R)"
  by (simp add: shift_def)

lemma shift_pp_rigid_specification_RS[simp]:
  "shift (pp_rigid_specification R) =
    pp_rigid_specification (shift R)"
  by (simp add: shift_def)

definition pp_T6_RS_axioms :: "oterm set" where
  "pp_T6_RS_axioms =
    insert pp_RS
      (insert pp_strong_L2 pp_T6_core_PP_axioms)"

subsection \<open>The existential diagonal\<close>

definition pp_RS_diagonal :: "oterm \<Rightarrow> oterm" where
  "pp_RS_diagonal R =
    Lam Prop
      (Exists pp_unary_ty
        (Exists Prop
          (Conj
            (pp_pure pp_unary_ty (Var 1))
            (Conj
              (App (shift (shift (shift R))) (Var 0))
              (Conj
                (Eq Prop
                  (Var 2)
                  (App (Var 1) (Var 0)))
                (Neg (App (Var 1) (Var 2))))))))"

definition pp_RS_diagonal_body :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "pp_RS_diagonal_body R x =
    Exists pp_unary_ty
      (Exists Prop
        (Conj
          (pp_pure pp_unary_ty (Var 1))
          (Conj
            (App (shift (shift R)) (Var 0))
            (Conj
              (Eq Prop
                (shift (shift x))
                (App (Var 1) (Var 0)))
              (Neg (App (Var 1) (shift (shift x))))))))"

definition pp_RS_diagonal_builder :: oterm where
  "pp_RS_diagonal_builder =
    Lam (pp_unary_ty \<rightarrow>\<^sub>o Prop)
      (Lam pp_unary_ty
        (Lam Prop
          (Exists pp_unary_ty
            (Exists Prop
              (Conj
                (App (Var 4) (Var 1))
                (Conj
                  (App (Var 3) (Var 0))
                  (Conj
                    (Eq Prop
                      (Var 2)
                      (App (Var 1) (Var 0)))
                    (Neg (App (Var 1) (Var 2))))))))))"

abbreviation pp_RS_diagonal_instance :: "oterm \<Rightarrow> oterm" where
  "pp_RS_diagonal_instance R \<equiv>
    App
      (App pp_RS_diagonal_builder (pp_Pure pp_unary_ty))
      R"

lemma typed_pp_RS_diagonal:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_RS_diagonal R : pp_unary_ty"
proof -
  let ?\<Delta> = "Prop # pp_unary_ty # Prop # \<Gamma>"
  have x_type: "?\<Delta> \<turnstile> Var 2 : Prop"
    by (rule has_type.Var) (simp add: lookup_def)
  have Y_type: "?\<Delta> \<turnstile> Var 1 : pp_unary_ty"
    by (rule has_type.Var) (simp add: lookup_def)
  have y_type: "?\<Delta> \<turnstile> Var 0 : Prop"
    by (rule typed_var0)
  have R1: "Prop # \<Gamma> \<turnstile> shift R : pp_unary_ty"
    using R_type by (rule typed_shift_ctx)
  have R2: "pp_unary_ty # Prop # \<Gamma> \<turnstile>
      shift (shift R) : pp_unary_ty"
    using R1 by (rule typed_shift_ctx)
  have R3: "?\<Delta> \<turnstile>
      shift (shift (shift R)) : pp_unary_ty"
    using R2 by (rule typed_shift_ctx)
  have Ry_type:
    "?\<Delta> \<turnstile> App (shift (shift (shift R))) (Var 0) : Prop"
    using R3 y_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Yy_type: "?\<Delta> \<turnstile> App (Var 1) (Var 0) : Prop"
    using Y_type y_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have Yx_type: "?\<Delta> \<turnstile> App (Var 1) (Var 2) : Prop"
    using Y_type x_type unfolding pp_unary_ty_def
    by (rule has_type.App)
  have body_type:
    "?\<Delta> \<turnstile>
      Conj
        (pp_pure pp_unary_ty (Var 1))
        (Conj
          (App (shift (shift (shift R))) (Var 0))
          (Conj
            (Eq Prop (Var 2) (App (Var 1) (Var 0)))
            (Neg (App (Var 1) (Var 2))))) : Prop"
    using typed_pp_pure[OF Y_type]
      Ry_type x_type Yy_type Yx_type
    by (intro has_type.Conj has_type.Eq has_type.Neg)
  have body_type':
    "Prop # (Prop \<rightarrow>\<^sub>o Prop) # Prop # \<Gamma> \<turnstile>
      Conj
        (pp_pure (Prop \<rightarrow>\<^sub>o Prop) (Var 1))
        (Conj
          (App (shift (shift (shift R))) (Var 0))
          (Conj
            (Eq Prop (Var 2) (App (Var 1) (Var 0)))
            (Neg (App (Var 1) (Var 2))))) : Prop"
    using body_type by (simp add: pp_unary_ty_def)
  show ?thesis
    unfolding pp_RS_diagonal_def pp_unary_ty_def
    using body_type'
    by (intro has_type.Lam has_type.Exists)
qed

lemma pp_RS_diagonal_body_substitution:
  "subst0 x
    (Exists pp_unary_ty
      (Exists Prop
        (Conj
          (pp_pure pp_unary_ty (Var 1))
          (Conj
            (App (shift (shift (shift R))) (Var 0))
            (Conj
              (Eq Prop
                (Var 2)
                (App (Var 1) (Var 0)))
              (Neg (App (Var 1) (Var 2))))))))
    = pp_RS_diagonal_body R x"
  by (simp add: pp_RS_diagonal_body_def subst0_def
      pp_pure_def pp_Pure_def)

lemma pp_RS_diagonal_apply_contract:
  "beta_contract
    (App (pp_RS_diagonal R) x)
    (pp_RS_diagonal_body R x)"
proof -
  have raw:
    "beta_contract
      (App
        (Lam Prop
          (Exists pp_unary_ty
            (Exists Prop
              (Conj
                (pp_pure pp_unary_ty (Var 1))
                (Conj
                  (App (shift (shift (shift R))) (Var 0))
                  (Conj
                    (Eq Prop
                      (Var 2)
                      (App (Var 1) (Var 0)))
                    (Neg (App (Var 1) (Var 2)))))))))
        x)
      (subst0 x
        (Exists pp_unary_ty
          (Exists Prop
            (Conj
              (pp_pure pp_unary_ty (Var 1))
              (Conj
                (App (shift (shift (shift R))) (Var 0))
                (Conj
                  (Eq Prop
                    (Var 2)
                    (App (Var 1) (Var 0)))
                  (Neg (App (Var 1) (Var 2)))))))))"
    by (rule beta_contract.beta)
  show ?thesis
    using raw
    by (simp only: pp_RS_diagonal_def
        pp_RS_diagonal_body_substitution)
qed

lemma typed_pp_RS_diagonal_body:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
    and x_type: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile> pp_RS_diagonal_body R x : Prop"
proof -
  have diagonal_type:
    "\<Gamma> \<turnstile> pp_RS_diagonal R : pp_unary_ty"
    using R_type by (rule typed_pp_RS_diagonal)
  have application_type:
    "\<Gamma> \<turnstile> App (pp_RS_diagonal R) x : Prop"
    using diagonal_type x_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have step:
    "beta_contract
      (App (pp_RS_diagonal R) x)
      (pp_RS_diagonal_body R x)"
    by (rule pp_RS_diagonal_apply_contract)
  show ?thesis
    using step application_type
    by (rule beta_contract_preserves_typing)
qed

lemma pp_RS_diagonal_apply_beta:
  "compatible_step beta_contract
    (App (pp_RS_diagonal R) x)
    (pp_RS_diagonal_body R x)"
  using pp_RS_diagonal_apply_contract
  by (rule compatible_step.root)

lemma CEV_pp_RS_diagonal_apply_eq:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
    and x_type: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq Prop
      (App (pp_RS_diagonal R) x)
      (pp_RS_diagonal_body R x)"
proof -
  have diagonal_type:
    "\<Gamma> \<turnstile> pp_RS_diagonal R : pp_unary_ty"
    using R_type by (rule typed_pp_RS_diagonal)
  have left_type:
    "\<Gamma> \<turnstile> App (pp_RS_diagonal R) x : Prop"
    using diagonal_type x_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have right_type:
    "\<Gamma> \<turnstile> pp_RS_diagonal_body R x : Prop"
    using R_type x_type by (rule typed_pp_RS_diagonal_body)
  have iff:
    "\<Gamma> \<turnstile>\<^sub>CEV
      (App (pp_RS_diagonal R) x
        \<longleftrightarrow>\<^sub>o pp_RS_diagonal_body R x)"
    using left_type right_type pp_RS_diagonal_apply_beta
    by (rule CEV_beta_step)
  show ?thesis
    using left_type right_type iff
    by (rule CEV_zeroary_equivalence)
qed

lemma typed_pp_RS_diagonal_builder:
  "\<Gamma> \<turnstile> pp_RS_diagonal_builder :
    (pp_unary_ty \<rightarrow>\<^sub>o Prop)
      \<rightarrow>\<^sub>o (pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty)"
  by (rule infer_type_sound)
    (simp add: pp_RS_diagonal_builder_def pp_unary_ty_def
      lookup_def)

lemma pp_RS_diagonal_builder_constant_free:
  "consts_of pp_RS_diagonal_builder = {}"
  by (simp add: pp_RS_diagonal_builder_def)

lemma typed_pp_RS_diagonal_instance:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
  shows "\<Gamma> \<turnstile> pp_RS_diagonal_instance R : pp_unary_ty"
  using typed_pp_RS_diagonal_builder
    typed_pp_Pure[of \<Gamma> pp_unary_ty] R_type
  by (intro has_type.App)

lemma pp_RS_diagonal_R_substitution:
  "subst0 R
    (Lam Prop
      (Exists pp_unary_ty
        (Exists Prop
          (Conj
            (pp_pure pp_unary_ty (Var 1))
            (Conj
              (App (Var 3) (Var 0))
              (Conj
                (Eq Prop
                  (Var 2)
                  (App (Var 1) (Var 0)))
                (Neg (App (Var 1) (Var 2)))))))))
    = pp_RS_diagonal R"
  by (simp add: pp_RS_diagonal_def subst0_def
      subst_lift_shift shift_def eval_nat_numeral)

lemma pp_RS_diagonal_instance_beta:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
  shows
  "beta_eta_equiv \<Gamma> pp_unary_ty
    (pp_RS_diagonal_instance R)
    (pp_RS_diagonal R)"
proof -
  have first:
    "beta_contract
      (App pp_RS_diagonal_builder (pp_Pure pp_unary_ty))
      (subst0 (pp_Pure pp_unary_ty)
        (Lam pp_unary_ty
          (Lam Prop
            (Exists pp_unary_ty
              (Exists Prop
                (Conj
                  (App (Var 4) (Var 1))
                  (Conj
                    (App (Var 3) (Var 0))
                    (Conj
                      (Eq Prop
                        (Var 2)
                        (App (Var 1) (Var 0)))
                      (Neg (App (Var 1) (Var 2)))))))))))"
    unfolding pp_RS_diagonal_builder_def
    by (rule beta_contract.beta)
  have first_step:
    "compatible_step beta_contract
      (pp_RS_diagonal_instance R)
      (App
        (Lam pp_unary_ty
          (Lam Prop
            (Exists pp_unary_ty
              (Exists Prop
                (Conj
                  (pp_pure pp_unary_ty (Var 1))
                  (Conj
                    (App (Var 3) (Var 0))
                    (Conj
                      (Eq Prop
                        (Var 2)
                        (App (Var 1) (Var 0)))
                      (Neg (App (Var 1) (Var 2))))))))))
        R)"
    using first
    by (intro compatible_step.App_left compatible_step.root)
      (simp add: subst0_def pp_pure_def pp_Pure_def
        pp_RS_diagonal_builder_def eval_nat_numeral)
  have second:
    "beta_contract
      (App
        (Lam pp_unary_ty
          (Lam Prop
            (Exists pp_unary_ty
              (Exists Prop
                (Conj
                  (pp_pure pp_unary_ty (Var 1))
                  (Conj
                    (App (Var 3) (Var 0))
                    (Conj
                      (Eq Prop
                        (Var 2)
                        (App (Var 1) (Var 0)))
                      (Neg (App (Var 1) (Var 2))))))))))
        R)
      (subst0 R
        (Lam Prop
          (Exists pp_unary_ty
            (Exists Prop
              (Conj
                (pp_pure pp_unary_ty (Var 1))
                (Conj
                  (App (Var 3) (Var 0))
                  (Conj
                    (Eq Prop
                      (Var 2)
                      (App (Var 1) (Var 0)))
                    (Neg (App (Var 1) (Var 2))))))))))"
    by (rule beta_contract.beta)
  have second_step:
    "compatible_step beta_contract
      (App
        (Lam pp_unary_ty
          (Lam Prop
            (Exists pp_unary_ty
              (Exists Prop
                (Conj
                  (pp_pure pp_unary_ty (Var 1))
                  (Conj
                    (App (Var 3) (Var 0))
                    (Conj
                      (Eq Prop
                        (Var 2)
                        (App (Var 1) (Var 0)))
                      (Neg (App (Var 1) (Var 2))))))))))
        R)
      (pp_RS_diagonal R)"
    using second
    by (intro compatible_step.root)
      (simp only: pp_RS_diagonal_R_substitution)
  have source_type:
    "\<Gamma> \<turnstile> pp_RS_diagonal_instance R : pp_unary_ty"
    using R_type by (rule typed_pp_RS_diagonal_instance)
  have intermediate_type:
    "\<Gamma> \<turnstile>
      App
        (Lam pp_unary_ty
          (Lam Prop
            (Exists pp_unary_ty
              (Exists Prop
                (Conj
                  (pp_pure pp_unary_ty (Var 1))
                  (Conj
                    (App (Var 3) (Var 0))
                    (Conj
                      (Eq Prop
                        (Var 2)
                        (App (Var 1) (Var 0)))
                      (Neg (App (Var 1) (Var 2))))))))))
        R : pp_unary_ty"
  proof (rule has_type.App)
    show "\<Gamma> \<turnstile>
      Lam pp_unary_ty
        (Lam Prop
          (Exists pp_unary_ty
            (Exists Prop
              (Conj
                (pp_pure pp_unary_ty (Var 1))
                (Conj
                  (App (Var 3) (Var 0))
                  (Conj
                    (Eq Prop
                      (Var 2)
                      (App (Var 1) (Var 0)))
                    (Neg (App (Var 1) (Var 2)))))))))
      : pp_unary_ty \<rightarrow>\<^sub>o pp_unary_ty"
      by (rule infer_type_sound)
        (simp add: pp_pure_def pp_Pure_def pp_unary_ty_def lookup_def)
    show "\<Gamma> \<turnstile> R : pp_unary_ty"
      by (rule R_type)
  qed
  have target_type:
    "\<Gamma> \<turnstile> pp_RS_diagonal R : pp_unary_ty"
    using R_type by (rule typed_pp_RS_diagonal)
  have first_equiv:
    "beta_eta_equiv \<Gamma> pp_unary_ty
      (pp_RS_diagonal_instance R)
      (App
        (Lam pp_unary_ty
          (Lam Prop
            (Exists pp_unary_ty
              (Exists Prop
                (Conj
                  (pp_pure pp_unary_ty (Var 1))
                  (Conj
                    (App (Var 3) (Var 0))
                    (Conj
                      (Eq Prop
                        (Var 2)
                        (App (Var 1) (Var 0)))
                      (Neg (App (Var 1) (Var 2))))))))))
        R)"
    using source_type intermediate_type first_step
    by (rule beta_eta_equiv.Beta)
  have second_equiv:
    "beta_eta_equiv \<Gamma> pp_unary_ty
      (App
        (Lam pp_unary_ty
          (Lam Prop
            (Exists pp_unary_ty
              (Exists Prop
                (Conj
                  (pp_pure pp_unary_ty (Var 1))
                  (Conj
                    (App (Var 3) (Var 0))
                    (Conj
                      (Eq Prop
                        (Var 2)
                        (App (Var 1) (Var 0)))
                      (Neg (App (Var 1) (Var 2))))))))))
        R)
      (pp_RS_diagonal R)"
    using intermediate_type target_type second_step
    by (rule beta_eta_equiv.Beta)
  show ?thesis
    using first_equiv second_equiv
    by (rule beta_eta_equiv.Trans)
qed

lemma beta_eta_equiv_app_left_RS:
  assumes conversion: "beta_eta_equiv \<Gamma> \<rho> M N"
    and type_shape: "\<rho> = (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
    and argument_type: "\<Gamma> \<turnstile> A : \<sigma>"
  shows "beta_eta_equiv \<Gamma> \<tau> (App M A) (App N A)"
  using conversion type_shape argument_type
proof (induction arbitrary: \<sigma> \<tau> A)
  case (Refl \<Gamma> M \<rho>)
  have M_type: "\<Gamma> \<turnstile> M : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using Refl.hyps Refl.prems by simp
  then show ?case
    using Refl.prems(2)
    by (intro beta_eta_equiv.Refl has_type.App)
next
  case (Beta \<Gamma> M \<rho> N)
  have function_types:
    "\<Gamma> \<turnstile> M : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    "\<Gamma> \<turnstile> N : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using Beta.hyps Beta.prems by simp_all
  have M_type: "\<Gamma> \<turnstile> App M A : \<tau>"
    using function_types(1) Beta.prems(2) by (rule has_type.App)
  have N_type: "\<Gamma> \<turnstile> App N A : \<tau>"
    using function_types(2) Beta.prems(2) by (rule has_type.App)
  have step: "compatible_step beta_contract (App M A) (App N A)"
    using Beta.hyps(3) by (rule compatible_step.App_left)
  show ?case
    using M_type N_type step by (rule beta_eta_equiv.Beta)
next
  case (Eta \<Gamma> M \<rho> N)
  have function_types:
    "\<Gamma> \<turnstile> M : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    "\<Gamma> \<turnstile> N : \<sigma> \<rightarrow>\<^sub>o \<tau>"
    using Eta.hyps Eta.prems by simp_all
  have M_type: "\<Gamma> \<turnstile> App M A : \<tau>"
    using function_types(1) Eta.prems(2) by (rule has_type.App)
  have N_type: "\<Gamma> \<turnstile> App N A : \<tau>"
    using function_types(2) Eta.prems(2) by (rule has_type.App)
  have step: "compatible_step eta_contract (App M A) (App N A)"
    using Eta.hyps(3) by (rule compatible_step.App_left)
  show ?case
    using M_type N_type step by (rule beta_eta_equiv.Eta)
next
  case (Sym \<Gamma> \<rho> M N)
  have inner:
    "beta_eta_equiv \<Gamma> \<tau> (App M A) (App N A)"
    using Sym.prems by (rule Sym.IH)
  show ?case
    using inner by (rule beta_eta_equiv.Sym)
next
  case (Trans \<Gamma> \<rho> M N P)
  have first:
    "beta_eta_equiv \<Gamma> \<tau> (App M A) (App N A)"
    using Trans.prems by (rule Trans.IH(1))
  have second:
    "beta_eta_equiv \<Gamma> \<tau> (App N A) (App P A)"
    using Trans.prems by (rule Trans.IH(2))
  show ?case
    using first second by (rule beta_eta_equiv.Trans)
qed

lemma shift_pp_RS_diagonal_builder[simp]:
  "shift pp_RS_diagonal_builder = pp_RS_diagonal_builder"
  by (simp add: shift_def pp_RS_diagonal_builder_def
      shift_by_def shift_ren_def rename_comp comp_def eval_nat_numeral)

lemma shift_pp_RS_diagonal[simp]:
  "shift (pp_RS_diagonal R) = pp_RS_diagonal (shift R)"
  by (simp add: shift_def pp_RS_diagonal_def
      shift_by_def shift_ren_def rename_comp comp_def eval_nat_numeral)

lemma shift_pp_Pure_RS[simp]:
  "shift (pp_Pure \<tau>) = pp_Pure \<tau>"
  by (simp add: shift_def pp_Pure_def)

lemma shift_pp_RS_diagonal_instance[simp]:
  "shift (pp_RS_diagonal_instance R) =
    pp_RS_diagonal_instance (shift R)"
  by (simp add: shift_def pp_Pure_def pp_RS_diagonal_builder_def
      shift_by_def shift_ren_def rename_comp comp_def eval_nat_numeral)

lemma CEV_pp_RS_diagonal_instance_pointwise:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
  shows "Prop # \<Gamma> \<turnstile>\<^sub>CEV
    (App (shift (pp_RS_diagonal_instance R)) (Var 0)
      \<longleftrightarrow>\<^sub>o
    App (shift (pp_RS_diagonal R)) (Var 0))"
proof -
  have shifted_R_type:
    "Prop # \<Gamma> \<turnstile> shift R : pp_unary_ty"
    using R_type by (rule typed_shift_ctx)
  have conversion:
    "beta_eta_equiv (Prop # \<Gamma>) pp_unary_ty
      (pp_RS_diagonal_instance (shift R))
      (pp_RS_diagonal (shift R))"
    using shifted_R_type by (rule pp_RS_diagonal_instance_beta)
  have pointwise:
    "beta_eta_equiv (Prop # \<Gamma>) Prop
      (App (pp_RS_diagonal_instance (shift R)) (Var 0))
      (App (pp_RS_diagonal (shift R)) (Var 0))"
  proof (rule beta_eta_equiv_app_left_RS)
    show "beta_eta_equiv (Prop # \<Gamma>) pp_unary_ty
      (pp_RS_diagonal_instance (shift R))
      (pp_RS_diagonal (shift R))"
      by (rule conversion)
    show "pp_unary_ty = Prop \<rightarrow>\<^sub>o Prop"
      by (simp add: pp_unary_ty_def)
    show "Prop # \<Gamma> \<turnstile> Var 0 : Prop"
      by (rule typed_var0)
  qed
  show ?thesis
    using pointwise by (simp add: CEV_beta_eta_equiv)
qed

lemma CEV_pp_RS_diagonal_instance_eq:
  assumes R_type: "\<Gamma> \<turnstile> R : pp_unary_ty"
  shows "\<Gamma> \<turnstile>\<^sub>CEV
    Eq pp_unary_ty
      (pp_RS_diagonal_instance R)
      (pp_RS_diagonal R)"
proof -
  have "\<Gamma> \<turnstile>\<^sub>CEV
    Eq (Prop \<rightarrow>\<^sub>o Prop)
      (pp_RS_diagonal_instance R)
      (pp_RS_diagonal R)"
  proof (rule CEV_unary_equivalence
      [OF _ _ CEV_pp_RS_diagonal_instance_pointwise[OF R_type]])
    show "\<Gamma> \<turnstile> pp_RS_diagonal_instance R :
      Prop \<rightarrow>\<^sub>o Prop"
      using typed_pp_RS_diagonal_instance[OF R_type]
      by (simp add: pp_unary_ty_def)
    show "\<Gamma> \<turnstile> pp_RS_diagonal R :
      Prop \<rightarrow>\<^sub>o Prop"
      using typed_pp_RS_diagonal[OF R_type]
      by (simp add: pp_unary_ty_def)
  qed
  then show ?thesis
    by (simp add: pp_unary_ty_def)
qed

end
