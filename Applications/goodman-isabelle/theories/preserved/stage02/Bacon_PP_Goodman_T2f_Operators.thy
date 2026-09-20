theory Bacon_PP_Goodman_T2f_Operators
  imports 
    "Goodman_Legacy_02.Bacon_PP_Goodman_Fun_Prime_Six_Distinct"
begin

section \<open>The six pure unary operators behind Goodman T2f\<close>

lemma CEV_T2f_taut_plus:
  assumes "prop_tautology \<Gamma> A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms
  by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.H H_proves.PC)

lemma CEVp_not_ObjFalse:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg ObjFalse"
proof -
  have d_true: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjTrue"
    by (rule CEV_axiom_proves_ObjTrue)
  have taut:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ObjTrue (Neg ObjFalse)"
  proof (rule CEV_T2f_taut_plus)
    show "prop_tautology \<Gamma> (Imp ObjTrue (Neg ObjFalse))"
      unfolding prop_tautology_def ObjFalse_def
      using typed_ObjTrue
      by (auto intro: has_type.Imp has_type.Neg)
  qed
  show ?thesis
    using d_true taut by (rule CEV_axiom_proves.MP)
qed

definition gd_true_op :: oterm where
  "gd_true_op = Lam Prop ObjTrue"

definition gd_false_op :: oterm where
  "gd_false_op = Lam Prop ObjFalse"

definition gd_box_op :: oterm where
  "gd_box_op = Lam Prop (Eq Prop (Var 0) ObjTrue)"

definition gd_bot_op :: oterm where
  "gd_bot_op = Lam Prop (Eq Prop (Var 0) ObjFalse)"

subsection \<open>Typing\<close>

lemma typed_gd_true_op: "\<Gamma> \<turnstile> gd_true_op : pp_unary_ty"
  unfolding gd_true_op_def pp_unary_ty_def
  using typed_ObjTrue by (rule has_type.Lam)

lemma typed_gd_false_op: "\<Gamma> \<turnstile> gd_false_op : pp_unary_ty"
  unfolding gd_false_op_def pp_unary_ty_def
  using typed_ObjFalse by (rule has_type.Lam)

lemma typed_gd_box_op: "\<Gamma> \<turnstile> gd_box_op : pp_unary_ty"
  unfolding gd_box_op_def pp_unary_ty_def
  by (intro has_type.Lam has_type.Eq has_type.Var typed_ObjTrue)
    (simp add: lookup_def)

lemma typed_gd_bot_op: "\<Gamma> \<turnstile> gd_bot_op : pp_unary_ty"
  unfolding gd_bot_op_def pp_unary_ty_def
  by (intro has_type.Lam has_type.Eq has_type.Var typed_ObjFalse)
    (simp add: lookup_def)

subsection \<open>Purity: all four are closed logical terms\<close>

lemma gd_true_op_purity_axiom:
  "pp_pure pp_unary_ty gd_true_op \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> gd_true_op : pp_unary_ty"
    by (rule typed_gd_true_op)
  show "consts_of gd_true_op = {}"
    by (simp add: gd_true_op_def ObjTrue_def)
  show "pp_pure pp_unary_ty gd_true_op = pp_pure pp_unary_ty gd_true_op"
    by simp
qed

lemma gd_false_op_purity_axiom:
  "pp_pure pp_unary_ty gd_false_op \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> gd_false_op : pp_unary_ty"
    by (rule typed_gd_false_op)
  show "consts_of gd_false_op = {}"
    by (simp add: gd_false_op_def ObjFalse_def ObjTrue_def)
  show "pp_pure pp_unary_ty gd_false_op = pp_pure pp_unary_ty gd_false_op"
    by simp
qed

lemma gd_box_op_purity_axiom:
  "pp_pure pp_unary_ty gd_box_op \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> gd_box_op : pp_unary_ty"
    by (rule typed_gd_box_op)
  show "consts_of gd_box_op = {}"
    by (simp add: gd_box_op_def ObjTrue_def)
  show "pp_pure pp_unary_ty gd_box_op = pp_pure pp_unary_ty gd_box_op"
    by simp
qed

lemma gd_bot_op_purity_axiom:
  "pp_pure pp_unary_ty gd_bot_op \<in> pp_purity_schema"
  unfolding pp_purity_schema_def pp_logical_vocabulary_def
proof (intro CollectI exI conjI)
  show "[] \<turnstile> gd_bot_op : pp_unary_ty"
    by (rule typed_gd_bot_op)
  show "consts_of gd_bot_op = {}"
    by (simp add: gd_bot_op_def ObjFalse_def ObjTrue_def)
  show "pp_pure pp_unary_ty gd_bot_op = pp_pure pp_unary_ty gd_bot_op"
    by simp
qed

subsection \<open>Beta\<close>

lemma gd_true_op_beta:
  "compatible_step beta_contract (App gd_true_op A) ObjTrue"
proof (rule compatible_step.root)
  have step: "beta_contract (App (Lam Prop ObjTrue) A)
      (subst0 A ObjTrue)"
    by (rule beta_contract.beta)
  show "beta_contract (App gd_true_op A) ObjTrue"
    using step by (simp add: gd_true_op_def subst0_def ObjTrue_def)
qed

lemma gd_false_op_beta:
  "compatible_step beta_contract (App gd_false_op A) ObjFalse"
proof (rule compatible_step.root)
  have step: "beta_contract (App (Lam Prop ObjFalse) A)
      (subst0 A ObjFalse)"
    by (rule beta_contract.beta)
  show "beta_contract (App gd_false_op A) ObjFalse"
    using step
    by (simp add: gd_false_op_def subst0_def ObjFalse_def ObjTrue_def)
qed

lemma gd_box_op_beta:
  "compatible_step beta_contract (App gd_box_op A) (Eq Prop A ObjTrue)"
proof (rule compatible_step.root)
  have step: "beta_contract (App (Lam Prop (Eq Prop (Var 0) ObjTrue)) A)
      (subst0 A (Eq Prop (Var 0) ObjTrue))"
    by (rule beta_contract.beta)
  show "beta_contract (App gd_box_op A) (Eq Prop A ObjTrue)"
    using step by (simp add: gd_box_op_def subst0_def ObjTrue_def)
qed

lemma gd_bot_op_beta:
  "compatible_step beta_contract (App gd_bot_op A) (Eq Prop A ObjFalse)"
proof (rule compatible_step.root)
  have step: "beta_contract (App (Lam Prop (Eq Prop (Var 0) ObjFalse)) A)
      (subst0 A (Eq Prop (Var 0) ObjFalse))"
    by (rule beta_contract.beta)
  show "beta_contract (App gd_bot_op A) (Eq Prop A ObjFalse)"
    using step
    by (simp add: gd_bot_op_def subst0_def ObjFalse_def ObjTrue_def)
qed

end
