theory Bacon_PP_Goodman_T2f_Values
  imports 
    "Goodman_Legacy_03.Bacon_PP_Goodman_T2f_Separation"
begin

section \<open>Truth values of the six operators at \<open>\<top>\<close> and \<open>\<bottom>\<close>\<close>

subsection \<open>Generic transport across a beta step\<close>

lemma CEVs_app_true:
  assumes O_type: "\<Gamma> \<turnstile> OPR : pp_unary_ty"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
    and R_type: "\<Gamma> \<turnstile> R : Prop"
    and beta: "compatible_step beta_contract (App OPR q) R"
    and dR: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s R"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App OPR q"
proof -
  have app_type: "\<Gamma> \<turnstile> App OPR q : Prop"
    using O_type q_type unfolding pp_unary_ty_def by (rule has_type.App)
  have eq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App OPR q) R"
    using app_type R_type beta by (rule CEVs_eq_of_beta)
  show ?thesis
    using app_type R_type dR eq by (rule CEVs_eq_prop_intro)
qed

lemma CEVs_app_false:
  assumes O_type: "\<Gamma> \<turnstile> OPR : pp_unary_ty"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
    and R_type: "\<Gamma> \<turnstile> R : Prop"
    and beta: "compatible_step beta_contract (App OPR q) R"
    and dnR: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg R"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App OPR q)"
proof -
  have app_type: "\<Gamma> \<turnstile> App OPR q : Prop"
    using O_type q_type unfolding pp_unary_ty_def by (rule has_type.App)
  have eq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (App OPR q) R"
    using app_type R_type beta by (rule CEVs_eq_of_beta)
  have neq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg (App OPR q)) (Neg R)"
    using app_type R_type eq by (rule CEVs_eq_neg_cong)
  have nA_type: "\<Gamma> \<turnstile> Neg (App OPR q) : Prop"
    using app_type by (rule has_type.Neg)
  have nR_type: "\<Gamma> \<turnstile> Neg R : Prop"
    using R_type by (rule has_type.Neg)
  show ?thesis
    using nA_type nR_type dnR neq by (rule CEVs_eq_prop_intro)
qed

subsection \<open>The basic decided propositions\<close>

lemma CEVs_ObjTrue: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjTrue"
  using CEV_axiom_proves_ObjTrue by (rule CEV_axiom_from.Theorem)

lemma CEVs_not_ObjFalse: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ObjFalse"
  using CEVp_not_ObjFalse by (rule CEV_axiom_from.Theorem)

lemma CEVs_true_neq_false:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Neg (Eq Prop ObjTrue ObjFalse)"
proof (rule CEV_axiom_from.Theorem, rule CEV_axiom_proves.Base)
  show "\<Gamma> \<turnstile>\<^sub>CEV Neg (Eq Prop ObjTrue ObjFalse)"
    using CEV_bare_no_proposition_identical_to_its_negation[
      OF typed_ObjTrue, where \<Gamma> = \<Gamma>]
    unfolding ObjFalse_def .
qed

lemma CEVs_neq_sym:
  assumes X_type: "\<Gamma> \<turnstile> X : \<sigma>"
    and Y_type: "\<Gamma> \<turnstile> Y : \<sigma>"
    and neq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq \<sigma> X Y)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq \<sigma> Y X)"
proof -
  let ?E = "Eq \<sigma> Y X"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using Y_type X_type by (rule has_type.Eq)
  have sub: "S \<subseteq> insert ?E S" by blast
  have d_E: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using E_type by (intro CEV_axiom_from.Assumption) simp
  have flip: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> X Y"
    using Y_type X_type d_E by (rule CEV_axiom_from_eq_sym)
  have neq': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq \<sigma> X Y)"
    using neq sub by (rule CEV_axiom_from_mono)
  have d_false: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using flip neq' by (rule CEV_axiom_from_contradiction)
  have imp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?E ObjFalse"
    using E_type d_false by (rule CEV_axiom_from_deduction)
  have to_neg:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (Imp ?E ObjFalse) (Neg ?E)"
    using CEV_proves_imp_false_to_neg[OF E_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis using imp to_neg by (rule CEV_axiom_from.MP)
qed

lemma CEVs_false_neq_true:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Neg (Eq Prop ObjFalse ObjTrue)"
  using typed_ObjTrue typed_ObjFalse CEVs_true_neq_false
  by (rule CEVs_neq_sym)

subsection \<open>The twelve values\<close>

lemma val_Ktop_at_true:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gd_true_op ObjTrue"
  using typed_gd_true_op typed_ObjTrue typed_ObjTrue gd_true_op_beta
    CEVs_ObjTrue
  by (rule CEVs_app_true)

lemma val_Ktop_at_false:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gd_true_op ObjFalse"
  using typed_gd_true_op typed_ObjFalse typed_ObjTrue gd_true_op_beta
    CEVs_ObjTrue
  by (rule CEVs_app_true)

lemma val_Kbot_at_true:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App gd_false_op ObjTrue)"
  using typed_gd_false_op typed_ObjTrue typed_ObjFalse gd_false_op_beta
    CEVs_not_ObjFalse
  by (rule CEVs_app_false)

lemma val_Kbot_at_false:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App gd_false_op ObjFalse)"
  using typed_gd_false_op typed_ObjFalse typed_ObjFalse gd_false_op_beta
    CEVs_not_ObjFalse
  by (rule CEVs_app_false)

lemma val_Id_at_true:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App pp_identity_operator ObjTrue"
  using typed_pp_identity_operator typed_ObjTrue typed_ObjTrue
    pp_identity_apply_beta CEVs_ObjTrue
  by (rule CEVs_app_true)

lemma val_Id_at_false:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App pp_identity_operator ObjFalse)"
  using typed_pp_identity_operator typed_ObjFalse typed_ObjFalse
    pp_identity_apply_beta CEVs_not_ObjFalse
  by (rule CEVs_app_false)

lemma val_Neg_at_true:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App pp_negation_operator ObjTrue)"
proof (rule CEVs_app_false)
  show "\<Gamma> \<turnstile> pp_negation_operator : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  show "\<Gamma> \<turnstile> ObjTrue : Prop" by (rule typed_ObjTrue)
  show "\<Gamma> \<turnstile> Neg ObjTrue : Prop"
    using typed_ObjFalse unfolding ObjFalse_def .
  show "compatible_step beta_contract
      (App pp_negation_operator ObjTrue) (Neg ObjTrue)"
    by (rule pp_negation_apply_beta)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Neg ObjTrue)"
    using CEVs_not_ObjFalse unfolding ObjFalse_def .
qed

lemma val_Neg_at_false:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App pp_negation_operator ObjFalse"
proof (rule CEVs_app_true)
  show "\<Gamma> \<turnstile> pp_negation_operator : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  show "\<Gamma> \<turnstile> ObjFalse : Prop" by (rule typed_ObjFalse)
  show "\<Gamma> \<turnstile> Neg ObjFalse : Prop"
    using typed_ObjFalse by (rule has_type.Neg)
  show "compatible_step beta_contract
      (App pp_negation_operator ObjFalse) (Neg ObjFalse)"
    by (rule pp_negation_apply_beta)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ObjFalse"
    by (rule CEVs_not_ObjFalse)
qed

lemma val_Box_at_true:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gd_box_op ObjTrue"
proof (rule CEVs_app_true)
  show "\<Gamma> \<turnstile> gd_box_op : pp_unary_ty" by (rule typed_gd_box_op)
  show "\<Gamma> \<turnstile> ObjTrue : Prop" by (rule typed_ObjTrue)
  show "\<Gamma> \<turnstile> Eq Prop ObjTrue ObjTrue : Prop"
    using typed_ObjTrue typed_ObjTrue by (rule has_type.Eq)
  show "compatible_step beta_contract (App gd_box_op ObjTrue)
      (Eq Prop ObjTrue ObjTrue)"
    by (rule gd_box_op_beta)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ObjTrue ObjTrue"
    using typed_ObjTrue by (rule CEVs_eq_refl)
qed

lemma val_Box_at_false:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App gd_box_op ObjFalse)"
proof (rule CEVs_app_false)
  show "\<Gamma> \<turnstile> gd_box_op : pp_unary_ty" by (rule typed_gd_box_op)
  show "\<Gamma> \<turnstile> ObjFalse : Prop" by (rule typed_ObjFalse)
  show "\<Gamma> \<turnstile> Eq Prop ObjFalse ObjTrue : Prop"
    using typed_ObjFalse typed_ObjTrue by (rule has_type.Eq)
  show "compatible_step beta_contract (App gd_box_op ObjFalse)
      (Eq Prop ObjFalse ObjTrue)"
    by (rule gd_box_op_beta)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq Prop ObjFalse ObjTrue)"
    by (rule CEVs_false_neq_true)
qed

lemma val_Bot_at_true:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App gd_bot_op ObjTrue)"
proof (rule CEVs_app_false)
  show "\<Gamma> \<turnstile> gd_bot_op : pp_unary_ty" by (rule typed_gd_bot_op)
  show "\<Gamma> \<turnstile> ObjTrue : Prop" by (rule typed_ObjTrue)
  show "\<Gamma> \<turnstile> Eq Prop ObjTrue ObjFalse : Prop"
    using typed_ObjTrue typed_ObjFalse by (rule has_type.Eq)
  show "compatible_step beta_contract (App gd_bot_op ObjTrue)
      (Eq Prop ObjTrue ObjFalse)"
    by (rule gd_bot_op_beta)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq Prop ObjTrue ObjFalse)"
    by (rule CEVs_true_neq_false)
qed

lemma val_Bot_at_false:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App gd_bot_op ObjFalse"
proof (rule CEVs_app_true)
  show "\<Gamma> \<turnstile> gd_bot_op : pp_unary_ty" by (rule typed_gd_bot_op)
  show "\<Gamma> \<turnstile> ObjFalse : Prop" by (rule typed_ObjFalse)
  show "\<Gamma> \<turnstile> Eq Prop ObjFalse ObjFalse : Prop"
    using typed_ObjFalse typed_ObjFalse by (rule has_type.Eq)
  show "compatible_step beta_contract (App gd_bot_op ObjFalse)
      (Eq Prop ObjFalse ObjFalse)"
    by (rule gd_bot_op_beta)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop ObjFalse ObjFalse"
    using typed_ObjFalse by (rule CEVs_eq_refl)
qed

end

