theory Bacon_PP_Goodman_T2f_Pairwise
  imports 
    "Goodman_Legacy_03.Bacon_PP_Goodman_T2f_Values"
begin

section \<open>The fifteen operator inequalities and Goodman T2f\<close>

subsection \<open>Purity of the six operators in the local layer\<close>

lemma CEVs_pure_op:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and ax: "pp_pure pp_unary_ty A \<in> pp_purity_schema"
    and A_type: "\<Gamma> \<turnstile> A : pp_unary_ty"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty A"
proof (rule CEV_axiom_from.Theorem)
  have mem: "pp_pure pp_unary_ty A \<in> T"
    using ax core unfolding pp_T6_core_PP_axioms_def by blast
  show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_pure pp_unary_ty A"
    using mem typed_pp_pure[OF A_type] by (rule CEV_axiom_proves.Axiom)
qed

lemma pure_Ktop:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty gd_true_op"
  using core gd_true_op_purity_axiom typed_gd_true_op by (rule CEVs_pure_op)

lemma pure_Kbot:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty gd_false_op"
  using core gd_false_op_purity_axiom typed_gd_false_op by (rule CEVs_pure_op)

lemma pure_Id:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty pp_identity_operator"
  using core pp_identity_operator_purity_axiom typed_pp_identity_operator by (rule CEVs_pure_op)

lemma pure_Neg:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty pp_negation_operator"
  using core pp_negation_operator_purity_axiom typed_pp_negation_operator by (rule CEVs_pure_op)

lemma pure_Box:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty gd_box_op"
  using core gd_box_op_purity_axiom typed_gd_box_op by (rule CEVs_pure_op)

lemma pure_Bot:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty gd_bot_op"
  using core gd_bot_op_purity_axiom typed_gd_bot_op by (rule CEVs_pure_op)

subsection \<open>The thirteen inequalities separated at \<open>\<top>\<close> or \<open>\<bottom>\<close>\<close>

lemma opneq_Ktop_Kbot:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_true_op gd_false_op)"
  using typed_gd_true_op typed_gd_false_op typed_ObjTrue val_Ktop_at_true val_Kbot_at_true
  by (rule CEVs_operator_neq_via_witness)

lemma opneq_Ktop_Id:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_true_op pp_identity_operator)"
  using typed_gd_true_op typed_pp_identity_operator typed_ObjFalse val_Ktop_at_false val_Id_at_false
  by (rule CEVs_operator_neq_via_witness)

lemma opneq_Ktop_Neg:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_true_op pp_negation_operator)"
  using typed_gd_true_op typed_pp_negation_operator typed_ObjTrue val_Ktop_at_true val_Neg_at_true
  by (rule CEVs_operator_neq_via_witness)

lemma opneq_Ktop_Box:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_true_op gd_box_op)"
  using typed_gd_true_op typed_gd_box_op typed_ObjFalse val_Ktop_at_false val_Box_at_false
  by (rule CEVs_operator_neq_via_witness)

lemma opneq_Ktop_Bot:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_true_op gd_bot_op)"
  using typed_gd_true_op typed_gd_bot_op typed_ObjTrue val_Ktop_at_true val_Bot_at_true
  by (rule CEVs_operator_neq_via_witness)

lemma opneq_Kbot_Id:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_false_op pp_identity_operator)"
proof (rule CEVs_neq_sym)
  show "\<Gamma> \<turnstile> pp_identity_operator : pp_unary_ty" by (rule typed_pp_identity_operator)
  show "\<Gamma> \<turnstile> gd_false_op : pp_unary_ty" by (rule typed_gd_false_op)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty pp_identity_operator gd_false_op)"
    using typed_pp_identity_operator typed_gd_false_op typed_ObjTrue val_Id_at_true val_Kbot_at_true
    by (rule CEVs_operator_neq_via_witness)
qed

lemma opneq_Kbot_Neg:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_false_op pp_negation_operator)"
proof (rule CEVs_neq_sym)
  show "\<Gamma> \<turnstile> pp_negation_operator : pp_unary_ty" by (rule typed_pp_negation_operator)
  show "\<Gamma> \<turnstile> gd_false_op : pp_unary_ty" by (rule typed_gd_false_op)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty pp_negation_operator gd_false_op)"
    using typed_pp_negation_operator typed_gd_false_op typed_ObjFalse val_Neg_at_false val_Kbot_at_false
    by (rule CEVs_operator_neq_via_witness)
qed

lemma opneq_Kbot_Box:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_false_op gd_box_op)"
proof (rule CEVs_neq_sym)
  show "\<Gamma> \<turnstile> gd_box_op : pp_unary_ty" by (rule typed_gd_box_op)
  show "\<Gamma> \<turnstile> gd_false_op : pp_unary_ty" by (rule typed_gd_false_op)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_box_op gd_false_op)"
    using typed_gd_box_op typed_gd_false_op typed_ObjTrue val_Box_at_true val_Kbot_at_true
    by (rule CEVs_operator_neq_via_witness)
qed

lemma opneq_Kbot_Bot:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_false_op gd_bot_op)"
proof (rule CEVs_neq_sym)
  show "\<Gamma> \<turnstile> gd_bot_op : pp_unary_ty" by (rule typed_gd_bot_op)
  show "\<Gamma> \<turnstile> gd_false_op : pp_unary_ty" by (rule typed_gd_false_op)
  show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_bot_op gd_false_op)"
    using typed_gd_bot_op typed_gd_false_op typed_ObjFalse val_Bot_at_false val_Kbot_at_false
    by (rule CEVs_operator_neq_via_witness)
qed

lemma opneq_Id_Neg:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty pp_identity_operator pp_negation_operator)"
  using typed_pp_identity_operator typed_pp_negation_operator typed_ObjTrue val_Id_at_true val_Neg_at_true
  by (rule CEVs_operator_neq_via_witness)

lemma opneq_Id_Bot:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty pp_identity_operator gd_bot_op)"
  using typed_pp_identity_operator typed_gd_bot_op typed_ObjTrue val_Id_at_true val_Bot_at_true
  by (rule CEVs_operator_neq_via_witness)

lemma opneq_Neg_Box:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty pp_negation_operator gd_box_op)"
  using typed_pp_negation_operator typed_gd_box_op typed_ObjFalse val_Neg_at_false val_Box_at_false
  by (rule CEVs_operator_neq_via_witness)

lemma opneq_Box_Bot:
  "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_box_op gd_bot_op)"
  using typed_gd_box_op typed_gd_bot_op typed_ObjTrue val_Box_at_true val_Bot_at_true
  by (rule CEVs_operator_neq_via_witness)

subsection \<open>The two inequalities that require T2e\<close>

lemma opneq_Id_Box:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and d_F: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime r"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty pp_identity_operator gd_box_op)"
proof -
  let ?NC = "pp_noncontingent r"
  let ?w = "Neg (pp_noncontingent r)"
  have NC_type: "\<Gamma> \<turnstile> ?NC : Prop"
    using r_type by (rule typed_pp_noncontingent)
  have nNC_type: "\<Gamma> \<turnstile> Neg ?NC : Prop"
    using NC_type by (rule has_type.Neg)
  have f1: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?NC"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T2e_false[
          OF pp_T2_min_axioms_into_T6_extension[OF core] r_type]]
    by (rule CEV_axiom_from.MP)
  have f2: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o ?NC"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T2e_possible[
          OF pp_T2_min_axioms_into_T6_extension[OF core] r_type]]
    by (rule CEV_axiom_from.MP)
  have dA: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App pp_identity_operator ?w"
    using typed_pp_identity_operator nNC_type nNC_type
      pp_identity_apply_beta f1
    by (rule CEVs_app_true)
  have dnB: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App gd_box_op ?w)"
  proof (rule CEVs_app_false)
    show "\<Gamma> \<turnstile> gd_box_op : pp_unary_ty" by (rule typed_gd_box_op)
    show "\<Gamma> \<turnstile> ?w : Prop" by (rule nNC_type)
    show "\<Gamma> \<turnstile> Eq Prop ?w ObjTrue : Prop"
      using nNC_type typed_ObjTrue by (rule has_type.Eq)
    show "compatible_step beta_contract (App gd_box_op ?w)
        (Eq Prop ?w ObjTrue)"
      by (rule gd_box_op_beta)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq Prop ?w ObjTrue)"
      using f2 unfolding ObjDiamond_def ObjBox_def .
  qed
  show ?thesis
    using typed_pp_identity_operator typed_gd_box_op nNC_type dA dnB
    by (rule CEVs_operator_neq_via_witness)
qed

lemma opneq_Neg_Bot:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and d_F: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime r"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty pp_negation_operator gd_bot_op)"
proof -
  let ?NC = "pp_noncontingent r"
  let ?w = "pp_noncontingent r"
  have NC_type: "\<Gamma> \<turnstile> ?NC : Prop"
    using r_type by (rule typed_pp_noncontingent)
  have nNC_type: "\<Gamma> \<turnstile> Neg ?NC : Prop"
    using NC_type by (rule has_type.Neg)
  have f1: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?NC"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T2e_false[
          OF pp_T2_min_axioms_into_T6_extension[OF core] r_type]]
    by (rule CEV_axiom_from.MP)
  have f2: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o ?NC"
    using d_F
      CEV_axiom_from.Theorem[
        OF CEV_Goodman_T2e_possible[
          OF pp_T2_min_axioms_into_T6_extension[OF core] r_type]]
    by (rule CEV_axiom_from.MP)
  have dA: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App pp_negation_operator ?w"
    using typed_pp_negation_operator NC_type nNC_type
      pp_negation_apply_beta f1
    by (rule CEVs_app_true)
  have dnB: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App gd_bot_op ?w)"
  proof (rule CEVs_app_false)
    show "\<Gamma> \<turnstile> gd_bot_op : pp_unary_ty" by (rule typed_gd_bot_op)
    show "\<Gamma> \<turnstile> ?w : Prop" by (rule NC_type)
    show "\<Gamma> \<turnstile> Eq Prop ?w ObjFalse : Prop"
      using NC_type typed_ObjFalse by (rule has_type.Eq)
    show "compatible_step beta_contract (App gd_bot_op ?w)
        (Eq Prop ?w ObjFalse)"
      by (rule gd_bot_op_beta)
    show "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq Prop ?w ObjFalse)"
      using NC_type f2 by (rule CEVs_possible_imp_neq_ObjFalse)
  qed
  show ?thesis
    using typed_pp_negation_operator typed_gd_bot_op NC_type dA dnB
    by (rule CEVs_operator_neq_via_witness)
qed

subsection \<open>Goodman T2f: the fifteen proposition inequalities\<close>

theorem T2f_Ktop_Kbot:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (ObjTrue) (ObjFalse)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App gd_true_op r : Prop"
    using typed_gd_true_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App gd_false_op r : Prop"
    using typed_gd_false_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_true_op gd_false_op)"
    by (rule opneq_Ktop_Kbot)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App gd_true_op r) (App gd_false_op r))"
    using r_type typed_gd_true_op typed_gd_false_op pure_Ktop[OF core] pure_Kbot[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_true_op r) (ObjTrue)"
    using appA_type typed_ObjTrue gd_true_op_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_false_op r) (ObjFalse)"
    using appB_type typed_ObjFalse gd_false_op_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjTrue) (ObjFalse))"
    using appA_type appB_type typed_ObjTrue typed_ObjFalse betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Ktop_Id:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (ObjTrue) (r)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App gd_true_op r : Prop"
    using typed_gd_true_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App pp_identity_operator r : Prop"
    using typed_pp_identity_operator r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_true_op pp_identity_operator)"
    by (rule opneq_Ktop_Id)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App gd_true_op r) (App pp_identity_operator r))"
    using r_type typed_gd_true_op typed_pp_identity_operator pure_Ktop[OF core] pure_Id[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_true_op r) (ObjTrue)"
    using appA_type typed_ObjTrue gd_true_op_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_identity_operator r) (r)"
    using appB_type r_type pp_identity_apply_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjTrue) (r))"
    using appA_type appB_type typed_ObjTrue r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Ktop_Neg:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (ObjTrue) (Neg r)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App gd_true_op r : Prop"
    using typed_gd_true_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App pp_negation_operator r : Prop"
    using typed_pp_negation_operator r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_true_op pp_negation_operator)"
    by (rule opneq_Ktop_Neg)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App gd_true_op r) (App pp_negation_operator r))"
    using r_type typed_gd_true_op typed_pp_negation_operator pure_Ktop[OF core] pure_Neg[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_true_op r) (ObjTrue)"
    using appA_type typed_ObjTrue gd_true_op_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_negation_operator r) (Neg r)"
    using appB_type neg_r_type pp_negation_apply_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjTrue) (Neg r))"
    using appA_type appB_type typed_ObjTrue neg_r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Ktop_Box:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (ObjTrue) (Eq Prop r ObjTrue)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App gd_true_op r : Prop"
    using typed_gd_true_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App gd_box_op r : Prop"
    using typed_gd_box_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_true_op gd_box_op)"
    by (rule opneq_Ktop_Box)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App gd_true_op r) (App gd_box_op r))"
    using r_type typed_gd_true_op typed_gd_box_op pure_Ktop[OF core] pure_Box[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_true_op r) (ObjTrue)"
    using appA_type typed_ObjTrue gd_true_op_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_box_op r) (Eq Prop r ObjTrue)"
    using appB_type box_r_type gd_box_op_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjTrue) (Eq Prop r ObjTrue))"
    using appA_type appB_type typed_ObjTrue box_r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Ktop_Bot:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (ObjTrue) (Eq Prop r ObjFalse)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App gd_true_op r : Prop"
    using typed_gd_true_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App gd_bot_op r : Prop"
    using typed_gd_bot_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_true_op gd_bot_op)"
    by (rule opneq_Ktop_Bot)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App gd_true_op r) (App gd_bot_op r))"
    using r_type typed_gd_true_op typed_gd_bot_op pure_Ktop[OF core] pure_Bot[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_true_op r) (ObjTrue)"
    using appA_type typed_ObjTrue gd_true_op_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_bot_op r) (Eq Prop r ObjFalse)"
    using appB_type bot_r_type gd_bot_op_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjTrue) (Eq Prop r ObjFalse))"
    using appA_type appB_type typed_ObjTrue bot_r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Kbot_Id:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (ObjFalse) (r)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App gd_false_op r : Prop"
    using typed_gd_false_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App pp_identity_operator r : Prop"
    using typed_pp_identity_operator r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_false_op pp_identity_operator)"
    by (rule opneq_Kbot_Id)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App gd_false_op r) (App pp_identity_operator r))"
    using r_type typed_gd_false_op typed_pp_identity_operator pure_Kbot[OF core] pure_Id[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_false_op r) (ObjFalse)"
    using appA_type typed_ObjFalse gd_false_op_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_identity_operator r) (r)"
    using appB_type r_type pp_identity_apply_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjFalse) (r))"
    using appA_type appB_type typed_ObjFalse r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Kbot_Neg:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (ObjFalse) (Neg r)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App gd_false_op r : Prop"
    using typed_gd_false_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App pp_negation_operator r : Prop"
    using typed_pp_negation_operator r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_false_op pp_negation_operator)"
    by (rule opneq_Kbot_Neg)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App gd_false_op r) (App pp_negation_operator r))"
    using r_type typed_gd_false_op typed_pp_negation_operator pure_Kbot[OF core] pure_Neg[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_false_op r) (ObjFalse)"
    using appA_type typed_ObjFalse gd_false_op_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_negation_operator r) (Neg r)"
    using appB_type neg_r_type pp_negation_apply_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjFalse) (Neg r))"
    using appA_type appB_type typed_ObjFalse neg_r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Kbot_Box:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (ObjFalse) (Eq Prop r ObjTrue)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App gd_false_op r : Prop"
    using typed_gd_false_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App gd_box_op r : Prop"
    using typed_gd_box_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_false_op gd_box_op)"
    by (rule opneq_Kbot_Box)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App gd_false_op r) (App gd_box_op r))"
    using r_type typed_gd_false_op typed_gd_box_op pure_Kbot[OF core] pure_Box[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_false_op r) (ObjFalse)"
    using appA_type typed_ObjFalse gd_false_op_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_box_op r) (Eq Prop r ObjTrue)"
    using appB_type box_r_type gd_box_op_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjFalse) (Eq Prop r ObjTrue))"
    using appA_type appB_type typed_ObjFalse box_r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Kbot_Bot:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (ObjFalse) (Eq Prop r ObjFalse)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App gd_false_op r : Prop"
    using typed_gd_false_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App gd_bot_op r : Prop"
    using typed_gd_bot_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_false_op gd_bot_op)"
    by (rule opneq_Kbot_Bot)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App gd_false_op r) (App gd_bot_op r))"
    using r_type typed_gd_false_op typed_gd_bot_op pure_Kbot[OF core] pure_Bot[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_false_op r) (ObjFalse)"
    using appA_type typed_ObjFalse gd_false_op_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_bot_op r) (Eq Prop r ObjFalse)"
    using appB_type bot_r_type gd_bot_op_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (ObjFalse) (Eq Prop r ObjFalse))"
    using appA_type appB_type typed_ObjFalse bot_r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Id_Neg:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (r) (Neg r)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App pp_identity_operator r : Prop"
    using typed_pp_identity_operator r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App pp_negation_operator r : Prop"
    using typed_pp_negation_operator r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty pp_identity_operator pp_negation_operator)"
    by (rule opneq_Id_Neg)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App pp_identity_operator r) (App pp_negation_operator r))"
    using r_type typed_pp_identity_operator typed_pp_negation_operator pure_Id[OF core] pure_Neg[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_identity_operator r) (r)"
    using appA_type r_type pp_identity_apply_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_negation_operator r) (Neg r)"
    using appB_type neg_r_type pp_negation_apply_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (r) (Neg r))"
    using appA_type appB_type r_type neg_r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Id_Box:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (r) (Eq Prop r ObjTrue)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App pp_identity_operator r : Prop"
    using typed_pp_identity_operator r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App gd_box_op r : Prop"
    using typed_gd_box_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty pp_identity_operator gd_box_op)"
    using core r_type d_F by (rule opneq_Id_Box)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App pp_identity_operator r) (App gd_box_op r))"
    using r_type typed_pp_identity_operator typed_gd_box_op pure_Id[OF core] pure_Box[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_identity_operator r) (r)"
    using appA_type r_type pp_identity_apply_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_box_op r) (Eq Prop r ObjTrue)"
    using appB_type box_r_type gd_box_op_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (r) (Eq Prop r ObjTrue))"
    using appA_type appB_type r_type box_r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Id_Bot:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (r) (Eq Prop r ObjFalse)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App pp_identity_operator r : Prop"
    using typed_pp_identity_operator r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App gd_bot_op r : Prop"
    using typed_gd_bot_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty pp_identity_operator gd_bot_op)"
    by (rule opneq_Id_Bot)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App pp_identity_operator r) (App gd_bot_op r))"
    using r_type typed_pp_identity_operator typed_gd_bot_op pure_Id[OF core] pure_Bot[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_identity_operator r) (r)"
    using appA_type r_type pp_identity_apply_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_bot_op r) (Eq Prop r ObjFalse)"
    using appB_type bot_r_type gd_bot_op_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (r) (Eq Prop r ObjFalse))"
    using appA_type appB_type r_type bot_r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Neg_Box:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (Neg r) (Eq Prop r ObjTrue)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App pp_negation_operator r : Prop"
    using typed_pp_negation_operator r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App gd_box_op r : Prop"
    using typed_gd_box_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty pp_negation_operator gd_box_op)"
    by (rule opneq_Neg_Box)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App pp_negation_operator r) (App gd_box_op r))"
    using r_type typed_pp_negation_operator typed_gd_box_op pure_Neg[OF core] pure_Box[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_negation_operator r) (Neg r)"
    using appA_type neg_r_type pp_negation_apply_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_box_op r) (Eq Prop r ObjTrue)"
    using appB_type box_r_type gd_box_op_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (Neg r) (Eq Prop r ObjTrue))"
    using appA_type appB_type neg_r_type box_r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Neg_Bot:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (Neg r) (Eq Prop r ObjFalse)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App pp_negation_operator r : Prop"
    using typed_pp_negation_operator r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App gd_bot_op r : Prop"
    using typed_gd_bot_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty pp_negation_operator gd_bot_op)"
    using core r_type d_F by (rule opneq_Neg_Bot)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App pp_negation_operator r) (App gd_bot_op r))"
    using r_type typed_pp_negation_operator typed_gd_bot_op pure_Neg[OF core] pure_Bot[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_negation_operator r) (Neg r)"
    using appA_type neg_r_type pp_negation_apply_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_bot_op r) (Eq Prop r ObjFalse)"
    using appB_type bot_r_type gd_bot_op_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (Neg r) (Eq Prop r ObjFalse))"
    using appA_type appB_type neg_r_type bot_r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

theorem T2f_Box_Bot:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Imp (pp_fun_prime r) (Neg (Eq Prop (Eq Prop r ObjTrue) (Eq Prop r ObjFalse)))"
proof -
  let ?F = "pp_fun_prime r"
  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have neg_r_type: "\<Gamma> \<turnstile> Neg r : Prop"
    using r_type by (rule has_type.Neg)
  have box_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have bot_r_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have appA_type: "\<Gamma> \<turnstile> App gd_box_op r : Prop"
    using typed_gd_box_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appB_type: "\<Gamma> \<turnstile> App gd_bot_op r : Prop"
    using typed_gd_bot_op r_type unfolding pp_unary_ty_def by (rule has_type.App)
  have d_F: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?F"
    using F_type by (intro CEV_axiom_from.Assumption) simp
  have opneq: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty gd_box_op gd_bot_op)"
    by (rule opneq_Box_Bot)
  have sep: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (App gd_box_op r) (App gd_bot_op r))"
    using r_type typed_gd_box_op typed_gd_bot_op pure_Box[OF core] pure_Bot[OF core]
      opneq d_F
    by (rule CEVs_fun_prime_separates)
  have betaA: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_box_op r) (Eq Prop r ObjTrue)"
    using appA_type box_r_type gd_box_op_beta by (rule CEVs_eq_of_beta)
  have betaB: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App gd_bot_op r) (Eq Prop r ObjFalse)"
    using appB_type bot_r_type gd_bot_op_beta by (rule CEVs_eq_of_beta)
  have res: "\<Gamma> ; T ; {?F} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Neg (Eq Prop (Eq Prop r ObjTrue) (Eq Prop r ObjFalse))"
    using appA_type appB_type box_r_type bot_r_type betaA betaB sep
    by (rule CEVs_neq_transport)
  show ?thesis
    using F_type res by (rule CEV_axiom_from_singleton_imp)
qed

end
