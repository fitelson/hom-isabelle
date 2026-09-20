theory Bacon_PP_Goodman_M5_Collision
  imports
    
    "Goodman_Legacy_02.Bacon_PP_Goodman_Fun_Prime_Noncontingency"
    "Goodman_Legacy_03.Bacon_PP_Goodman_T2f_Values"
begin

section \<open>Goodman M5: the noncontingency candidate is not injective\<close>

definition pp_M5_collision_operator :: oterm where
  "pp_M5_collision_operator =
    Lam Prop
      (Var 0 \<longleftrightarrow>\<^sub>o pp_noncontingent (Var 0))"

lemma typed_pp_M5_collision_operator:
  "\<Gamma> \<turnstile> pp_M5_collision_operator : pp_unary_ty"
  by (rule infer_type_sound)
    (simp add: pp_M5_collision_operator_def pp_unary_ty_def
      pp_noncontingent_def ObjBox_def ObjTrue_def lookup_def)

lemma pp_M5_collision_operator_beta:
  "compatible_step beta_contract
    (App pp_M5_collision_operator A)
    (A \<longleftrightarrow>\<^sub>o pp_noncontingent A)"
proof -
  let ?B =
    "Var 0 \<longleftrightarrow>\<^sub>o pp_noncontingent (Var 0)"
  have beta:
      "beta_contract (App (Lam Prop ?B) A) (subst0 A ?B)"
    by (rule beta_contract.beta)
  have subst:
      "subst0 A ?B =
        (A \<longleftrightarrow>\<^sub>o pp_noncontingent A)"
    by (simp add: pp_noncontingent_def subst0_def
        ObjBox_def ObjTrue_def)
  have "compatible_step beta_contract
      (App (Lam Prop ?B) A) (subst0 A ?B)"
    using beta by (rule compatible_step.root)
  then show ?thesis
    unfolding pp_M5_collision_operator_def
    using subst by simp
qed

lemma CEVp_M5_propositional:
  assumes typed: "\<Gamma> \<turnstile> A : Prop"
    and valid: "\<forall>v. prop_eval v A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
proof (rule CEV_axiom_proves.Base, rule CEV_prop_tautology)
  show "prop_tautology \<Gamma> A"
    unfolding prop_tautology_def using typed valid by blast
qed

lemma CEVp_M5_app_true:
  assumes O_type: "\<Gamma> \<turnstile> OPR : pp_unary_ty"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
    and R_type: "\<Gamma> \<turnstile> R : Prop"
    and beta: "compatible_step beta_contract (App OPR q) R"
    and dR: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ R"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ App OPR q"
proof -
  have "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App OPR q"
    using O_type q_type R_type beta
      CEV_axiom_from.Theorem[OF dR]
    by (rule CEVs_app_true)
  then show ?thesis
    unfolding CEV_axiom_from_empty_iff .
qed

theorem CEV_Goodman_M5_collision:
  assumes core: "pp_T2_min_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and fun_axiom: "pp_fun_prime r \<in> T"
  defines "N \<equiv> pp_noncontingent r"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Conj
      (Neg (Eq Prop N ObjTrue))
      (Eq Prop
        (App pp_M5_collision_operator N)
        (App pp_M5_collision_operator ObjTrue))"
proof -
  let ?F = "pp_fun_prime r"
  let ?N = "pp_noncontingent r"
  let ?BN = "\<box>\<^sub>o ?N"
  let ?BNN = "\<box>\<^sub>o (Neg ?N)"
  let ?NCN = "pp_noncontingent ?N"
  let ?NCT = "pp_noncontingent ObjTrue"
  let ?BodyN = "?N \<longleftrightarrow>\<^sub>o ?NCN"
  let ?BodyT = "ObjTrue \<longleftrightarrow>\<^sub>o ?NCT"
  let ?AppN = "App pp_M5_collision_operator ?N"
  let ?AppT = "App pp_M5_collision_operator ObjTrue"

  have F_type: "\<Gamma> \<turnstile> ?F : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have N_type: "\<Gamma> \<turnstile> ?N : Prop"
    using r_type by (rule typed_pp_noncontingent)
  have NCN_type: "\<Gamma> \<turnstile> ?NCN : Prop"
    using N_type by (rule typed_pp_noncontingent)
  have NCT_type: "\<Gamma> \<turnstile> ?NCT : Prop"
    using typed_ObjTrue by (rule typed_pp_noncontingent)
  have BN_type: "\<Gamma> \<turnstile> ?BN : Prop"
    using N_type by (rule typed_ObjBox)
  have BNN_type: "\<Gamma> \<turnstile> ?BNN : Prop"
    using N_type by (intro typed_ObjBox has_type.Neg)
  have BodyN_type: "\<Gamma> \<turnstile> ?BodyN : Prop"
    using N_type NCN_type by auto
  have BodyT_type: "\<Gamma> \<turnstile> ?BodyT : Prop"
    using typed_ObjTrue NCT_type by auto
  have AppN_type: "\<Gamma> \<turnstile> ?AppN : Prop"
    using typed_pp_M5_collision_operator N_type
    unfolding pp_unary_ty_def by (rule has_type.App)
  have AppT_type: "\<Gamma> \<turnstile> ?AppT : Prop"
    using typed_pp_M5_collision_operator typed_ObjTrue
    unfolding pp_unary_ty_def by (rule has_type.App)

  have d_F: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ?F"
    using fun_axiom F_type by (rule CEV_axiom_proves.Axiom)
  have d_not_N: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg ?N"
    using d_F CEV_Goodman_T2e_false[OF core r_type]
    by (rule CEV_axiom_proves.MP)
  have d_diamond_N:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<diamond>\<^sub>o ?N"
    using d_F CEV_Goodman_T2e_possible[OF core r_type]
    by (rule CEV_axiom_proves.MP)
  have d_T:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ?BN ?N"
    using CEV_modal_T[OF N_type]
    unfolding modal_T_def
    by (rule CEV_axiom_proves.Base)
  have taut_not_box:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Neg ?N) (Imp (Imp ?BN ?N) (Neg ?BN))"
    by (rule CEVp_M5_propositional)
      (use N_type BN_type in auto)
  have step_not_box:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Imp ?BN ?N) (Neg ?BN)"
    using d_not_N taut_not_box by (rule CEV_axiom_proves.MP)
  have d_not_BN:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg ?BN"
    using d_T step_not_box by (rule CEV_axiom_proves.MP)
  have d_not_BNN:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg ?BNN"
    using d_diamond_N unfolding ObjDiamond_def .
  have taut_not_NCN:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Neg ?BN) (Imp (Neg ?BNN) (Neg ?NCN))"
  proof (rule CEVp_M5_propositional)
    show "\<Gamma> \<turnstile>
        Imp (Neg ?BN)
          (Imp (Neg ?BNN) (Neg ?NCN)) : Prop"
      using BN_type BNN_type NCN_type by auto
    show "\<forall>v. prop_eval v
        (Imp (Neg ?BN)
          (Imp (Neg ?BNN) (Neg ?NCN)))"
      by (simp add: pp_noncontingent_def)
  qed
  have step_not_NCN:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Neg ?BNN) (Neg ?NCN)"
    using d_not_BN taut_not_NCN by (rule CEV_axiom_proves.MP)
  have d_not_NCN:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg ?NCN"
    using d_not_BNN step_not_NCN by (rule CEV_axiom_proves.MP)
  have taut_BodyN:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Neg ?N) (Imp (Neg ?NCN) ?BodyN)"
    by (rule CEVp_M5_propositional)
      (use N_type NCN_type in auto)
  have step_BodyN:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (Neg ?NCN) ?BodyN"
    using d_not_N taut_BodyN by (rule CEV_axiom_proves.MP)
  have d_BodyN: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ?BodyN"
    using d_not_NCN step_BodyN by (rule CEV_axiom_proves.MP)

  have d_box_true:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o ObjTrue"
    using CEV_axiom_proves_ObjTrue
    by (rule CEV_axiom_necessitation)
  have taut_NCT:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp (\<box>\<^sub>o ObjTrue) ?NCT"
  proof (rule CEVp_M5_propositional)
    have box_true_type:
        "\<Gamma> \<turnstile> \<box>\<^sub>o ObjTrue : Prop"
      using typed_ObjTrue by (rule typed_ObjBox)
    show "\<Gamma> \<turnstile>
        Imp (\<box>\<^sub>o ObjTrue) ?NCT : Prop"
      using box_true_type NCT_type by auto
    show "\<forall>v. prop_eval v
        (Imp (\<box>\<^sub>o ObjTrue) ?NCT)"
      by (simp add: pp_noncontingent_def)
  qed
  have d_NCT: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ?NCT"
    using d_box_true taut_NCT by (rule CEV_axiom_proves.MP)
  have taut_BodyT:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ObjTrue (Imp ?NCT ?BodyT)"
  proof (rule CEVp_M5_propositional)
    have inner_type:
        "\<Gamma> \<turnstile> Imp ?NCT ?BodyT : Prop"
      using NCT_type BodyT_type by (rule has_type.Imp)
    show "\<Gamma> \<turnstile>
        Imp ObjTrue (Imp ?NCT ?BodyT) : Prop"
      using typed_ObjTrue inner_type by (rule has_type.Imp)
    show "\<forall>v. prop_eval v
        (Imp ObjTrue (Imp ?NCT ?BodyT))"
      by simp
  qed
  have step_BodyT:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Imp ?NCT ?BodyT"
    using CEV_axiom_proves_ObjTrue taut_BodyT
    by (rule CEV_axiom_proves.MP)
  have d_BodyT: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ?BodyT"
    using d_NCT step_BodyT by (rule CEV_axiom_proves.MP)

  have d_AppN: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ?AppN"
    using typed_pp_M5_collision_operator N_type BodyN_type
      pp_M5_collision_operator_beta d_BodyN
    by (rule CEVp_M5_app_true)
  have d_AppT: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ?AppT"
    using typed_pp_M5_collision_operator typed_ObjTrue BodyT_type
      pp_M5_collision_operator_beta d_BodyT
    by (rule CEVp_M5_app_true)
  have app_bicond:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        (?AppN \<longleftrightarrow>\<^sub>o ?AppT)"
    using d_AppN d_AppT
    by (rule CEV_axiom_biconditional_of_theorems)
  have app_eq:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop ?AppN ?AppT"
    using AppN_type AppT_type app_bicond
    by (rule CEV_axiom_zeroary_equivalence)
  have distinct:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Neg (Eq Prop ?N ObjTrue)"
    using d_not_BN unfolding ObjBox_def .
  have result:
      "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
        Conj (Neg (Eq Prop ?N ObjTrue))
          (Eq Prop ?AppN ?AppT)"
    using distinct app_eq by (rule CEV_axiom_conj_intro)
  show ?thesis
    unfolding N_def using result .
qed

text \<open>
  The displayed conjunction gives explicit unequal inputs, namely
  noncontingency of the fundamental proposition and truth, on which
  \<open>\<lambda>p. p \<longleftrightarrow> NC(p)\<close> has identical values.  Hence the
  candidate is not injective in the theory obtained by naming a
  \<open>fun'\<close> witness.
\<close>

end
