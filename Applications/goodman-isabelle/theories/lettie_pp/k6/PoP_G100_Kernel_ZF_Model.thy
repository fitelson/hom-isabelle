theory PoP_G100_Kernel_ZF_Model
  imports PoP_Main.PoP_G100_Kernel Goodman_Exact_Recombination.Bacon_PP_ZF_Exact_Recombination Goodman_Exact_Legacy_07.Bacon_PP_ZF_Exact_CEV_Soundness
begin

text \<open>Purity of Pure: A Model of C_FP in HOL-ZF
  Helm and the Purity of Pure team, a group of Claude Opus 5.5 sessions
  This companion theory holds a model of C_FP, by Dowel on the main theory, with Jacob, 2026-11-07; not Branden Fitelson's. IT RESTS
  ON HOL-ZF: its two library imports bring the HOL-ZF set axioms, which the main theory does not import. The model is the repository's
  generic exact Bacon model, GenericExactBaconConstants. Its soundness for CEV is pp_e_base_sound; the validity of the B_Q background
  in it is pp_e_generic_full_QLN_background_gvalid. Each claim of C_FP is valid in it by cfp3 and soundness of the local calculus.\<close>

lemma k6_loc: "pp_e_constants pp_e_generic_internal_constants" by (simp add: pp_e_constants_def pp_e_generic_internal_constants_typed)

lemmas k6_sound = pp_e_constants.pp_e_base_sound[OF k6_loc] and k6_all = pp_e_constants.pp_e_closed_gvalid_all_contexts[OF k6_loc]
  and k6_zeta = pp_e_constants.pp_e_zeta_sound[OF k6_loc]

abbreviation k6_gv :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where "k6_gv \<equiv> GenericExactBaconConstants.ExactBaconHenkin.gvalid"

lemma k6_MP: "k6_gv \<Gamma> A \<Longrightarrow> k6_gv \<Gamma> (Imp A B) \<Longrightarrow> k6_gv \<Gamma> B" by (rule GenericExactBaconConstants.ExactBaconHenkin.gvalidI)
  (metis GenericExactBaconConstants.ExactBaconHenkin.gvalidD GenericExactBaconConstants.ExactBaconHenkin.den_Imp)

lemma k6_local: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A \<Longrightarrow> (\<And>B. B \<in> T \<Longrightarrow> k6_gv \<Gamma> B) \<Longrightarrow> k6_gv \<Gamma> A"
proof (induction rule: CEV_set_derivable.induct)
  case (Derive_MP \<Gamma> T A B) then show ?case using k6_MP[of \<Gamma> A B] by blast
qed (blast, rule k6_sound)

lemma k6_B: "B \<in> pp_full_QLN_background_axioms \<Longrightarrow> k6_gv \<Gamma> B"
  using pp_e_generic_full_QLN_background_gvalid unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def by blast

theorem k6_model: "GenericExactBaconConstants.ExactBaconHenkin.gvalid_set pp_CFP_axioms"
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def
  using k6_all[OF pp_CFP_closed k6_local[OF cfp3 k6_B]] by blast

theorem k6: "\<not> [] ; pp_CFP_axioms \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
  using k6_local[of "[]" pp_CFP_axioms ObjFalse] k6_model GenericExactBaconConstants.ExactBaconHenkin.ObjFalse_not_gvalid
  unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def by blast

theorem k6_plus: "CEV_axiom_consistent [] pp_CFP_axioms"
  by (rule GenericExactBaconConstants.ExactBaconHenkin.CEV_axiom_consistent_of_gvalid[OF k6_sound k6_zeta k6_model])

theorem k6_ctl_PP: "k6_gv [] (Neg pp_target_PP)"
  using k6_local[OF cfp2] k6_model unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def by blast

theorem k6_ctl_dist: "\<not> k6_gv [] (cfp_R2 False)" proof
  assume r: "k6_gv [] (cfp_R2 False)"
  have ty: "[] \<turnstile> Imp k_EF (Imp (pp_pure cfp_c2 cfp_Xe) (Imp (cfp_R2 False) ObjFalse)) : Prop"
    using cfp_EF_ty typed_pp_pure[OF cfp_X_ty(2)] cfp_R2_ty(1) typed_ObjFalse by blast
  have t: "[] \<turnstile>\<^sub>CEV Imp k_EF (Imp (pp_pure cfp_c2 cfp_Xe) (Imp (cfp_R2 False) ObjFalse))"
    by (rule rc_pc1[OF cfp_ctl_dist ty]) (unfold ObjFalse_def prop_eval.simps, blast)
  have e: "k6_gv [] k_EF" and x: "k6_gv [] (pp_pure cfp_c2 cfp_Xe)"
    using k6_model cfp_mem(3) cfp_LP[OF cfp_X_ty(2) cfp_X_closed(2)] unfolding GenericExactBaconConstants.ExactBaconHenkin.gvalid_set_def by blast+
  have "k6_gv [] ObjFalse" by (rule k6_MP[OF r k6_MP[OF x k6_MP[OF e k6_sound[OF t]]]])
  then show False using GenericExactBaconConstants.ExactBaconHenkin.ObjFalse_not_gvalid by blast
qed

end
