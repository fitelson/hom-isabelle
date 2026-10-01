theory Verification_Checkpoint
  imports Normalization_Witness_Setup Typed_Equality Typed_Quantifier Typed_Implication
begin

section \<open>Kernel-checked construction checkpoint, not yet source modelhood\<close>

text \<open>The following audit checks proof dependencies of the concrete
  counterexample calculations, the all-type carrier construction and the
  logical/combinatory membership results. No theorem in this checkpoint
  asserts the independent source action-model or book model predicate.
  The model bridge is checked later in Typed_Source_Model and
  Typed_Paper_Model. The all-relational-type Boolean-algebra identification
  and the interpretation of the additional source hypotheses and failed
  Rigid Comprehension instance remain separate obligations.\<close>

ML \<open>
  val facts = [
    @{thm norm_U_free}, @{thm normalization_fiber_Inf_bottom},
    @{thm normalization_does_not_preserve_fiber},
    @{thm no_rigid_profile_for_zero_fiber},
    @{thm root_prop_atomic}, @{thm footnote_setup_and_normalization_loss},
    @{thm finite_carrier_eventually_constant}, @{thm ulim_binary},
    @{thm ulim_ball_finite},
    @{thm typed_M_finite}, @{thm typed_M_nonempty},
    @{thm typed_S_finite}, @{thm typed_S_nonempty},
    @{thm typed_j_type}, @{thm typed_j_onto}, @{thm typed_S_extensional},
    @{thm typed_R_joint_surjective}, @{thm typed_rs_surjective},
    @{thm typed_rn_surjective}, @{thm typed_R_nonempty},
    @{thm typed_R_application}, @{thm typed_R_application_s},
    @{thm typed_R_application_n}, @{thm typed_R_extensional},
    @{thm zprop_carrier}, @{thm zprop_inject}, @{thm typed_rs_zprop},
    @{thm typed_normalization_action_failure},
    @{thm typed_req_type}, @{thm typed_req_apply},
    @{thm typed_rall_type}, @{thm typed_rall_truth},
    @{thm typed_rall_middle_truth}, @{thm typed_rall_leaf_truth},
    @{thm typed_rall_limit_truth},
    @{thm tc_rK_type}, @{thm tc_rK_apply},
    @{thm tc_rS_type}, @{thm tc_rS_apply},
    @{thm ti_r_type}, @{thm ti_r_apply}];
  val _ = if null (Thm_Deps.all_oracles facts) then ()
    else error "Unexpected oracle dependency";
  val _ = List.app (fn th =>
    if null (Thm.hyps_of th) andalso null (Thm.tpairs_of th) then ()
    else error "Residual proof obligation") facts;
  val _ = writeln ("VERIFICATION-CHECKPOINT: " ^ string_of_int (length facts) ^
    " clean construction endpoints; source-model certificate is in Typed_Paper_Model");
\<close>

end
