theory Bacon_PP_ZF_Exact_Logical_Stock_Action
  imports 
    "Goodman_Exact_Legacy_05.Bacon_PP_ZF_Exact_Substitution"
    "Goodman_Exact_Logical_Stock.Bacon_PP_ZF_Exact_Logical_Stock"
begin

theorem pp_e_closed_den_action_invariant:
  assumes typed: "[] \<turnstile> M : \<sigma>"
  shows "pp_b_action \<sigma> i (pp_e_closed_den M) =
    pp_e_closed_den M"
  unfolding pp_e_closed_den_def
  by (rule DefaultExactBaconEquivariant.pp_e_eval_action[
      OF typed pp_e_empty_env_typed pp_e_closed_env_action])

end
