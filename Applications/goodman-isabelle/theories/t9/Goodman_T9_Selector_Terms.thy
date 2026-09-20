theory Goodman_T9_Selector_Terms
  imports Goodman_Integration_Exact_M.Goodman_Exact_M1_Fn59
    Goodman_Integration_Exact_L2.Goodman_Exact_Fun_Prime_Root
begin

section \<open>Typed lowering of a PC selector to a unary proposition operator\<close>

abbreviation gi_T9_pred where "gi_T9_pred \<equiv> Arr gb_unary Prop"
abbreviation gi_T9_J_type where "gi_T9_J_type \<equiv> Arr gi_T9_pred gb_unary"
abbreviation gi_T9_lower_type where
  "gi_T9_lower_type \<equiv> Arr gi_T9_pred (Arr gi_T9_pred (Arr gb_unary gb_unary))"

definition gi_T9_J_builder :: oterm where
  "gi_T9_J_builder = Lam gi_T9_pred (Lam Prop
    (Forall gb_unary (Forall gb_unary
      (Imp (Conj (App (Var 3) (Var 1)) (App (Var 3) (Var 0)))
        (Imp (Eq Prop (App (Var 1) (Var 2)) (App (Var 0) (Var 2)))
          (Eq gb_unary (Var 1) (Var 0)))))))"

definition gi_T9_lower_builder :: oterm where
  "gi_T9_lower_builder = Lam gi_T9_pred (Lam gi_T9_pred (Lam gb_unary (Lam Prop
    (Exists gb_unary (Exists Prop
      (Conj (App (Var 5) (Var 1))
        (Conj (App (Var 4) (Var 1))
          (Conj (App (Var 3) (Var 0))
            (Eq Prop (Var 2) (App (Var 1) (Var 0)))))))))))"

text \<open>
  J(P)(p) says that evaluation at p is injective on operators selected by P.
  The second closed logical builder takes P:u→t, H:u→t and J:u, where
  u=t→t, and produces the UNARY operator
  F(p) = ∃X q (P(X) ∧ H(X) ∧ J(q) ∧ p=Xq).
  Thus a PC selector H is not mistaken for the unary operator F required
  by the T9 counting argument. All three input constants are abstracted.
\<close>

lemma gi_T9_J_builder_type:
  "[] \<turnstile> gi_T9_J_builder : gi_T9_J_type"
  by (rule infer_type_sound; simp add: gi_T9_J_builder_def lookup_def)

lemma gi_T9_lower_builder_type:
  "[] \<turnstile> gi_T9_lower_builder : gi_T9_lower_type"
  by (rule infer_type_sound; simp add: gi_T9_lower_builder_def lookup_def)

lemma gi_T9_builders_logical:
  "pp_logical_vocabulary gi_T9_J_builder"
  "pp_logical_vocabulary gi_T9_lower_builder"
  by (simp_all add: gi_T9_J_builder_def gi_T9_lower_builder_def pp_logical_vocabulary_def)

definition gi_T9_J_value where
  "gi_T9_J_value C = pp_e_closed_den gi_T9_J_builder \<acute> C pp_pure_name gi_T9_pred"

definition gi_T9_lower_value where
  "gi_T9_lower_value C H =
    ((pp_e_closed_den gi_T9_lower_builder \<acute> C pp_pure_name gi_T9_pred) \<acute> H) \<acute> gi_T9_J_value C"

context pp_e_constants
begin

lemma gi_T9_J_value_member:
  "Elem (gi_T9_J_value C) (pp_e_domain gb_unary)"
  unfolding gi_T9_J_value_def
  by (rule pp_e_app_closed[OF pp_e_closed_den_in_domain[OF gi_T9_J_builder_type] C_typed])

lemma gi_T9_lower_value_member:
  assumes hm: "Elem H (pp_e_domain gi_T9_pred)"
  shows "Elem (gi_T9_lower_value C H) (pp_e_domain gb_unary)"
proof -
  have bm: "Elem (pp_e_closed_den gi_T9_lower_builder) (pp_e_domain gi_T9_lower_type)"
    by (rule pp_e_closed_den_in_domain[OF gi_T9_lower_builder_type])
  have first: "Elem (pp_e_closed_den gi_T9_lower_builder \<acute> C pp_pure_name gi_T9_pred)
    (pp_e_domain (Arr gi_T9_pred (Arr gb_unary gb_unary)))"
    by (rule pp_e_app_closed[OF bm C_typed])
  have second: "Elem ((pp_e_closed_den gi_T9_lower_builder \<acute> C pp_pure_name gi_T9_pred) \<acute> H)
    (pp_e_domain (Arr gb_unary gb_unary))"
    by (rule pp_e_app_closed[OF first hm])
  show ?thesis unfolding gi_T9_lower_value_def by (rule pp_e_app_closed[OF second gi_T9_J_value_member])
qed

lemma gi_T9_J_value_holds:
  assumes pm: "Elem p (pp_e_domain Prop)"
  shows "pp_e_holds (gi_T9_J_value C \<acute> p) w \<longleftrightarrow>
    (\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      (\<forall>Y. Elem Y (pp_e_domain gb_unary) \<longrightarrow>
        ((gi_M1_exact_Pure C gb_unary w X \<and> gi_M1_exact_Pure C gb_unary w Y) \<longrightarrow>
          (pp_e_eqv Prop w (X \<acute> p) (Y \<acute> p) \<longrightarrow> pp_e_eqv gb_unary w X Y))))"
  using pm C_typed[of pp_pure_name gi_T9_pred]
  by (simp add: gi_T9_J_value_def pp_e_closed_den_def gi_T9_J_builder_def Lambda_app
    gi_M1_exact_Pure_def numeral_3_eq_3 numeral_2_eq_2)

lemma gi_T9_fun_prime_formula_holds:
  assumes mt: "\<Gamma> \<turnstile> M : Prop" and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval C \<rho> (pp_fun_prime M)) w =
    pp_e_holds (gi_T9_J_value C \<acute> pp_e_eval C \<rho> M) w"
proof -
  have pm: "Elem (pp_e_eval C \<rho> M) (pp_e_domain Prop)"
    using pp_e_eval_type[OF mt env] by (simp only: pp_e_dom_def)
  show ?thesis
    by (simp only: gi_T9_J_value_holds[OF pm] pp_fun_prime_def pp_pure_def pp_Pure_def
      pp_e_eval_Forall_holds pp_e_eval_Imp_holds pp_e_eval_Conj_holds pp_e_eval_Eq_holds
      pp_e_eval.simps(1,2,3) One_nat_def extend_env.simps gi_exact_eval_shift_two
      pp_unary_ty_def gi_M1_exact_Pure_def)
qed

lemma gi_T9_lower_value_holds:
  assumes hm: "Elem H (pp_e_domain gi_T9_pred)" and pm: "Elem p (pp_e_domain Prop)"
  shows "pp_e_holds (gi_T9_lower_value C H \<acute> p) w \<longleftrightarrow>
    (\<exists>X. Elem X (pp_e_domain gb_unary) \<and>
      (\<exists>q. Elem q (pp_e_domain Prop) \<and>
        gi_M1_exact_Pure C gb_unary w X \<and> pp_e_holds (H \<acute> X) w \<and>
        pp_e_holds (gi_T9_J_value C \<acute> q) w \<and> pp_e_eqv Prop w p (X \<acute> q)))"
  using hm pm C_typed[of pp_pure_name gi_T9_pred] gi_T9_J_value_member
  by (simp add: gi_T9_lower_value_def pp_e_closed_den_def gi_T9_lower_builder_def Lambda_app
    gi_M1_exact_Pure_def eval_nat_numeral)

end

text \<open>
  These typed value equations are the concrete selector-lowering step,
  not a cardinality theorem or an assumption that PC holds in the current
  generic model. The following integration must derive purity of these
  values from the actual native axiom package and obtain H from precisely
  stated full PC, before applying the counting argument.
\<close>

end
