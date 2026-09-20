theory Goodman_Exact_Fun_Prime_Root
  imports Goodman_Exact_L2_Root_Semantics
begin

section \<open>The two bound operators leave the proposition argument unchanged\<close>

lemma gi_exact_eval_shift_two:
  "pp_e_eval C (extend_env Y (extend_env X \<rho>)) (shift_by 2 M) = pp_e_eval C \<rho> M"
  using pp_e_eval_shift_by_extend_envs[where C=C and xs="[Y, X]" and \<rho>=\<rho> and M=M]
  by (simp add: numeral_2_eq_2)

lemma gi_exact_fun_prime_root_schema:
  "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_fun_prime M)) [] \<longleftrightarrow>
    (\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      (\<forall>Y. Elem Y (pp_e_domain gb_unary) \<longrightarrow>
        ((pp_e_closed_logical_stock gb_unary [] X \<and> pp_e_closed_logical_stock gb_unary [] Y) \<longrightarrow>
          (pp_e_eqv Prop []
            (X \<acute> pp_e_eval pp_e_generic_internal_constants \<rho> M)
            (Y \<acute> pp_e_eval pp_e_generic_internal_constants \<rho> M) \<longrightarrow>
           pp_e_eqv gb_unary [] X Y))))"
  using pp_e_classifier_holds[where \<sigma>=gb_unary
    and Q="pp_e_closed_logical_stock gb_unary" and w="[]"]
  by (simp only: pp_fun_prime_def pp_e_eval_Forall_holds pp_e_eval_Imp_holds
      pp_e_eval_Conj_holds pp_e_eval_Eq_holds pp_pure_def
      pp_e_eval.simps(1,3) pp_e_generic_eval_Pure One_nat_def extend_env.simps
      gi_exact_eval_shift_two pp_unary_ty_def; blast)

section \<open>Evaluation-injectivity on the exact denotation set\<close>

lemma gi_exact_fun_prime_root_schema_values:
  assumes pm: "Elem p (pp_e_domain Prop)"
  shows
    "(\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      (\<forall>Y. Elem Y (pp_e_domain gb_unary) \<longrightarrow>
        ((pp_e_closed_logical_stock gb_unary [] X \<and> pp_e_closed_logical_stock gb_unary [] Y) \<longrightarrow>
          (pp_e_eqv Prop [] (X \<acute> p) (Y \<acute> p) \<longrightarrow> pp_e_eqv gb_unary [] X Y))))
      \<longleftrightarrow>
    (\<forall>X\<in>pp_e_closed_unary_denotations. \<forall>Y\<in>pp_e_closed_unary_denotations.
      X \<acute> p = Y \<acute> p \<longrightarrow> X = Y)"
proof
  assume quantified: "\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      (\<forall>Y. Elem Y (pp_e_domain gb_unary) \<longrightarrow>
        ((pp_e_closed_logical_stock gb_unary [] X \<and> pp_e_closed_logical_stock gb_unary [] Y) \<longrightarrow>
          (pp_e_eqv Prop [] (X \<acute> p) (Y \<acute> p) \<longrightarrow> pp_e_eqv gb_unary [] X Y)))"
  show "\<forall>X\<in>pp_e_closed_unary_denotations. \<forall>Y\<in>pp_e_closed_unary_denotations.
      X \<acute> p = Y \<acute> p \<longrightarrow> X = Y"
  proof (intro ballI impI)
    fix X Y
    assume xs: "X \<in> pp_e_closed_unary_denotations"
      and ys: "Y \<in> pp_e_closed_unary_denotations"
      and same: "X \<acute> p = Y \<acute> p"
    have xm: "Elem X (pp_e_domain gb_unary)" by (rule pp_e_closed_unary_denotation_in_domain[OF xs])
    have ym: "Elem Y (pp_e_domain gb_unary)" by (rule pp_e_closed_unary_denotation_in_domain[OF ys])
    have pure_x: "pp_e_closed_logical_stock gb_unary [] X" by (simp only: gi_exact_root_unary_stock; rule xs)
    have pure_y: "pp_e_closed_logical_stock gb_unary [] Y" by (simp only: gi_exact_root_unary_stock; rule ys)
    have xp: "Elem (X \<acute> p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF xm pm])
    have yp: "Elem (Y \<acute> p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF ym pm])
    have values_related: "pp_e_eqv Prop [] (X \<acute> p) (Y \<acute> p)"
      by (simp only: gi_exact_root_eqv[OF xp yp]; rule same)
    have operators_related: "pp_e_eqv gb_unary [] X Y"
      using quantified xm ym pure_x pure_y values_related by blast
    show "X = Y" using operators_related by (simp only: gi_exact_root_eqv[OF xm ym])
  qed
next
  assume injective: "\<forall>X\<in>pp_e_closed_unary_denotations. \<forall>Y\<in>pp_e_closed_unary_denotations.
      X \<acute> p = Y \<acute> p \<longrightarrow> X = Y"
  show "\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      (\<forall>Y. Elem Y (pp_e_domain gb_unary) \<longrightarrow>
        ((pp_e_closed_logical_stock gb_unary [] X \<and> pp_e_closed_logical_stock gb_unary [] Y) \<longrightarrow>
          (pp_e_eqv Prop [] (X \<acute> p) (Y \<acute> p) \<longrightarrow> pp_e_eqv gb_unary [] X Y)))"
  proof (intro allI impI)
    fix X Y
    assume xm: "Elem X (pp_e_domain gb_unary)" and ym: "Elem Y (pp_e_domain gb_unary)"
      and pure: "pp_e_closed_logical_stock gb_unary [] X \<and> pp_e_closed_logical_stock gb_unary [] Y"
      and values_related: "pp_e_eqv Prop [] (X \<acute> p) (Y \<acute> p)"
    have xs: "X \<in> pp_e_closed_unary_denotations"
      using conjunct1[OF pure] by (simp only: gi_exact_root_unary_stock)
    have ys: "Y \<in> pp_e_closed_unary_denotations"
      using conjunct2[OF pure] by (simp only: gi_exact_root_unary_stock)
    have xp: "Elem (X \<acute> p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF xm pm])
    have yp: "Elem (Y \<acute> p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF ym pm])
    have same: "X \<acute> p = Y \<acute> p" using values_related by (simp only: gi_exact_root_eqv[OF xp yp])
    have equal: "X = Y" using injective xs ys same by blast
    show "pp_e_eqv gb_unary [] X Y" by (simp only: gi_exact_root_eqv[OF xm ym]; rule equal)
  qed
qed

lemma gi_exact_fun_prime_values_iff_raw:
  assumes pm: "Elem p (pp_e_domain Prop)"
  shows "(\<forall>X\<in>pp_e_closed_unary_denotations. \<forall>Y\<in>pp_e_closed_unary_denotations.
      X \<acute> p = Y \<acute> p \<longrightarrow> X = Y)
    \<longleftrightarrow> pp_e_exact_fun_prime (pp_n_bacon_extract p)"
proof
  assume injective: "\<forall>X\<in>pp_e_closed_unary_denotations. \<forall>Y\<in>pp_e_closed_unary_denotations.
      X \<acute> p = Y \<acute> p \<longrightarrow> X = Y"
  show "pp_e_exact_fun_prime (pp_n_bacon_extract p)"
  proof (rule pp_e_exact_fun_primeI)
    fix F H
    assume fs: "F \<in> pp_e_exact_operator_stock" and hs: "H \<in> pp_e_exact_operator_stock"
      and same: "F (pp_n_bacon_extract p) = H (pp_n_bacon_extract p)"
    obtain X where xs: "X \<in> pp_e_closed_unary_denotations" and fshape: "F = pp_e_raw_operator X"
      using fs unfolding pp_e_exact_operator_stock_def by blast
    obtain Y where ys: "Y \<in> pp_e_closed_unary_denotations" and hshape: "H = pp_e_raw_operator Y"
      using hs unfolding pp_e_exact_operator_stock_def by blast
    have xm: "Elem X (pp_e_domain gb_unary)" by (rule pp_e_closed_unary_denotation_in_domain[OF xs])
    have ym: "Elem Y (pp_e_domain gb_unary)" by (rule pp_e_closed_unary_denotation_in_domain[OF ys])
    have raw_same: "pp_e_raw_operator X (pp_n_bacon_extract p) = pp_e_raw_operator Y (pp_n_bacon_extract p)"
      using same by (simp only: fshape hshape)
    have value_same: "X \<acute> p = Y \<acute> p"
      using raw_same by (simp only: gi_exact_raw_application_eq_iff[OF xm ym pm pm])
    have equal: "X = Y" using injective xs ys value_same by blast
    show "F = H" by (simp only: fshape hshape equal)
  qed
next
  assume raw: "pp_e_exact_fun_prime (pp_n_bacon_extract p)"
  show "\<forall>X\<in>pp_e_closed_unary_denotations. \<forall>Y\<in>pp_e_closed_unary_denotations.
      X \<acute> p = Y \<acute> p \<longrightarrow> X = Y"
  proof (intro ballI impI)
    fix X Y
    assume xs: "X \<in> pp_e_closed_unary_denotations" and ys: "Y \<in> pp_e_closed_unary_denotations"
      and same: "X \<acute> p = Y \<acute> p"
    have xm: "Elem X (pp_e_domain gb_unary)" by (rule pp_e_closed_unary_denotation_in_domain[OF xs])
    have ym: "Elem Y (pp_e_domain gb_unary)" by (rule pp_e_closed_unary_denotation_in_domain[OF ys])
    have fs: "pp_e_raw_operator X \<in> pp_e_exact_operator_stock"
      unfolding pp_e_exact_operator_stock_def by (rule imageI[OF xs])
    have hs: "pp_e_raw_operator Y \<in> pp_e_exact_operator_stock"
      unfolding pp_e_exact_operator_stock_def by (rule imageI[OF ys])
    have raw_same: "pp_e_raw_operator X (pp_n_bacon_extract p) = pp_e_raw_operator Y (pp_n_bacon_extract p)"
      by (simp only: gi_exact_raw_application_eq_iff[OF xm ym pm pm]; rule same)
    have raw_equal: "pp_e_raw_operator X = pp_e_raw_operator Y"
      by (rule pp_e_exact_fun_primeD[OF raw fs hs raw_same])
    show "X = Y" by (rule gi_exact_raw_operator_injective[OF xm ym raw_equal])
  qed
qed

section \<open>The actual object-language fun′ formula at the root\<close>

theorem gi_exact_fun_prime_root_iff:
  assumes term_type: "\<Gamma> \<turnstile> M : Prop" and typed: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_fun_prime M)) [] \<longleftrightarrow>
    pp_e_exact_fun_prime (pp_n_bacon_extract (pp_e_eval pp_e_generic_internal_constants \<rho> M))"
proof -
  have pm: "Elem (pp_e_eval pp_e_generic_internal_constants \<rho> M) (pp_e_domain Prop)"
    using GenericExactBaconConstants.pp_e_eval_type[OF term_type typed] by (simp only: pp_e_dom_def)
  show ?thesis
    by (simp only: gi_exact_fun_prime_root_schema gi_exact_fun_prime_root_schema_values[OF pm]
        gi_exact_fun_prime_values_iff_raw[OF pm])
qed

corollary gi_exact_generic_fun_prime_variable_root:
  assumes index_type: "lookup \<Gamma> n = Some Prop" and typed: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_fun_prime (Var n))) [] \<longleftrightarrow>
    pp_e_exact_fun_prime (pp_n_bacon_extract (\<rho> n))"
  using gi_exact_fun_prime_root_iff[OF has_type.Var[OF index_type] typed]
  by (simp only: pp_e_eval.simps)

text \<open>
  This is evaluation of the actual constructor formula pp_fun_prime in
  the fixed generic Pure/Fun interpretation, not a newly defined alias
  for the semantic property. It covers each well-typed proposition term
  in a typed environment, including free-variable terms in the L2 matrix.
  Identity is equated with global equality only at the root. The pure
  stock remains the complete closed-logical stock, not an enlargement.
\<close>

end
