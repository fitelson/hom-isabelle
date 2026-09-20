theory Goodman_Exact_L2_Root_Semantics
  imports Goodman_Exact_Stock_Legacy_02.Bacon_PP_ZF_Exact_L2_Child_Variation
    Goodman_Integration_Exact_QLN.Goodman_Exact_Generic_Interpretation
begin

section \<open>Actual equality and the complete stock at the root\<close>

lemma gi_exact_root_eqv:
  assumes x: "Elem x (pp_e_domain \<sigma>)" and y: "Elem y (pp_e_domain \<sigma>)"
  shows "pp_e_eqv \<sigma> [] x y \<longleftrightarrow> x = y"
  by (simp only: pp_e_eqv_iff_action_eq[OF x y] rev.simps
    pp_b_action_one_all[OF x] pp_b_action_one_all[OF y])

lemma gi_exact_root_logical_stock:
  "pp_e_closed_logical_stock \<sigma> [] x \<longleftrightarrow>
    (\<exists>M. [] \<turnstile> M : \<sigma> \<and> pp_logical_vocabulary M \<and> x = pp_e_closed_den M)"
proof
  assume stock: "pp_e_closed_logical_stock \<sigma> [] x"
  then obtain M where xm: "Elem x (pp_e_domain \<sigma>)"
    and typed: "[] \<turnstile> M : \<sigma>" and logical: "pp_logical_vocabulary M"
    and related: "pp_e_eqv \<sigma> [] x (pp_e_closed_den M)"
    unfolding pp_e_closed_logical_stock_def by blast
  have same: "x = pp_e_closed_den M"
    using related by (simp only: gi_exact_root_eqv[OF xm pp_e_closed_den_in_domain[OF typed]])
  show "\<exists>M. [] \<turnstile> M : \<sigma> \<and> pp_logical_vocabulary M \<and> x = pp_e_closed_den M"
    using typed logical same by blast
next
  assume "\<exists>M. [] \<turnstile> M : \<sigma> \<and> pp_logical_vocabulary M \<and> x = pp_e_closed_den M"
  then obtain M where typed: "[] \<turnstile> M : \<sigma>" and logical: "pp_logical_vocabulary M"
    and shape: "x = pp_e_closed_den M" by blast
  show "pp_e_closed_logical_stock \<sigma> [] x"
    unfolding shape by (rule pp_e_closed_logical_stockI[OF typed logical])
qed

lemma gi_exact_root_unary_stock:
  "pp_e_closed_logical_stock gb_unary [] X \<longleftrightarrow> X \<in> pp_e_closed_unary_denotations"
  by (simp only: gi_exact_root_logical_stock pp_e_closed_unary_denotations_def mem_Collect_eq)

lemma gi_exact_raw_at_extract:
  assumes member: "Elem p (pp_e_domain Prop)"
  shows "pp_e_raw_operator X (pp_n_bacon_extract p) = pp_n_bacon_extract (X \<acute> p)"
  using member by (simp add: pp_e_raw_operator_def pp_n_bacon_embed_extract)

lemma gi_exact_raw_operator_injective:
  assumes xm: "Elem X (pp_e_domain gb_unary)" and ym: "Elem Y (pp_e_domain gb_unary)"
    and same: "pp_e_raw_operator X = pp_e_raw_operator Y"
  shows "X = Y"
proof (rule pp_b_function_ext[OF pp_b_arrow_member_function[OF xm] pp_b_arrow_member_function[OF ym]])
  fix p assume pm: "Elem p (pp_e_domain Prop)"
  have xp: "Elem (X \<acute> p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF xm pm])
  have yp: "Elem (Y \<acute> p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF ym pm])
  have extracted: "pp_n_bacon_extract (X \<acute> p) = pp_n_bacon_extract (Y \<acute> p)"
    using fun_cong[OF same, of "pp_n_bacon_extract p"]
    by (simp only: gi_exact_raw_at_extract[OF pm])
  show "X \<acute> p = Y \<acute> p"
    using pp_n_bacon_extract_injective_on_domain[of "X \<acute> p" "Y \<acute> p"] xp yp extracted by simp
qed

lemma gi_exact_raw_operator_eq_iff:
  "Elem X (pp_e_domain gb_unary) \<Longrightarrow> Elem Y (pp_e_domain gb_unary) \<Longrightarrow>
    pp_e_raw_operator X = pp_e_raw_operator Y \<longleftrightarrow> X = Y"
  using gi_exact_raw_operator_injective by blast

lemma gi_exact_raw_application_eq_iff:
  assumes xm: "Elem X (pp_e_domain gb_unary)" and ym: "Elem Y (pp_e_domain gb_unary)"
    and pm: "Elem p (pp_e_domain Prop)" and qm: "Elem q (pp_e_domain Prop)"
  shows "pp_e_raw_operator X (pp_n_bacon_extract p) = pp_e_raw_operator Y (pp_n_bacon_extract q)
    \<longleftrightarrow> X \<acute> p = Y \<acute> q"
proof -
  have xp: "Elem (X \<acute> p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF xm pm])
  have yq: "Elem (Y \<acute> q) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF ym qm])
  have xp_power: "Elem (X \<acute> p) (Power Nat)" using xp by simp
  have yq_power: "Elem (Y \<acute> q) (Power Nat)" using yq by simp
  have extract_iff: "pp_n_bacon_extract (X \<acute> p) = pp_n_bacon_extract (Y \<acute> q)
      \<longleftrightarrow> X \<acute> p = Y \<acute> q"
  proof
    assume same: "pp_n_bacon_extract (X \<acute> p) = pp_n_bacon_extract (Y \<acute> q)"
    show "X \<acute> p = Y \<acute> q"
      by (rule pp_n_bacon_extract_injective_on_domain[OF xp_power yq_power same])
  next
    assume same: "X \<acute> p = Y \<acute> q"
    show "pp_n_bacon_extract (X \<acute> p) = pp_n_bacon_extract (Y \<acute> q)"
      by (simp only: same)
  qed
  show ?thesis by (simp only: gi_exact_raw_at_extract[OF pm]
    gi_exact_raw_at_extract[OF qm] extract_iff)
qed

section \<open>Composition of exact unary values\<close>

definition gi_exact_value_compose where
  "gi_exact_value_compose X Y = Lambda (pp_e_domain Prop) (\<lambda>p. X \<acute> (Y \<acute> p))"

lemma gi_exact_eval_compose:
  "pp_e_eval C \<rho> (pp_compose M N) =
    gi_exact_value_compose (pp_e_eval C \<rho> M) (pp_e_eval C \<rho> N)"
  by (simp add: pp_compose_def gi_exact_value_compose_def pp_e_eval_shift)

lemma gi_exact_value_compose_member:
  assumes xm: "Elem X (pp_e_domain gb_unary)" and ym: "Elem Y (pp_e_domain gb_unary)"
  shows "Elem (gi_exact_value_compose X Y) (pp_e_domain gb_unary)"
proof -
  let ?env = "extend_env X (extend_env Y pp_e_closed_env)"
  have env: "pp_e_env_typed [gb_unary, gb_unary] ?env"
    by (rule pp_e_env_typed_extend[OF pp_e_env_typed_extend[OF pp_e_empty_env_typed ym] xm])
  have typed: "[gb_unary, gb_unary] \<turnstile> pp_compose (Var 0) (Var 1) : gb_unary"
    by (rule infer_type_sound)
      (simp add: pp_compose_def pp_unary_ty_def shift_def shift_ren_def lookup_def)
  have member: "pp_e_dom gb_unary
    (pp_e_eval pp_e_default_constants ?env (pp_compose (Var 0) (Var 1)))"
    by (rule DefaultExactBaconConstants.pp_e_eval_type[OF typed env])
  show ?thesis using member by (simp add: pp_e_dom_def gi_exact_eval_compose)
qed

lemma gi_exact_raw_value_compose:
  assumes xm: "Elem X (pp_e_domain gb_unary)" and ym: "Elem Y (pp_e_domain gb_unary)"
  shows "pp_e_raw_operator (gi_exact_value_compose X Y) = pp_e_raw_operator X \<circ> pp_e_raw_operator Y"
proof (rule ext)
  fix P
  have pm: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)"
    using pp_n_bacon_embed_in_domain[of P] by simp
  have yp: "Elem (Y \<acute> pp_n_bacon_embed P) (pp_e_domain Prop)"
    by (rule pp_e_app_closed[OF ym pm])
  have eta: "pp_n_bacon_embed (pp_n_bacon_extract (Y \<acute> pp_n_bacon_embed P)) = Y \<acute> pp_n_bacon_embed P"
    using yp by (simp add: pp_n_bacon_embed_extract)
  show "pp_e_raw_operator (gi_exact_value_compose X Y) P =
      (pp_e_raw_operator X \<circ> pp_e_raw_operator Y) P"
    unfolding pp_e_raw_operator_def gi_exact_value_compose_def comp_apply
    by (simp only: Lambda_app[OF pm] eta)
qed

text \<open>
  At the root, local identity is actual equality and the saturated unary
  stock is the literal closed-denotation set. The raw representation is
  faithful on the exact unary carrier. These facts prepare the object-language
  L2 evaluation bridge; they do not themselves assert that a particular
  interpretation falsifies the object-language formula.
\<close>

end
