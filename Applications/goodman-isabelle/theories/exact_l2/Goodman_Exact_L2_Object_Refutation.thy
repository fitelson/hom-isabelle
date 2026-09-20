theory Goodman_Exact_L2_Object_Refutation
  imports Goodman_Exact_Fun_Prime_Root Goodman_Exact_Kind_Root Goodman_Exact_L2_Transfer
    Goodman_Integration_Exact_QLN.Goodman_Exact_QLN_Model
begin

section \<open>The actual L2 formula implies its fixed-stock semantic instance\<close>

lemma gi_exact_L2_root_instance:
  assumes truth: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> pp_L2) []"
    and xm: "Elem X (pp_e_domain gb_unary)" and ym: "Elem Y (pp_e_domain gb_unary)"
    and pm: "Elem p (pp_e_domain Prop)" and qm: "Elem q (pp_e_domain Prop)"
    and pure_x: "pp_e_closed_logical_stock gb_unary [] X"
    and pure_y: "pp_e_closed_logical_stock gb_unary [] Y"
    and fp: "pp_e_exact_fun_prime (pp_n_bacon_extract p)"
    and fq: "pp_e_exact_fun_prime (pp_n_bacon_extract q)"
    and same: "X \<acute> p = Y \<acute> q"
  shows "pp_e_exact_same_kind (pp_e_raw_operator X) (pp_e_raw_operator Y)"
proof -
  let ?env = "extend_env q (extend_env p (extend_env Y (extend_env X \<rho>)))"
  let ?\<Gamma> = "[Prop, Prop, gb_unary, gb_unary]"
  have environment: "pp_e_env_typed ?\<Gamma> ?env"
    by (rule pp_e_env_typed_extend[OF pp_e_env_typed_extend[
      OF pp_e_env_typed_extend[OF pp_e_env_typed_extend[OF pp_e_empty_env_typed xm] ym] pm] qm])
  have pt: "?\<Gamma> \<turnstile> Var 1 : Prop" and qt: "?\<Gamma> \<turnstile> Var 0 : Prop"
    and xt: "?\<Gamma> \<turnstile> Var 3 : pp_unary_ty" and yt: "?\<Gamma> \<turnstile> Var 2 : pp_unary_ty"
    by (rule has_type.Var; simp add: lookup_def pp_unary_ty_def)+
  have px: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants ?env
      (pp_pure pp_unary_ty (Var 3))) []"
    using pure_x xm by (simp add: pp_pure_def pp_unary_ty_def pp_e_classifier_holds numeral_3_eq_3)
  have py: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants ?env
      (pp_pure pp_unary_ty (Var 2))) []"
    using pure_y ym by (simp add: pp_pure_def pp_unary_ty_def pp_e_classifier_holds)
  have pfp: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants ?env (pp_fun_prime (Var 1))) []"
    using fp by (simp only: gi_exact_fun_prime_root_iff[OF pt environment]; simp)
  have qfp: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants ?env (pp_fun_prime (Var 0))) []"
    using fq by (simp only: gi_exact_fun_prime_root_iff[OF qt environment]; simp)
  have xp: "Elem (X \<acute> p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF xm pm])
  have yq: "Elem (Y \<acute> q) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF ym qm])
  have x_eval: "pp_e_eval pp_e_generic_internal_constants ?env (App (Var 3) (Var 1)) = X \<acute> p"
    by (simp add: numeral_3_eq_3)
  have y_eval: "pp_e_eval pp_e_generic_internal_constants ?env (App (Var 2) (Var 0)) = Y \<acute> q"
    by simp
  have eq: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants ?env
      (Eq Prop (App (Var 3) (Var 1)) (App (Var 2) (Var 0)))) []"
    unfolding pp_e_eval_Eq_holds x_eval y_eval
    using same gi_exact_root_eqv[OF xp yq] by blast
  have kind: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants ?env (pp_same_kind (Var 3) (Var 2))) []"
    using truth xm ym pm qm px py pfp qfp eq
    unfolding pp_L2_def pp_unary_ty_def
    by (simp only: pp_e_eval_Forall_holds pp_e_eval_Imp_holds pp_e_eval_Conj_holds; blast)
  show ?thesis using kind
    by (simp only: gi_exact_same_kind_root_iff[OF xt yt environment]; simp add: numeral_3_eq_3)
qed

theorem gi_exact_L2_root_implies_fixed_stock:
  assumes truth: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> pp_L2) []"
  shows "pp_e_exact_L2"
proof -
  have kind: "pp_e_exact_same_kind F H"
    if fs: "F \<in> pp_e_exact_operator_stock" and hs: "H \<in> pp_e_exact_operator_stock"
      and fp: "pp_e_exact_fun_prime P" and fq: "pp_e_exact_fun_prime Q"
      and same: "F P = H Q" for F H P Q
  proof -
    obtain X where xs: "X \<in> pp_e_closed_unary_denotations" and fx: "F = pp_e_raw_operator X"
      using fs unfolding pp_e_exact_operator_stock_def by blast
    obtain Y where ys: "Y \<in> pp_e_closed_unary_denotations" and hy: "H = pp_e_raw_operator Y"
      using hs unfolding pp_e_exact_operator_stock_def by blast
    have xm: "Elem X (pp_e_domain gb_unary)" by (rule pp_e_closed_unary_denotation_in_domain[OF xs])
    have ym: "Elem Y (pp_e_domain gb_unary)" by (rule pp_e_closed_unary_denotation_in_domain[OF ys])
    have pm: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)" using pp_n_bacon_embed_in_domain[of P] by simp
    have qm: "Elem (pp_n_bacon_embed Q) (pp_e_domain Prop)" using pp_n_bacon_embed_in_domain[of Q] by simp
    have pure_x: "pp_e_closed_logical_stock gb_unary [] X" by (simp only: gi_exact_root_unary_stock; rule xs)
    have pure_y: "pp_e_closed_logical_stock gb_unary [] Y" by (simp only: gi_exact_root_unary_stock; rule ys)
    have app_same: "X \<acute> pp_n_bacon_embed P = Y \<acute> pp_n_bacon_embed Q"
      using same by (simp only: fx hy
        gi_exact_raw_application_eq_iff[OF xm ym pm qm, simplified])
    have fp': "pp_e_exact_fun_prime (pp_n_bacon_extract (pp_n_bacon_embed P))" using fp by simp
    have fq': "pp_e_exact_fun_prime (pp_n_bacon_extract (pp_n_bacon_embed Q))" using fq by simp
    show ?thesis unfolding fx hy
      by (rule gi_exact_L2_root_instance[OF truth xm ym pm qm pure_x pure_y fp' fq' app_same])
  qed
  show ?thesis unfolding pp_e_exact_L2_def pp_e_exact_L2_pair_def using kind by blast
qed

theorem gi_exact_generic_L2_false_at_root:
  "\<not> pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> pp_L2) []"
  using gi_exact_L2_root_implies_fixed_stock pp_e_child_variation_refutes_exact_L2 by blast

theorem gi_exact_native_L2_formula_false_at_root:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
  shows "\<not> gi_exact_valuation [] (gi_exact_goodman_denote pp_e_generic_internal_constants G g
    (gi_to_book G [] k pp_L2))"
proof -
  have vocabulary: "consts_of pp_L2 \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_L2_def pp_fun_prime_def pp_same_kind_def pp_group_member_def
      pp_reversible_def pp_compose_def pp_identity_operator_def pp_pure_def pp_Pure_def
      shift_def shift_by_def consts_of_rename)
  have denotation: "gi_exact_goodman_denote pp_e_generic_internal_constants G g (gi_to_book G [] k pp_L2) =
    pp_e_eval pp_e_generic_internal_constants pp_e_closed_env pp_L2"
    by (rule pp_e_constants.gi_exact_goodman_closed_denotation_translation[
      OF gi_exact_generic_constants rich typed_pp_L2 typed names vocabulary])
  show ?thesis by (simp only: denotation gi_exact_valuation_def; rule gi_exact_generic_L2_false_at_root)
qed

corollary gi_exact_native_L2_formula_not_global:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "\<not> gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gi_to_book G [] k pp_L2)"
proof
  assume valid: "gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gi_to_book G [] k pp_L2)"
  have typed: "book_env_typed gi_exact_domain G (gi_exact_default_assignment G)"
    by (rule gi_exact_default_assignment_typed)
  have at_root: "gi_exact_valuation [] (gi_exact_goodman_denote pp_e_generic_internal_constants G
    (gi_exact_default_assignment G) (gi_to_book G [] k pp_L2))"
    using valid typed unfolding gi_exact_goodman_global_valid_iff by blast
  show False using at_root gi_exact_native_L2_formula_false_at_root[OF rich names typed] by contradiction
qed

corollary gi_exact_QLN_background_not_proves_L2:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "\<not> goodman_book_proves gb_signature G (gi_native_QLN_background G)
    (gi_to_book G [] k pp_L2)"
proof
  assume derivation: "goodman_book_proves gb_signature G (gi_native_QLN_background G)
    (gi_to_book G [] k pp_L2)"
  have valid: "gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gi_to_book G [] k pp_L2)"
    by (rule pp_e_constants.gi_exact_goodman_extension_global_sound[
      OF gi_exact_generic_constants rich derivation gi_exact_generic_QLN_background_gvalid[OF rich]])
  show False using valid gi_exact_native_L2_formula_not_global[OF rich names] by contradiction
qed

text \<open>
  Unlike the raw-stock refutation alone, this theorem evaluates the actual
  translated object-language L2 formula in the specified native generic
  Pure/Fun interpretation. Failure is at the root, hence global validity
  fails. No enlarged Pure stock, PP model, or arbitrary interpretation is
  covered. A root counterexample does not assert falsity at every world.
  The final nonderivability theorem concerns the explicit no-PP background
  package. It leaves derivability after adding PP open.
\<close>

end
