theory Goodman_Exact_Basis_QSS
  imports Goodman_Exact_M5_Rebuilt_Model
    Goodman_Integration_Central_Stock.Goodman_Native_QSS
    Goodman_Integration_Exact_L2.Goodman_Exact_Fun_Prime_Root
begin

section \<open>Worldwise QSS from the actual moving seed\<close>

text \<open>
  At w, a pure unary value has its action by rev(w) in the invariant basis.
  A fundamental proposition's same action is the root generic seed.
  Agreement of the original applications at w therefore becomes equality
  of two basis applications at that root seed. The proved equalizer-seed
  construction separates those basis values. Transforming back gives local
  identity at w, not unqualified identity of the original global values.

  This argument does not assume that every view of one fixed proposition
  is fun′. The witness at w is the explicitly constructed moving seed.
\<close>

context gi_exact_invariant_basis
begin

lemma gi_basis_fundamental_action:
  assumes rm: "Elem r (pp_e_domain Prop)" and fundamental: "gi_basis_fundamental_at B Prop w r"
  shows "pp_b_action Prop (rev w) r = gi_basis_root_seed B"
  using fundamental
  by (simp only: gi_basis_fundamental_at.simps pp_e_eqv_iff_action_eq[OF rm gi_basis_seed_at_member]
    gi_basis_seed_at_action)

theorem gi_basis_QSS_at_world:
  assumes px: "gi_basis_pure B gb_unary w X" and py: "gi_basis_pure B gb_unary w Y"
    and rm: "Elem r (pp_e_domain Prop)" and fundamental: "gi_basis_fundamental_at B Prop w r"
    and agree: "pp_e_eqv Prop w (X \<acute> r) (Y \<acute> r)"
  shows "pp_e_eqv gb_unary w X Y"
proof -
  have xm: "Elem X (pp_e_domain gb_unary)" and ym: "Elem Y (pp_e_domain gb_unary)"
    by (rule gi_basis_pure_member[OF px], rule gi_basis_pure_member[OF py])
  let ?D = "pp_b_action gb_unary (rev w) X"
  let ?E = "pp_b_action gb_unary (rev w) Y"
  have db: "?D \<in> B gb_unary" using px by (simp only: gi_basis_pure_iff_action_member[OF xm])
  have eb: "?E \<in> B gb_unary" using py by (simp only: gi_basis_pure_iff_action_member[OF ym])
  have dm: "Elem ?D (pp_e_domain gb_unary)" and em: "Elem ?E (pp_e_domain gb_unary)"
    by (rule basis_member[OF db], rule basis_member[OF eb])
  have xr: "Elem (X \<acute> r) (pp_e_domain Prop)" and yr: "Elem (Y \<acute> r) (pp_e_domain Prop)"
    by (rule pp_e_app_closed[OF xm rm], rule pp_e_app_closed[OF ym rm])
  have acted: "pp_b_action Prop (rev w) (X \<acute> r) = pp_b_action Prop (rev w) (Y \<acute> r)"
    using agree by (simp only: pp_e_eqv_iff_action_eq[OF xr yr])
  have root_r: "pp_b_action Prop (rev w) r = gi_basis_root_seed B"
    by (rule gi_basis_fundamental_action[OF rm fundamental])
  have x_app: "?D \<acute> gi_basis_root_seed B = pp_b_action Prop (rev w) (X \<acute> r)"
    using pp_b_application_substitution_exact[OF xm rm, of "rev w"] by (simp only: root_r)
  have y_app: "?E \<acute> gi_basis_root_seed B = pp_b_action Prop (rev w) (Y \<acute> r)"
    using pp_b_application_substitution_exact[OF ym rm, of "rev w"] by (simp only: root_r)
  have applications: "?D \<acute> gi_basis_root_seed B = ?E \<acute> gi_basis_root_seed B"
    using acted x_app y_app by simp
  have raw_agreement: "pp_e_raw_operator ?D (gi_basis_raw_seed B) = pp_e_raw_operator ?E (gi_basis_raw_seed B)"
    using applications
      gi_exact_raw_application_eq_iff[OF dm em gi_basis_root_seed_member gi_basis_root_seed_member]
    by (simp only: gi_basis_root_seed_extract; blast)
  have ds: "pp_e_raw_operator ?D \<in> gi_basis_raw_stock B"
    and es: "pp_e_raw_operator ?E \<in> gi_basis_raw_stock B"
    unfolding gi_basis_raw_stock_def using db eb by blast+
  have raw_equal: "pp_e_raw_operator ?D = pp_e_raw_operator ?E"
    by (rule gi_basis_raw_seed_separates[OF ds es raw_agreement])
  have equal: "?D = ?E" by (rule gi_exact_raw_operator_injective[OF dm em raw_equal])
  show ?thesis by (simp only: pp_e_eqv_iff_action_eq[OF xm ym]; rule equal)
qed

section \<open>The actual source QSS and fun′ formulas\<close>

lemma gi_basis_QSS_holds_iff:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> pp_QSS) w \<longleftrightarrow>
    (\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      (\<forall>Y. Elem Y (pp_e_domain gb_unary) \<longrightarrow>
        (\<forall>r. Elem r (pp_e_domain Prop) \<longrightarrow>
          (gi_basis_pure B gb_unary w X \<and> gi_basis_pure B gb_unary w Y \<and> gi_basis_fundamental_at B Prop w r)
          \<longrightarrow> (pp_e_eqv Prop w (X \<acute> r) (Y \<acute> r) \<longrightarrow> pp_e_eqv gb_unary w X Y))))"
  by (simp add: pp_QSS_def pp_pure_def pp_fun_def gi_basis_eval_Pure gi_basis_eval_Fun
    pp_e_classifier_holds pp_unary_ty_def extend_env.simps pp_e_three_extensions_index_two)

theorem gi_basis_QSS_holds:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> pp_QSS) w"
  unfolding gi_basis_QSS_holds_iff using gi_basis_QSS_at_world by blast

lemma gi_basis_fun_prime_holds_iff:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> (pp_fun_prime M)) w \<longleftrightarrow>
    (\<forall>X. Elem X (pp_e_domain gb_unary) \<longrightarrow>
      (\<forall>Y. Elem Y (pp_e_domain gb_unary) \<longrightarrow>
        ((gi_basis_pure B gb_unary w X \<and> gi_basis_pure B gb_unary w Y) \<longrightarrow>
          (pp_e_eqv Prop w
            (X \<acute> pp_e_eval (gi_basis_internal_constants B) \<rho> M)
            (Y \<acute> pp_e_eval (gi_basis_internal_constants B) \<rho> M) \<longrightarrow>
            pp_e_eqv gb_unary w X Y))))"
  using pp_e_classifier_holds[where \<sigma>=gb_unary and Q="gi_basis_pure B gb_unary" and w=w]
  by (simp only: pp_fun_prime_def pp_e_eval_Forall_holds pp_e_eval_Imp_holds
    pp_e_eval_Conj_holds pp_e_eval_Eq_holds pp_pure_def pp_e_eval.simps(1,3)
    gi_basis_eval_Pure One_nat_def extend_env.simps gi_exact_eval_shift_two pp_unary_ty_def; blast)

theorem gi_basis_fundamental_fun_prime_holds:
  assumes rm: "Elem r (pp_e_domain Prop)" and fundamental: "gi_basis_fundamental_at B Prop w r"
  shows "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) (extend_env r \<rho>) (pp_fun_prime (Var 0))) w"
  by (simp only: gi_basis_fun_prime_holds_iff pp_e_eval.simps(1) extend_env.simps;
    use gi_basis_QSS_at_world[OF _ _ rm fundamental] in blast)

theorem gi_basis_moving_seed_fun_prime_at_world:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) (extend_env (gi_basis_seed_at B w) \<rho>)
    (pp_fun_prime (Var 0))) w"
proof (rule gi_basis_fundamental_fun_prime_holds[OF gi_basis_seed_at_member])
  show "gi_basis_fundamental_at B Prop w (gi_basis_seed_at B w)"
    by (simp only: gi_basis_fundamental_at.simps; rule pp_e_eqv_reflexive[OF gi_basis_seed_at_member])
qed

theorem gi_basis_exists_fun_prime_holds:
  "pp_e_holds (pp_e_eval (gi_basis_internal_constants B) \<rho> pp_exists_fun_prime) w"
  by (simp only: pp_exists_fun_prime_def pp_e_eval_Exists_holds;
    rule exI[where x="gi_basis_seed_at B w"], rule conjI[OF gi_basis_seed_at_member gi_basis_moving_seed_fun_prime_at_world])

section \<open>Native global QSS and existence\<close>

theorem gi_basis_native_QSS_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G (gb_QSS G)"
proof -
  obtain cmap where names: "gi_goodman_names cmap" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of pp_QSS \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_QSS_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def)
  show ?thesis by (rule gi_basis_native_closed_shape_gvalid[OF rich typed_pp_QSS names vocabulary
    gi_QSS_translation[OF names] gi_basis_QSS_holds])
qed

theorem gi_basis_native_exists_fun_prime_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid (gi_basis_internal_constants B) G (gb_exists_fun_prime G)"
proof -
  obtain cmap where names: "gi_goodman_names cmap" using gi_goodman_names_satisfiable by blast
  have vocabulary: "consts_of pp_exists_fun_prime \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_exists_fun_prime_def pp_fun_prime_def pp_pure_def pp_Pure_def shift_by_def consts_of_rename)
  show ?thesis by (rule gi_basis_native_closed_shape_gvalid[OF rich typed_pp_exists_fun_prime names vocabulary
    gi_exists_fun_prime_translation[OF names] gi_basis_exists_fun_prime_holds])
qed

end

section \<open>QSS in the actual rebuilt interpreter, not just its auxiliary basis interpreter\<close>

context gi_exact_expanded_stock
begin

theorem gi_M5_rebuilt_native_QSS_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid (gi_M5_rebuilt_constants k K) G (gb_QSS G)"
  using gi_exact_invariant_basis.gi_basis_native_QSS_gvalid[OF gi_M5_expanded_invariant_basis rich]
  by (simp only: gi_M5_rebuilt_native_global_valid_iff[OF gb_QSS_language[OF rich]])

theorem gi_M5_rebuilt_native_exists_fun_prime_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid (gi_M5_rebuilt_constants k K) G (gb_exists_fun_prime G)"
  using gi_exact_invariant_basis.gi_basis_native_exists_fun_prime_gvalid[OF gi_M5_expanded_invariant_basis rich]
  by (simp only: gi_M5_rebuilt_native_global_valid_iff[OF gb_exists_fun_prime_language[OF rich]])

end

corollary gi_exact_M5_rebuilt_QSS_gvalid:
  "sg_rich G \<Longrightarrow> gi_exact_goodman_global_valid (gi_M5_exotic_constants R) G (gb_QSS G)"
  by (rule gi_exact_expanded_stock.gi_M5_rebuilt_native_QSS_gvalid[OF gi_exact_M5_exotic_expanded_stock]; assumption)

corollary gi_exact_M5_rebuilt_exists_fun_prime_gvalid:
  "sg_rich G \<Longrightarrow> gi_exact_goodman_global_valid (gi_M5_exotic_constants R) G (gb_exists_fun_prime G)"
  by (rule gi_exact_expanded_stock.gi_M5_rebuilt_native_exists_fun_prime_gvalid[OF gi_exact_M5_exotic_expanded_stock]; assumption)

text \<open>
  The existential witness is gi_basis_seed_at B w at the world w, and
  its transformed value is the root generic seed. We never infer that all
  views of that root seed are fun′ in the fixed root stock. QSS has been
  proved for the actual locally saturated Pure interpretation and every
  fundamental role occupant, including the complete enlarged basis used
  in the rebuilt model. No PP, Purity of Fun, or assumed QSS axiom is used.
\<close>

end
