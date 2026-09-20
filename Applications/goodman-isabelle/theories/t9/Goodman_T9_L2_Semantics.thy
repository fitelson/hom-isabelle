theory Goodman_T9_L2_Semantics
  imports Goodman_T9_Kind_Selector
    Goodman_Integration_Exact_L2.Goodman_Exact_Kind_Root
begin

section \<open>Actual root evaluation with an arbitrary typed constant interpretation\<close>

context pp_e_constants
begin

lemma gi_T9_pure_formula_root_iff:
  assumes typed: "\<Gamma> \<turnstile> M : \<sigma>" and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval C \<rho> (pp_pure \<sigma> M)) [] \<longleftrightarrow>
    pp_e_eval C \<rho> M \<in> gi_T9_root_pure C \<sigma>"
proof -
  have member: "Elem (pp_e_eval C \<rho> M) (pp_e_domain \<sigma>)"
    using pp_e_eval_type[OF typed env] by (simp only: pp_e_dom_def)
  show ?thesis using member
    by (simp add: pp_pure_def pp_Pure_def gi_T9_root_pure_def gi_M1_exact_Pure_def)
qed

lemma gi_T9_reversible_body_root:
  assumes zm: "Elem (pp_e_eval C \<rho> Z) (pp_e_domain gb_unary)" and wm: "Elem W (pp_e_domain gb_unary)"
  shows "pp_e_holds (pp_e_eval C (extend_env W \<rho>)
    (Conj (pp_pure pp_unary_ty (Var 0))
      (Conj (Eq pp_unary_ty (pp_compose (shift Z) (Var 0)) pp_identity_operator)
        (Eq pp_unary_ty (pp_compose (Var 0) (shift Z)) pp_identity_operator)))) []
    \<longleftrightarrow> gi_M1_exact_Pure C gb_unary [] W \<and>
      gi_exact_value_compose (pp_e_eval C \<rho> Z) W = gi_T9_identity \<and>
      gi_exact_value_compose W (pp_e_eval C \<rho> Z) = gi_T9_identity"
proof -
  have zw: "Elem (gi_exact_value_compose (pp_e_eval C \<rho> Z) W) (pp_e_domain gb_unary)"
    by (rule gi_exact_value_compose_member[OF zm wm])
  have wz: "Elem (gi_exact_value_compose W (pp_e_eval C \<rho> Z)) (pp_e_domain gb_unary)"
    by (rule gi_exact_value_compose_member[OF wm zm])
  show ?thesis
    by (simp only: pp_e_eval_Conj_holds pp_e_eval_Eq_holds pp_pure_def pp_Pure_def
      gi_exact_eval_compose pp_e_eval_shift gi_exact_identity_denotation
      pp_e_eval.simps(1,2,3) extend_env.simps pp_unary_ty_def gi_M1_exact_Pure_def
      gi_exact_root_eqv[OF zw gi_exact_identity_denotation_member]
      gi_exact_root_eqv[OF wz gi_exact_identity_denotation_member] gi_T9_identity_def)
qed

theorem gi_T9_reversible_formula_root_iff:
  assumes typed: "\<Gamma> \<turnstile> Z : pp_unary_ty" and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval C \<rho> (pp_reversible Z)) [] \<longleftrightarrow>
    (\<exists>W\<in>gi_T9_root_pure C gb_unary.
      gi_exact_value_compose (pp_e_eval C \<rho> Z) W = gi_T9_identity \<and>
      gi_exact_value_compose W (pp_e_eval C \<rho> Z) = gi_T9_identity)"
proof -
  have zm: "Elem (pp_e_eval C \<rho> Z) (pp_e_domain gb_unary)"
    using pp_e_eval_type[OF typed env] by (simp only: pp_e_dom_def pp_unary_ty_def)
  let ?B = "\<lambda>W. pp_e_holds (pp_e_eval C (extend_env W \<rho>)
    (Conj (pp_pure pp_unary_ty (Var 0))
      (Conj (Eq pp_unary_ty (pp_compose (shift Z) (Var 0)) pp_identity_operator)
        (Eq pp_unary_ty (pp_compose (Var 0) (shift Z)) pp_identity_operator)))) []"
  let ?I = "\<lambda>W. gi_exact_value_compose (pp_e_eval C \<rho> Z) W = gi_T9_identity \<and>
      gi_exact_value_compose W (pp_e_eval C \<rho> Z) = gi_T9_identity"
  show ?thesis
  proof
    assume holds: "pp_e_holds (pp_e_eval C \<rho> (pp_reversible Z)) []"
    have original: "\<exists>W. Elem W (pp_e_domain pp_unary_ty) \<and> ?B W"
      using holds by (simp only: pp_reversible_def pp_e_eval_Exists_holds)
    then obtain W where wm0: "Elem W (pp_e_domain pp_unary_ty)" and body: "?B W" by blast
    have wm: "Elem W (pp_e_domain gb_unary)" using wm0 by (simp only: pp_unary_ty_def)
    have condition: "gi_M1_exact_Pure C gb_unary [] W \<and> ?I W"
      using body gi_T9_reversible_body_root[OF zm wm] by blast
    have wp: "W \<in> gi_T9_root_pure C gb_unary" using wm condition unfolding gi_T9_root_pure_def by simp
    show "\<exists>W\<in>gi_T9_root_pure C gb_unary. ?I W" using wp condition by blast
  next
    assume inverse: "\<exists>W\<in>gi_T9_root_pure C gb_unary. ?I W"
    then obtain W where wp: "W \<in> gi_T9_root_pure C gb_unary" and inverse: "?I W" by blast
    have wm: "Elem W (pp_e_domain gb_unary)" and pure: "gi_M1_exact_Pure C gb_unary [] W"
      using wp unfolding gi_T9_root_pure_def by auto
    have body: "?B W" using pure inverse gi_T9_reversible_body_root[OF zm wm] by blast
    have wm0: "Elem W (pp_e_domain pp_unary_ty)" using wm by (simp only: pp_unary_ty_def)
    have original: "\<exists>W. Elem W (pp_e_domain pp_unary_ty) \<and> ?B W" using wm0 body by blast
    show "pp_e_holds (pp_e_eval C \<rho> (pp_reversible Z)) []"
      using original by (simp only: pp_reversible_def pp_e_eval_Exists_holds)
  qed
qed

theorem gi_T9_group_formula_root_iff:
  assumes typed: "\<Gamma> \<turnstile> Z : pp_unary_ty" and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval C \<rho> (pp_group_member Z)) [] \<longleftrightarrow>
    pp_e_eval C \<rho> Z \<in> gi_T9_root_group C"
proof -
  have pure: "pp_e_holds (pp_e_eval C \<rho> (pp_pure pp_unary_ty Z)) [] \<longleftrightarrow>
    pp_e_eval C \<rho> Z \<in> gi_T9_root_pure C gb_unary"
    using gi_T9_pure_formula_root_iff[OF typed env] by (simp only: pp_unary_ty_def)
  show ?thesis by (simp only: pp_group_member_def pp_e_eval_Conj_holds pure
    gi_T9_reversible_formula_root_iff[OF typed env] gi_T9_root_group_def mem_Collect_eq)
qed

theorem gi_T9_same_kind_formula_root_iff:
  assumes xt: "\<Gamma> \<turnstile> X : pp_unary_ty" and yt: "\<Gamma> \<turnstile> Y : pp_unary_ty"
    and env: "pp_e_env_typed \<Gamma> \<rho>"
  shows "pp_e_holds (pp_e_eval C \<rho> (pp_same_kind X Y)) [] \<longleftrightarrow>
    gi_T9_same_kind C (pp_e_eval C \<rho> X) (pp_e_eval C \<rho> Y)"
proof -
  let ?x = "pp_e_eval C \<rho> X"
  let ?y = "pp_e_eval C \<rho> Y"
  have xm: "Elem ?x (pp_e_domain gb_unary)" and ym: "Elem ?y (pp_e_domain gb_unary)"
    using pp_e_eval_type[OF xt env] pp_e_eval_type[OF yt env]
    by (simp_all only: pp_e_dom_def pp_unary_ty_def)
  let ?B = "\<lambda>W. pp_e_holds (pp_e_eval C (extend_env W \<rho>)
      (Conj (pp_group_member (Var 0))
        (Eq pp_unary_ty (shift X) (pp_compose (shift Y) (Var 0))))) []"
  have body_clause: "?B W \<longleftrightarrow>
      W \<in> gi_T9_root_group C \<and> ?x = gi_exact_value_compose ?y W"
    if wm: "Elem W (pp_e_domain gb_unary)" for W
  proof -
    have extended: "pp_e_env_typed (pp_unary_ty # \<Gamma>) (extend_env W \<rho>)"
      by (rule pp_e_env_typed_extend[OF env]; simp only: pp_unary_ty_def; rule wm)
    have group: "pp_e_holds (pp_e_eval C (extend_env W \<rho>) (pp_group_member (Var 0))) []
        \<longleftrightarrow> W \<in> gi_T9_root_group C"
      using gi_T9_group_formula_root_iff[OF typed_var0 extended] by simp
    have composed: "Elem (gi_exact_value_compose ?y W) (pp_e_domain gb_unary)"
      by (rule gi_exact_value_compose_member[OF ym wm])
    show ?thesis by (simp only: pp_e_eval_Conj_holds group pp_e_eval_Eq_holds gi_exact_eval_compose
      pp_e_eval_shift pp_e_eval.simps(1) extend_env.simps pp_unary_ty_def gi_exact_root_eqv[OF xm composed])
  qed
  show ?thesis
  proof
    assume holds: "pp_e_holds (pp_e_eval C \<rho> (pp_same_kind X Y)) []"
    have original: "\<exists>W. Elem W (pp_e_domain pp_unary_ty) \<and> ?B W"
      using holds by (simp only: pp_same_kind_def pp_e_eval_Exists_holds)
    then obtain W where wm0: "Elem W (pp_e_domain pp_unary_ty)" and body: "?B W" by blast
    have wm: "Elem W (pp_e_domain gb_unary)" using wm0 by (simp only: pp_unary_ty_def)
    have transformed: "W \<in> gi_T9_root_group C \<and> ?x = gi_exact_value_compose ?y W"
      using body body_clause[OF wm] by blast
    show "gi_T9_same_kind C ?x ?y" unfolding gi_T9_same_kind_def using transformed by blast
  next
    assume same: "gi_T9_same_kind C ?x ?y"
    then obtain W where wg: "W \<in> gi_T9_root_group C" and equation: "?x = gi_exact_value_compose ?y W"
      unfolding gi_T9_same_kind_def by blast
    have wm: "Elem W (pp_e_domain gb_unary)"
      using wg unfolding gi_T9_root_group_def gi_T9_root_pure_def by blast
    have body: "?B W" using wg equation body_clause[OF wm] by blast
    have wm0: "Elem W (pp_e_domain pp_unary_ty)" using wm by (simp only: pp_unary_ty_def)
    have original: "\<exists>W. Elem W (pp_e_domain pp_unary_ty) \<and> ?B W" using wm0 body by blast
    show "pp_e_holds (pp_e_eval C \<rho> (pp_same_kind X Y)) []"
      using original by (simp only: pp_same_kind_def pp_e_eval_Exists_holds)
  qed
qed

section \<open>Actual object-language L2 supplies the value-level transfer condition\<close>

theorem gi_T9_L2_root_instance:
  assumes truth: "pp_e_holds (pp_e_eval C \<rho> pp_L2) []"
    and xp: "X \<in> gi_T9_root_pure C gb_unary" and yp: "Y \<in> gi_T9_root_pure C gb_unary"
    and pm: "Elem p (pp_e_domain Prop)" and qm: "Elem q (pp_e_domain Prop)"
    and jp: "pp_e_holds (gi_T9_J_value C \<acute> p) []" and jq: "pp_e_holds (gi_T9_J_value C \<acute> q) []"
    and same: "X \<acute> p = Y \<acute> q"
  shows "gi_T9_same_kind C X Y"
proof -
  have xm: "Elem X (pp_e_domain gb_unary)" and ym: "Elem Y (pp_e_domain gb_unary)"
    using xp yp unfolding gi_T9_root_pure_def by auto
  let ?env = "extend_env q (extend_env p (extend_env Y (extend_env X \<rho>)))"
  let ?\<Gamma> = "[Prop, Prop, gb_unary, gb_unary]"
  have environment: "pp_e_env_typed ?\<Gamma> ?env"
    by (rule pp_e_env_typed_extend[OF pp_e_env_typed_extend[
      OF pp_e_env_typed_extend[OF pp_e_env_typed_extend[OF pp_e_empty_env_typed xm] ym] pm] qm])
  have pt: "?\<Gamma> \<turnstile> Var 1 : Prop" and qt: "?\<Gamma> \<turnstile> Var 0 : Prop"
    and xt: "?\<Gamma> \<turnstile> Var 3 : pp_unary_ty" and yt: "?\<Gamma> \<turnstile> Var 2 : pp_unary_ty"
    by (rule has_type.Var; simp add: lookup_def pp_unary_ty_def)+
  have px: "pp_e_holds (pp_e_eval C ?env (pp_pure pp_unary_ty (Var 3))) []"
    using xp by (simp only: gi_T9_pure_formula_root_iff[OF xt environment]; simp add: pp_unary_ty_def numeral_3_eq_3)
  have py: "pp_e_holds (pp_e_eval C ?env (pp_pure pp_unary_ty (Var 2))) []"
    using yp by (simp only: gi_T9_pure_formula_root_iff[OF yt environment]; simp add: pp_unary_ty_def)
  have pfp: "pp_e_holds (pp_e_eval C ?env (pp_fun_prime (Var 1))) []"
    using jp by (simp only: gi_T9_fun_prime_formula_holds[OF pt environment]; simp)
  have qfp: "pp_e_holds (pp_e_eval C ?env (pp_fun_prime (Var 0))) []"
    using jq by (simp only: gi_T9_fun_prime_formula_holds[OF qt environment]; simp)
  have xpm: "Elem (X \<acute> p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF xm pm])
  have yqm: "Elem (Y \<acute> q) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF ym qm])
  have x_eval: "pp_e_eval C ?env (App (Var 3) (Var 1)) = X \<acute> p" by (simp add: numeral_3_eq_3)
  have y_eval: "pp_e_eval C ?env (App (Var 2) (Var 0)) = Y \<acute> q" by simp
  have eq: "pp_e_holds (pp_e_eval C ?env (Eq Prop (App (Var 3) (Var 1)) (App (Var 2) (Var 0)))) []"
    by (simp only: pp_e_eval_Eq_holds x_eval y_eval gi_exact_root_eqv[OF xpm yqm]; rule same)
  have kind: "pp_e_holds (pp_e_eval C ?env (pp_same_kind (Var 3) (Var 2))) []"
    using truth xm ym pm qm px py pfp qfp eq
    unfolding pp_L2_def pp_unary_ty_def
    by (simp only: pp_e_eval_Forall_holds pp_e_eval_Imp_holds pp_e_eval_Conj_holds; blast)
  show ?thesis using kind
    by (simp only: gi_T9_same_kind_formula_root_iff[OF xt yt environment]; simp add: numeral_3_eq_3)
qed

end

section \<open>Language-guarded input from the native translated L2 formula\<close>

lemma gi_T9_L2_vocabulary:
  "consts_of pp_L2 \<subseteq> {pp_pure_name, pp_fun_name}"
  by (simp add: pp_L2_def pp_fun_prime_def pp_same_kind_def pp_group_member_def
    pp_reversible_def pp_compose_def pp_identity_operator_def pp_pure_def pp_Pure_def
    shift_def shift_by_def consts_of_rename)

lemma gi_T9_native_L2_language:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
  shows "book_theory_formula gb_signature G (gi_to_book G [] k pp_L2)"
  by (rule gi_to_book_language[OF rich typed_pp_L2 _ gi_L2_admitted[OF names]]; simp)

context pp_e_constants
begin

theorem gi_T9_native_L2_root_implies_source:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and truth: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2))"
  shows "pp_e_holds (pp_e_eval C pp_e_closed_env pp_L2) []"
proof -
  have denotation: "gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2) = pp_e_eval C pp_e_closed_env pp_L2"
    by (rule gi_exact_goodman_closed_denotation_translation[OF rich typed_pp_L2 typed names gi_T9_L2_vocabulary])
  show ?thesis using truth by (simp only: denotation gi_exact_valuation_def)
qed

theorem gi_T9_native_L2_root_instance:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and truth: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2))"
    and xp: "X \<in> gi_T9_root_pure C gb_unary" and yp: "Y \<in> gi_T9_root_pure C gb_unary"
    and pm: "Elem p (pp_e_domain Prop)" and qm: "Elem q (pp_e_domain Prop)"
    and jp: "pp_e_holds (gi_T9_J_value C \<acute> p) []" and jq: "pp_e_holds (gi_T9_J_value C \<acute> q) []"
    and same: "X \<acute> p = Y \<acute> q"
  shows "gi_T9_same_kind C X Y"
  by (rule gi_T9_L2_root_instance[OF gi_T9_native_L2_root_implies_source[OF rich names typed truth]
    xp yp pm qm jp jq same])

theorem gi_T9_L2_formula_implies_root_L2:
  assumes truth: "pp_e_holds (pp_e_eval C \<rho> pp_L2) []"
  shows "gi_T9_root_L2 C"
  unfolding gi_T9_root_L2_def
  by (intro ballI allI impI; rule gi_T9_L2_root_instance[OF truth]; assumption)

corollary gi_T9_native_L2_implies_root_L2:
  assumes rich: "sg_rich G" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and truth: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2))"
  shows "gi_T9_root_L2 C"
  by (rule gi_T9_L2_formula_implies_root_L2[OF gi_T9_native_L2_root_implies_source[OF rich names typed truth]])

end

text \<open>
  C is arbitrary subject to exact-carrier typing. These results do not
  silently substitute the fixed generic interpretation, and they do not
  assume its closed-logical stock equals an arbitrary root Pure extension.
  The reversible formula supplies only a pure inverse; the separate group
  formula supplies purity of the operator as well. All identities are
  converted to literal value equality only at the root.

  Native L2 is an explicit input, with the source vocabulary restricted
  to Pure/Fun and the target language separately verified. No derivation
  of L2 from PP, PC premise, or consistency claim is made here.
\<close>

end
