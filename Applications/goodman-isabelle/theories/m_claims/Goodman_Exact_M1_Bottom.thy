theory Goodman_Exact_M1_Bottom
  imports "Goodman_Integration_Exact_QLN.Goodman_Exact_Generic_Interpretation"
begin

section \<open>Proposition purity is noncontingency in the exact complete stock\<close>

lemma gi_M1_exact_closed_truth:
  "pp_e_holds (pp_e_closed_den ObjTrue) w"
  by (simp add: pp_e_closed_den_def pp_e_eval_ObjTrue)

lemma gi_M1_exact_closed_falsity:
  "\<not> pp_e_holds (pp_e_closed_den ObjFalse) w"
  by (simp add: pp_e_closed_den_def ObjFalse_def pp_e_eval_ObjTrue)

theorem gi_M1_exact_proposition_stock_noncontingency:
  assumes member: "Elem p (pp_e_domain Prop)"
  shows "pp_e_closed_logical_stock Prop w p \<longleftrightarrow>
    ((\<forall>v. prefix w v \<longrightarrow> pp_e_holds p v) \<or>
     (\<forall>v. prefix w v \<longrightarrow> \<not> pp_e_holds p v))"
proof
  assume stock: "pp_e_closed_logical_stock Prop w p"
  obtain M where typed: "[] \<turnstile> M : Prop"
    and related: "pp_e_eqv Prop w p (pp_e_closed_den M)"
    using stock unfolding pp_e_closed_logical_stock_def by blast
  have uniform: "pp_e_holds p v = pp_e_holds (pp_e_closed_den M) []"
    if future: "prefix w v" for v
    using pp_e_prop_eqv_at[OF related future]
      pp_e_closed_prop_den_world_constant[OF typed, where v=v] by blast
  show "(\<forall>v. prefix w v \<longrightarrow> pp_e_holds p v) \<or>
      (\<forall>v. prefix w v \<longrightarrow> \<not> pp_e_holds p v)"
    using uniform by (cases "pp_e_holds (pp_e_closed_den M) []") blast+
next
  assume noncontingent: "(\<forall>v. prefix w v \<longrightarrow> pp_e_holds p v) \<or>
      (\<forall>v. prefix w v \<longrightarrow> \<not> pp_e_holds p v)"
  then show "pp_e_closed_logical_stock Prop w p"
  proof
    assume always_true: "\<forall>v. prefix w v \<longrightarrow> pp_e_holds p v"
    have related: "pp_e_eqv Prop w p (pp_e_closed_den ObjTrue)"
      using always_true by (simp only: pp_e_eqv.simps gi_M1_exact_closed_truth; simp)
    have typed: "[] \<turnstile> ObjTrue : Prop" by (rule typed_ObjTrue)
    have logical: "pp_logical_vocabulary ObjTrue"
      by (simp add: pp_logical_vocabulary_def ObjTrue_def)
    show ?thesis unfolding pp_e_closed_logical_stock_def
      using member typed logical related by blast
  next
    assume always_false: "\<forall>v. prefix w v \<longrightarrow> \<not> pp_e_holds p v"
    have related: "pp_e_eqv Prop w p (pp_e_closed_den ObjFalse)"
      using always_false gi_M1_exact_closed_falsity
      by (simp only: pp_e_eqv.simps; blast)
    have typed: "[] \<turnstile> ObjFalse : Prop" by (rule typed_ObjFalse)
    have logical: "pp_logical_vocabulary ObjFalse"
      by (simp add: pp_logical_vocabulary_def ObjFalse_def ObjTrue_def)
    show ?thesis unfolding pp_e_closed_logical_stock_def
      using member typed logical related by blast
  qed
qed

section \<open>The displayed closed logical term NC = λp.(□p ∨ □¬p)\<close>

definition gi_M1_NC_body :: "sgcontext \<Rightarrow> 'c book_named_term" where
  "gi_M1_NC_body G = book_or G
    (book_box G (NVar (gb_x G Prop)))
    (book_box G (book_not G (NVar (gb_x G Prop))))"

definition gi_M1_NC :: "sgcontext \<Rightarrow> 'c book_named_term" where
  "gi_M1_NC G = NLam (gb_x G Prop) (gi_M1_NC_body G)"

lemma gi_M1_NC_body_language:
  assumes rich: "sg_rich G"
  shows "book_theory_formula \<Sigma> G (gi_M1_NC_body G)"
  unfolding gi_M1_NC_body_def
  by (intro book_or_language[OF rich] book_box_language[OF rich]
      book_not_language[OF rich] gb_x_language[OF rich])

lemma gi_M1_NC_language:
  assumes rich: "sg_rich G"
  shows "book_in_language book_minimal_logical_type UNIV \<Sigma> G (gi_M1_NC G) gb_unary"
proof -
  have abstraction: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
      (NLam (gb_x G Prop) (gi_M1_NC_body G)) (Arr (G (gb_x G Prop)) Prop)"
    by (rule book_language_Lam[OF gi_M1_NC_body_language[OF rich]])
  show ?thesis using abstraction
    by (simp only: gi_M1_NC_def gb_names_type(1)[OF rich])
qed

lemma gi_M1_NC_closed:
  "named_fv (gi_M1_NC G) = {}"
  by (simp add: gi_M1_NC_def gi_M1_NC_body_def book_or_fv book_box_fv book_not_fv)

lemma gi_M1_NC_closed_logical:
  assumes rich: "sg_rich G"
  shows "gb_closed_logical G gb_unary (gi_M1_NC G)"
  unfolding gb_closed_logical_def
  by (rule conjI[OF gi_M1_NC_language[OF rich] gi_M1_NC_closed])

lemma gi_M1_NC_string_rename:
  "gi_goodman_string_term (gi_M1_NC G) = gi_M1_NC G"
  by (simp only: gi_M1_NC_def gi_M1_NC_body_def book_typed_name_map.simps
      gi_typed_name_map_or book_full_typed_name_map_box book_typed_name_map_not)

context pp_e_constants
begin

lemma gi_M1_NC_body_holds:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
  shows "pp_e_holds (gi_exact_named_denote C G g (gi_M1_NC_body G)) w =
    ((\<forall>v. prefix w v \<longrightarrow> pp_e_holds (g (gb_x G Prop)) v) \<or>
     (\<forall>v. prefix w v \<longrightarrow> \<not> pp_e_holds (g (gb_x G Prop)) v))"
proof -
  let ?p = "NVar (gb_x G Prop) :: string book_named_term"
  have pl: "book_theory_formula (\<lambda>_. UNIV) G ?p" by (rule gb_x_language[OF rich])
  have npl: "book_theory_formula (\<lambda>_. UNIV) G (book_not G ?p)"
    by (rule book_not_language[OF rich pl])
  have bpl: "book_theory_formula (\<lambda>_. UNIV) G (book_box G ?p)"
    by (rule book_box_language[OF rich pl])
  have bnpl: "book_theory_formula (\<lambda>_. UNIV) G (book_box G (book_not G ?p))"
    by (rule book_box_language[OF rich npl])
  show ?thesis
    by (simp only: gi_M1_NC_body_def gi_exact_named_or_holds[OF rich typed bpl bnpl]
        gi_exact_named_box_holds[OF rich typed pl] gi_exact_named_box_holds[OF rich typed npl]
        gi_exact_named_not_holds[OF rich typed pl] gi_exact_named_denote_var)
qed

theorem gi_M1_NC_denotes_exact_classifier:
  assumes rich: "sg_rich G" and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_named_denote C G g (gi_M1_NC G) =
    pp_e_classifier Prop (pp_e_closed_logical_stock Prop)"
proof -
  let ?F = "gi_exact_named_denote C G g (gi_M1_NC G)"
  let ?H = "pp_e_classifier Prop (pp_e_closed_logical_stock Prop)"
  let ?n = "gb_x G Prop"
  have nt: "G ?n = Prop" by (rule gb_names_type(1)[OF rich])
  have fm: "Elem ?F (pp_e_domain gb_unary)"
    using gi_exact_named_denote_type[OF gi_M1_NC_language[OF rich, where \<Sigma>="\<lambda>_. UNIV"] typed]
    by (simp only: gi_exact_domain_member)
  have hm: "Elem ?H (pp_e_domain gb_unary)"
    by (rule pp_e_classifier_in_domain[OF pp_e_closed_logical_stock_admissible])
  show ?thesis
  proof (rule pp_b_function_ext[OF pp_b_arrow_member_function[OF fm] pp_b_arrow_member_function[OF hm]])
    fix p
    assume pm: "Elem p (pp_e_domain Prop)"
    have named_member: "p \<in> gi_exact_domain (G ?n)"
      by (simp only: nt gi_exact_domain_member; rule pm)
    have updated: "book_env_typed gi_exact_domain G (g(?n := p))"
      by (rule book_env_update[OF typed named_member])
    have application: "?F \<acute> p = gi_exact_named_denote C G (g(?n := p)) (gi_M1_NC_body G)"
      using gi_exact_named_lambda_application[
        OF rich gi_M1_NC_body_language[OF rich, where \<Sigma>="\<lambda>_. UNIV"] typed named_member]
      by (simp only: gi_M1_NC_def gi_exact_app_value nt)
    have fp: "Elem (?F \<acute> p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF fm pm])
    have hp: "Elem (?H \<acute> p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF hm pm])
    show "?F \<acute> p = ?H \<acute> p"
    proof (rule pp_e_prop_ext[OF fp hp])
      fix w
      have left_truth: "pp_e_holds (?F \<acute> p) w =
          ((\<forall>v. prefix w v \<longrightarrow> pp_e_holds p v) \<or>
           (\<forall>v. prefix w v \<longrightarrow> \<not> pp_e_holds p v))"
        by (simp only: application gi_M1_NC_body_holds[OF rich updated] fun_upd_same)
      have right_truth: "pp_e_holds (?H \<acute> p) w =
          ((\<forall>v. prefix w v \<longrightarrow> pp_e_holds p v) \<or>
           (\<forall>v. prefix w v \<longrightarrow> \<not> pp_e_holds p v))"
        by (simp only: pp_e_classifier_holds[OF pm] gi_M1_exact_proposition_stock_noncontingency[OF pm])
      show "pp_e_holds (?F \<acute> p) w = pp_e_holds (?H \<acute> p) w"
        by (simp only: left_truth right_truth)
    qed
  qed
qed

end

lemma gi_M1_NC_native_closed_denotation:
  assumes rich: "sg_rich G"
  shows "gi_exact_native_closed_den G (gi_M1_NC G) =
    pp_e_classifier Prop (pp_e_closed_logical_stock Prop)"
proof -
  have constants: "pp_e_constants pp_e_default_constants"
    by standard (simp add: pp_e_default_constants_def pp_e_default_in_domain)
  show ?thesis
    unfolding gi_exact_native_closed_den_def gi_exact_goodman_denote_def
    by (simp only: gi_M1_NC_string_rename;
      rule pp_e_constants.gi_M1_NC_denotes_exact_classifier[
        OF constants rich gi_exact_default_assignment_typed])
qed

theorem gi_M1_exact_bottom_classifier_in_native_stock:
  assumes rich: "sg_rich G"
  shows "gi_exact_native_logical_stock G gb_unary w
    (pp_e_classifier Prop (pp_e_closed_logical_stock Prop))"
proof -
  have logical: "gb_closed_logical G gb_unary (gi_M1_NC G :: gb_term)"
    by (rule gi_M1_NC_closed_logical[OF rich])
  have member: "gi_exact_native_closed_den G (gi_M1_NC G) \<in> gi_exact_domain gb_unary"
    by (rule gi_exact_native_closed_den_member[OF logical])
  have related: "book_leibniz_equiv gi_exact_domain gi_exact_app (gi_exact_valuation w) gb_unary
      (gi_exact_native_closed_den G (gi_M1_NC G)) (gi_exact_native_closed_den G (gi_M1_NC G))"
    by (rule book_leibniz_refl[where D=gi_exact_domain and app=gi_exact_app
      and V="gi_exact_valuation w" and \<sigma>=gb_unary, OF member])
  have stock: "gi_exact_native_logical_stock G gb_unary w (gi_exact_native_closed_den G (gi_M1_NC G))"
    unfolding gi_exact_native_logical_stock_def
    by (rule conjI[OF member], rule exI[where x="gi_M1_NC G"], rule conjI[OF logical related])
  show ?thesis using stock by (simp only: gi_M1_NC_native_closed_denotation[OF rich])
qed

theorem gi_M1_exact_native_purity_is_noncontingency:
  assumes rich: "sg_rich G" and language: "book_theory_formula gb_signature G A"
    and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_valuation w (gi_exact_goodman_denote pp_e_generic_internal_constants G g (gb_pure Prop A))
    \<longleftrightarrow>
    ((\<forall>v. prefix w v \<longrightarrow> pp_e_holds (gi_exact_goodman_denote pp_e_generic_internal_constants G g A) v) \<or>
     (\<forall>v. prefix w v \<longrightarrow> \<not> pp_e_holds (gi_exact_goodman_denote pp_e_generic_internal_constants G g A) v))"
proof -
  have member: "Elem (gi_exact_goodman_denote pp_e_generic_internal_constants G g A) (pp_e_domain Prop)"
    using gi_exact_generic_native_denote_type[OF language typed] by (simp only: gi_exact_domain_member)
  show ?thesis by (simp only: gi_exact_generic_native_pure_holds[OF rich language typed]
      gi_exact_native_stock_iff_original[OF rich] gi_M1_exact_proposition_stock_noncontingency[OF member])
qed

theorem gi_M1_exact_bottom_PP_gvalid:
  assumes rich: "sg_rich G"
  shows "gi_exact_goodman_global_valid pp_e_generic_internal_constants G (gb_purity_of_pure Prop)"
proof (unfold gi_exact_goodman_global_valid_iff, intro allI impI)
  fix w g
  assume typed: "book_env_typed gi_exact_domain G g"
  have language: "book_in_language book_minimal_logical_type UNIV gb_signature G (gb_Pure Prop) gb_unary"
    by (rule gb_Pure_language)
  have stock: "gi_exact_native_logical_stock G gb_unary w
      (gi_exact_goodman_denote pp_e_generic_internal_constants G g (gb_Pure Prop))"
    by (simp only: gi_exact_generic_Pure_denotation; rule gi_M1_exact_bottom_classifier_in_native_stock[OF rich])
  show "gi_exact_valuation w
      (gi_exact_goodman_denote pp_e_generic_internal_constants G g (gb_purity_of_pure Prop))"
    unfolding gb_purity_of_pure_def
    using gi_exact_generic_native_pure_holds[OF rich language typed, where w=w] stock by blast
qed

text \<open>
  This verifies M1's bottom-type observation by an actual closed logical
  denotation on Bacon's exact carriers. The conclusion is Pureₜ→ₜ(Pureₜ),
  expressed by gb_purity_of_pure Prop. It is NOT gb_target_PP, which asks
  for purity of the unary-operator classifier at the next type. No claim
  that arbitrary invariant operators are logically definable is used.
\<close>

end
