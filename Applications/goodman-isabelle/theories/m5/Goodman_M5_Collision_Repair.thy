theory Goodman_M5_Collision_Repair
  imports Goodman_M5_Local_Collision_Counterexample
    Goodman_Integration_Exact_L2.Goodman_Exact_Kind_Root
begin

section \<open>A different, unconditional semantic collision for the same operator\<close>

text \<open>
  The failure of the local NC(r) collision does not make the historical
  operator F(p) = (p ↔ NC(p)) injective. In this exact model a simpler pair
  works: P = UNIV − {[]} and truth. NC(P) = P, so F(P) = UNIV = F(UNIV),
  while P ≠ UNIV. This is a semantic calculation in Bacon's exact model;
  it is not presented as a new CEV+ proof or as a PP countermodel.
\<close>

definition gi_M5_punctured_truth :: pp_sem_prop where
  "gi_M5_punctured_truth = UNIV - {[]}"

lemma gi_M5_punctured_truth_nonextreme:
  "gi_M5_punctured_truth \<noteq> {}" "gi_M5_punctured_truth \<noteq> UNIV"
proof -
  have member: "[0] \<in> gi_M5_punctured_truth" by (simp add: gi_M5_punctured_truth_def)
  have excluded: "[] \<notin> gi_M5_punctured_truth" by (simp add: gi_M5_punctured_truth_def)
  show "gi_M5_punctured_truth \<noteq> {}" using member by blast
  show "gi_M5_punctured_truth \<noteq> UNIV" using excluded by blast
qed

lemma gi_M5_punctured_truth_view:
  "pp_view i gi_M5_punctured_truth = (if i = [] then gi_M5_punctured_truth else UNIV)"
  by (cases "i = []"; auto simp: pp_view_def gi_M5_punctured_truth_def)

lemma gi_M5_punctured_truth_NC:
  "gi_M5_raw_NC gi_M5_punctured_truth = gi_M5_punctured_truth"
proof (rule set_eqI)
  fix i
  have criterion: "i \<in> gi_M5_raw_NC gi_M5_punctured_truth \<longleftrightarrow>
    pp_view i gi_M5_punctured_truth = UNIV \<or> pp_view i gi_M5_punctured_truth = {}"
    by (auto simp: gi_M5_raw_NC_def pp_sem_box_def gi_M5_view_complement)
  show "i \<in> gi_M5_raw_NC gi_M5_punctured_truth \<longleftrightarrow> i \<in> gi_M5_punctured_truth"
  proof (cases "i = []")
    case True
    have view: "pp_view i gi_M5_punctured_truth = gi_M5_punctured_truth" by (simp add: True)
    have excluded: "i \<notin> gi_M5_punctured_truth" by (simp add: True gi_M5_punctured_truth_def)
    show ?thesis using criterion view excluded gi_M5_punctured_truth_nonextreme by blast
  next
    case False
    have view: "pp_view i gi_M5_punctured_truth = UNIV"
      using gi_M5_punctured_truth_view[of i] False by simp
    have member: "i \<in> gi_M5_punctured_truth" using False by (simp add: gi_M5_punctured_truth_def)
    show ?thesis using criterion view member by blast
  qed
qed

theorem gi_M5_raw_corrected_collision:
  "gi_M5_raw_collision gi_M5_punctured_truth = UNIV"
  "gi_M5_raw_collision UNIV = UNIV"
  "gi_M5_punctured_truth \<noteq> UNIV"
proof -
  show "gi_M5_raw_collision gi_M5_punctured_truth = UNIV"
    by (simp only: gi_M5_raw_collision_def gi_M5_punctured_truth_NC; simp)
  show "gi_M5_raw_collision UNIV = UNIV" by (rule gi_M5_raw_collision_truth)
  show "gi_M5_punctured_truth \<noteq> UNIV" by (rule gi_M5_punctured_truth_nonextreme(2))
qed

lemma gi_M5_collision_operator_logical:
  "pp_logical_vocabulary pp_M5_collision_operator"
  by (simp add: pp_logical_vocabulary_def pp_M5_collision_operator_def pp_noncontingent_def ObjBox_def ObjTrue_def)

lemma gi_M5_collision_operator_denotation:
  "pp_e_eval C \<rho> pp_M5_collision_operator = pp_e_closed_den pp_M5_collision_operator"
  by (rule gi_exact_old_closed_evaluation[OF typed_pp_M5_collision_operator gi_M5_collision_operator_logical])

lemma gi_M5_collision_operator_member:
  "Elem (pp_e_closed_den pp_M5_collision_operator) (pp_e_domain gb_unary)"
  by (rule pp_e_closed_den_in_domain[OF typed_pp_M5_collision_operator[unfolded pp_unary_ty_def]])

lemma gi_M5_collision_application_extract:
  assumes pm: "Elem p (pp_e_domain Prop)"
  shows "pp_n_bacon_extract (pp_e_closed_den pp_M5_collision_operator \<acute> p) =
    gi_M5_raw_collision (pp_n_bacon_extract p)"
proof -
  have member: "Elem (pp_e_eval pp_e_default_constants (extend_env p pp_e_closed_env) (Var 0)) (pp_e_domain Prop)"
    using pm by simp
  have evaluated: "pp_n_bacon_extract (pp_e_eval pp_e_default_constants (extend_env p pp_e_closed_env)
    (App pp_M5_collision_operator (Var 0))) =
    gi_M5_raw_collision (pp_n_bacon_extract (pp_e_eval pp_e_default_constants (extend_env p pp_e_closed_env) (Var 0)))"
    by (rule gi_M5_eval_collision_raw[OF member])
  show ?thesis using evaluated by (simp only: pp_e_eval.simps(1,3) gi_M5_collision_operator_denotation extend_env.simps)
qed

theorem gi_M5_collision_operator_raw:
  "pp_e_raw_operator (pp_e_closed_den pp_M5_collision_operator) = gi_M5_raw_collision"
proof (rule ext)
  fix P
  have pm: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)" using pp_n_bacon_embed_in_domain[of P] by simp
  show "pp_e_raw_operator (pp_e_closed_den pp_M5_collision_operator) P = gi_M5_raw_collision P"
    by (simp only: pp_e_raw_operator_def gi_M5_collision_application_extract[OF pm]; simp)
qed

lemma gi_M5_equal_propositions_from_extract:
  assumes xm: "Elem x (pp_e_domain Prop)" and ym: "Elem y (pp_e_domain Prop)"
    and same: "pp_n_bacon_extract x = pp_n_bacon_extract y"
  shows "x = y"
proof -
  have xp: "Elem x (Power Nat)" and yp: "Elem y (Power Nat)" using xm ym by simp_all
  show ?thesis by (rule pp_n_bacon_extract_injective_on_domain[OF xp yp same])
qed

theorem gi_M5_exact_corrected_collision:
  "pp_n_bacon_embed gi_M5_punctured_truth \<noteq> pp_zf_truth True"
  "pp_e_closed_den pp_M5_collision_operator \<acute> pp_n_bacon_embed gi_M5_punctured_truth = pp_zf_truth True"
  "pp_e_closed_den pp_M5_collision_operator \<acute> pp_zf_truth True = pp_zf_truth True"
proof -
  have pm: "Elem (pp_n_bacon_embed gi_M5_punctured_truth) (pp_e_domain Prop)"
    using pp_n_bacon_embed_in_domain[of gi_M5_punctured_truth] by simp
  have tm: "Elem (pp_zf_truth True) (pp_e_domain Prop)" by (rule pp_e_truth_in_domain)
  have truth_raw: "pp_n_bacon_extract (pp_zf_truth True) = UNIV"
    using gi_M5_eval_truth_raw[where C=pp_e_default_constants and \<rho>=pp_e_closed_env]
    by (simp only: pp_e_eval_ObjTrue)
  show "pp_n_bacon_embed gi_M5_punctured_truth \<noteq> pp_zf_truth True"
  proof
    assume same: "pp_n_bacon_embed gi_M5_punctured_truth = pp_zf_truth True"
    have "gi_M5_punctured_truth = UNIV"
      using arg_cong[OF same, where f=pp_n_bacon_extract] truth_raw by simp
    then show False using gi_M5_punctured_truth_nonextreme(2) by contradiction
  qed
  show "pp_e_closed_den pp_M5_collision_operator \<acute> pp_n_bacon_embed gi_M5_punctured_truth = pp_zf_truth True"
  proof (rule gi_M5_equal_propositions_from_extract[OF pp_e_app_closed[OF gi_M5_collision_operator_member pm] tm])
    show "pp_n_bacon_extract (pp_e_closed_den pp_M5_collision_operator \<acute> pp_n_bacon_embed gi_M5_punctured_truth) =
      pp_n_bacon_extract (pp_zf_truth True)"
      by (simp only: gi_M5_collision_application_extract[OF pm] truth_raw;
        simp add: gi_M5_raw_corrected_collision(1))
  qed
  show "pp_e_closed_den pp_M5_collision_operator \<acute> pp_zf_truth True = pp_zf_truth True"
    by (rule gi_M5_equal_propositions_from_extract[OF pp_e_app_closed[OF gi_M5_collision_operator_member tm] tm];
      simp only: gi_M5_collision_application_extract[OF tm] truth_raw gi_M5_raw_collision_truth)
qed

theorem gi_M5_exact_operator_not_injective:
  "\<not> inj_on (\<lambda>p. pp_e_closed_den pp_M5_collision_operator \<acute> p) (gi_exact_domain Prop)"
proof
  assume injective: "inj_on (\<lambda>p. pp_e_closed_den pp_M5_collision_operator \<acute> p) (gi_exact_domain Prop)"
  have pm: "pp_n_bacon_embed gi_M5_punctured_truth \<in> gi_exact_domain Prop"
    using pp_n_bacon_embed_in_domain[of gi_M5_punctured_truth] by (simp add: gi_exact_domain_member)
  have tm: "pp_zf_truth True \<in> gi_exact_domain Prop"
    using pp_e_truth_in_domain[of True] by (simp only: gi_exact_domain_member)
  have same_output: "pp_e_closed_den pp_M5_collision_operator \<acute> pp_n_bacon_embed gi_M5_punctured_truth =
    pp_e_closed_den pp_M5_collision_operator \<acute> pp_zf_truth True"
    by (simp only: gi_M5_exact_corrected_collision(2,3))
  have same_input: "pp_n_bacon_embed gi_M5_punctured_truth = pp_zf_truth True"
    by (rule inj_onD[OF injective same_output pm tm])
  show False by (rule notE[OF gi_M5_exact_corrected_collision(1) same_input])
qed

section \<open>The actual existential collision sentence is true at the root\<close>

definition gi_M5_corrected_collision_sentence :: oterm where
  "gi_M5_corrected_collision_sentence = Exists Prop
    (Conj (Neg (Eq Prop (Var 0) ObjTrue))
      (Eq Prop (App pp_M5_collision_operator (Var 0)) (App pp_M5_collision_operator ObjTrue)))"

lemma gi_M5_corrected_collision_sentence_typed:
  "[] \<turnstile> gi_M5_corrected_collision_sentence : Prop"
proof -
  have ft: "[Prop] \<turnstile> pp_M5_collision_operator : Arr Prop Prop"
    using typed_pp_M5_collision_operator[where \<Gamma>="[Prop]"] by (simp only: pp_unary_ty_def)
  have left: "[Prop] \<turnstile> App pp_M5_collision_operator (Var 0) : Prop"
    by (rule has_type.App[OF ft typed_var0])
  have right: "[Prop] \<turnstile> App pp_M5_collision_operator ObjTrue : Prop"
    by (rule has_type.App[OF ft typed_ObjTrue])
  show ?thesis unfolding gi_M5_corrected_collision_sentence_def
    by (intro has_type.Exists has_type.Conj has_type.Neg has_type.Eq typed_var0 typed_ObjTrue left right)
qed

theorem gi_M5_corrected_collision_sentence_root:
  "pp_e_holds (pp_e_eval C \<rho> gi_M5_corrected_collision_sentence) []"
proof -
  let ?p = "pp_n_bacon_embed gi_M5_punctured_truth"
  let ?F = "pp_e_closed_den pp_M5_collision_operator"
  have pm: "Elem ?p (pp_e_domain Prop)" using pp_n_bacon_embed_in_domain[of gi_M5_punctured_truth] by simp
  have tm: "Elem (pp_zf_truth True) (pp_e_domain Prop)" by (rule pp_e_truth_in_domain)
  have fm: "Elem ?F (pp_e_domain gb_unary)" by (rule gi_M5_collision_operator_member)
  have fp: "Elem (?F \<acute> ?p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF fm pm])
  have ft: "Elem (?F \<acute> pp_zf_truth True) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF fm tm])
  show ?thesis unfolding gi_M5_corrected_collision_sentence_def
  proof (simp only: pp_e_eval_Exists_holds, rule exI[where x="?p"], rule conjI[OF pm])
    show "pp_e_holds (pp_e_eval C (extend_env ?p \<rho>)
      (Conj (Neg (Eq Prop (Var 0) ObjTrue))
        (Eq Prop (App pp_M5_collision_operator (Var 0)) (App pp_M5_collision_operator ObjTrue)))) []"
      by (simp only: pp_e_eval_Conj_holds pp_e_eval_Neg_holds pp_e_eval_Eq_holds
        pp_e_eval.simps(1,3) gi_M5_collision_operator_denotation pp_e_eval_ObjTrue extend_env.simps
        gi_exact_root_eqv[OF pm tm] gi_exact_root_eqv[OF fp ft] gi_M5_exact_corrected_collision;
        simp)
  qed
qed

section \<open>No inverse exists; root nonreversibility in the original exact interpretation\<close>

lemma gi_M5_raw_collision_no_left_inverse:
  "\<not> (\<exists>W :: pp_e_operator. W \<circ> gi_M5_raw_collision = id)"
proof
  assume "\<exists>W :: pp_e_operator. W \<circ> gi_M5_raw_collision = id"
  then obtain W where inverse: "W \<circ> gi_M5_raw_collision = id" by blast
  have a: "W UNIV = gi_M5_punctured_truth"
    using fun_cong[OF inverse, of gi_M5_punctured_truth] by (simp add: gi_M5_raw_corrected_collision(1))
  have b: "W UNIV = UNIV" using fun_cong[OF inverse, of UNIV] by (simp add: gi_M5_raw_collision_truth)
  have impossible: "gi_M5_punctured_truth = UNIV" using a b by simp
  show False by (rule notE[OF gi_M5_punctured_truth_nonextreme(2) impossible])
qed

theorem gi_M5_actual_nonreversibility_at_root:
  "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (Neg (pp_reversible pp_M5_collision_operator))) []"
proof (simp only: pp_e_eval_Neg_holds, intro notI)
  assume reversible: "pp_e_holds (pp_e_eval pp_e_generic_internal_constants \<rho> (pp_reversible pp_M5_collision_operator)) []"
  have inverses: "\<exists>W\<in>pp_e_exact_operator_stock.
    gi_M5_raw_collision \<circ> W = id \<and> W \<circ> gi_M5_raw_collision = id"
    using reversible gi_exact_reversible_root_iff[OF typed_pp_M5_collision_operator pp_e_empty_env_typed,
      where \<rho>=\<rho>]
    by (simp only: gi_M5_collision_operator_denotation gi_M5_collision_operator_raw)
  have left_inverse: "\<exists>W :: pp_e_operator. W \<circ> gi_M5_raw_collision = id" using inverses by blast
  show False by (rule notE[OF gi_M5_raw_collision_no_left_inverse left_inverse])
qed

theorem gi_M5_native_corrected_collision_at_root:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap" and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_valuation [] (gi_exact_goodman_denote pp_e_generic_internal_constants G g
    (gi_to_book G [] cmap gi_M5_corrected_collision_sentence))"
proof -
  have vocabulary: "consts_of gi_M5_corrected_collision_sentence \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: gi_M5_corrected_collision_sentence_def pp_M5_collision_operator_def
      pp_noncontingent_def ObjBox_def ObjTrue_def)
  have denotation: "gi_exact_goodman_denote pp_e_generic_internal_constants G g (gi_to_book G [] cmap gi_M5_corrected_collision_sentence) =
    pp_e_eval pp_e_generic_internal_constants pp_e_closed_env gi_M5_corrected_collision_sentence"
    by (rule pp_e_constants.gi_exact_goodman_closed_denotation_translation[OF gi_exact_generic_constants rich
      gi_M5_corrected_collision_sentence_typed typed names vocabulary])
  show ?thesis by (simp only: denotation gi_exact_valuation_def; rule gi_M5_corrected_collision_sentence_root)
qed

theorem gi_M5_native_actual_nonreversibility_at_root:
  assumes rich: "sg_rich G" and names: "gi_goodman_names cmap" and typed: "book_env_typed gi_exact_domain G g"
  shows "gi_exact_valuation [] (gi_exact_goodman_denote pp_e_generic_internal_constants G g
    (gi_to_book G [] cmap (Neg (pp_reversible pp_M5_collision_operator))))"
proof -
  have source_type: "[] \<turnstile> Neg (pp_reversible pp_M5_collision_operator) : Prop"
    by (rule has_type.Neg, rule typed_pp_reversible, rule typed_pp_M5_collision_operator)
  have vocabulary: "consts_of (Neg (pp_reversible pp_M5_collision_operator)) \<subseteq> {pp_pure_name, pp_fun_name}"
    by (simp add: pp_reversible_def pp_compose_def pp_identity_operator_def pp_pure_def pp_Pure_def
      pp_M5_collision_operator_def pp_noncontingent_def ObjBox_def ObjTrue_def shift_def consts_of_rename)
  have denotation: "gi_exact_goodman_denote pp_e_generic_internal_constants G g
    (gi_to_book G [] cmap (Neg (pp_reversible pp_M5_collision_operator))) =
      pp_e_eval pp_e_generic_internal_constants pp_e_closed_env (Neg (pp_reversible pp_M5_collision_operator))"
    by (rule pp_e_constants.gi_exact_goodman_closed_denotation_translation[
      OF gi_exact_generic_constants rich source_type typed names vocabulary])
  show ?thesis by (simp only: denotation gi_exact_valuation_def; rule gi_M5_actual_nonreversibility_at_root)
qed

text \<open>
  The corrected witnesses are punctured truth and truth, not NC(r) and
  truth for an arbitrary locally fun′ r. The actual historical operator
  has equal exact values on these unequal inputs. Its existential collision
  sentence and its nonreversibility are verified at the root of the exact
  interpretation. These semantic conclusions do not turn the invalid local
  fun′⇒NC(r)-collision inference into a valid one, and do not claim a new
  object-language theorem from CEV+, PP, or existence of a fundamental entity.
\<close>

end
