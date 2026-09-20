theory Goodman_T9_Infinitude
  imports Goodman_T9_Native_Conclusion
begin

section \<open>Invertible left composition permutes the actual kinds\<close>

text \<open>
  This instantiates the finite-kind exclusion argument of the original
  Bacon_PP_Goodman_T9_Infinitude.thy (SHA256
  11de3683edb5fa2b18fdb3760c0a20162be46909663b53220aa07e758566f529).
  Unlike the older abstract action interface, the exact application law
  below is used only on typed proposition arguments. In particular both
  r and B·r are proved to belong to the proposition carrier when needed.
\<close>

definition gi_T9_left_action where
  "gi_T9_left_action C Z k = gi_T9_kind C (gi_exact_value_compose Z (gi_T9_kind_rep C k))"

definition gi_T9_cardinality_subset :: "'a set \<Rightarrow> nat \<Rightarrow> 'a set" where
  "gi_T9_cardinality_subset A n = (SOME B. B \<subseteq> A \<and> card B = n)"

lemma gi_T9_cardinality_subset_spec:
  assumes bound: "n \<le> card A"
  shows "gi_T9_cardinality_subset A n \<subseteq> A \<and> card (gi_T9_cardinality_subset A n) = n"
proof -
  obtain B where subset: "B \<subseteq> A" and card_eq: "card B = n"
    using obtain_subset_with_card_n[OF bound] by blast
  have witness: "\<exists>B. B \<subseteq> A \<and> card B = n" using subset card_eq by blast
  show ?thesis unfolding gi_T9_cardinality_subset_def by (rule someI_ex[OF witness])
qed

context gi_T9_native_purity
begin

lemma gi_T9_left_composition_respects_kind:
  assumes zg: "Z \<in> gi_T9_root_group C"
    and xp: "X \<in> gi_T9_root_pure C gb_unary" and yp: "Y \<in> gi_T9_root_pure C gb_unary"
    and same: "gi_T9_kind C X = gi_T9_kind C Y"
  shows "gi_T9_kind C (gi_exact_value_compose Z X) = gi_T9_kind C (gi_exact_value_compose Z Y)"
proof -
  have zp: "Z \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_group_pure[OF zg])
  have related: "gi_T9_same_kind C X Y" by (rule iffD1[OF gi_T9_kind_eq_iff[OF xp yp] same])
  obtain H where hg: "H \<in> gi_T9_root_group C" and shape: "X = gi_exact_value_compose Y H"
    using related unfolding gi_T9_same_kind_def by blast
  have hp: "H \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_group_pure[OF hg])
  have zxp: "gi_exact_value_compose Z X \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_compose_pure[OF zp xp])
  have zyp: "gi_exact_value_compose Z Y \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_compose_pure[OF zp yp])
  have equation: "gi_exact_value_compose Z X = gi_exact_value_compose (gi_exact_value_compose Z Y) H"
    by (simp only: shape gi_T9_compose_associative[OF zp yp hp])
  have related_outputs: "gi_T9_same_kind C (gi_exact_value_compose Z X) (gi_exact_value_compose Z Y)"
    unfolding gi_T9_same_kind_def using hg equation by blast
  show ?thesis by (rule iffD2[OF gi_T9_kind_eq_iff[OF zxp zyp] related_outputs])
qed

lemma gi_T9_left_action_member:
  assumes zg: "Z \<in> gi_T9_root_group C" and kind: "k \<in> gi_T9_kinds C"
  shows "gi_T9_left_action C Z k \<in> gi_T9_kinds C"
proof -
  have zp: "Z \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_group_pure[OF zg])
  have rp: "gi_T9_kind_rep C k \<in> gi_T9_root_pure C gb_unary"
    using gi_T9_kind_rep_spec[OF kind] by blast
  show ?thesis unfolding gi_T9_left_action_def
    by (rule gi_T9_pure_kind_member[OF gi_T9_compose_pure[OF zp rp]])
qed

theorem gi_T9_left_action_bijective:
  assumes zg: "Z \<in> gi_T9_root_group C"
  shows "bij_betw (gi_T9_left_action C Z) (gi_T9_kinds C) (gi_T9_kinds C)"
proof -
  obtain I where ig: "I \<in> gi_T9_root_group C"
    and inverse: "\<forall>X\<in>gi_T9_root_pure C gb_unary.
      gi_exact_value_compose I (gi_exact_value_compose Z X) = X \<and>
      gi_exact_value_compose Z (gi_exact_value_compose I X) = X"
    using gi_T9_group_inverse_action[OF zg] by blast
  have zp: "Z \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_group_pure[OF zg])
  have ip: "I \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_group_pure[OF ig])
  have into: "gi_T9_left_action C Z ` gi_T9_kinds C \<subseteq> gi_T9_kinds C"
    using gi_T9_left_action_member[OF zg] by blast
  have injective: "inj_on (gi_T9_left_action C Z) (gi_T9_kinds C)"
  proof (rule inj_onI)
    fix k l
    assume km: "k \<in> gi_T9_kinds C" and lm: "l \<in> gi_T9_kinds C"
      and same: "gi_T9_left_action C Z k = gi_T9_left_action C Z l"
    have kp: "gi_T9_kind_rep C k \<in> gi_T9_root_pure C gb_unary"
      using gi_T9_kind_rep_spec[OF km] by blast
    have lp: "gi_T9_kind_rep C l \<in> gi_T9_root_pure C gb_unary"
      using gi_T9_kind_rep_spec[OF lm] by blast
    have zkp: "gi_exact_value_compose Z (gi_T9_kind_rep C k) \<in> gi_T9_root_pure C gb_unary"
      by (rule gi_T9_compose_pure[OF zp kp])
    have zlp: "gi_exact_value_compose Z (gi_T9_kind_rep C l) \<in> gi_T9_root_pure C gb_unary"
      by (rule gi_T9_compose_pure[OF zp lp])
    have same_outputs: "gi_T9_kind C (gi_exact_value_compose Z (gi_T9_kind_rep C k)) =
      gi_T9_kind C (gi_exact_value_compose Z (gi_T9_kind_rep C l))"
      using same unfolding gi_T9_left_action_def .
    have transported: "gi_T9_kind C (gi_exact_value_compose I (gi_exact_value_compose Z (gi_T9_kind_rep C k))) =
      gi_T9_kind C (gi_exact_value_compose I (gi_exact_value_compose Z (gi_T9_kind_rep C l)))"
      by (rule gi_T9_left_composition_respects_kind[OF ig zkp zlp same_outputs])
    have cancel_k: "gi_exact_value_compose I (gi_exact_value_compose Z (gi_T9_kind_rep C k)) = gi_T9_kind_rep C k"
      using inverse kp by blast
    have cancel_l: "gi_exact_value_compose I (gi_exact_value_compose Z (gi_T9_kind_rep C l)) = gi_T9_kind_rep C l"
      using inverse lp by blast
    have same_representatives: "gi_T9_kind C (gi_T9_kind_rep C k) = gi_T9_kind C (gi_T9_kind_rep C l)"
      using transported by (simp only: cancel_k cancel_l)
    show "k = l" using same_representatives gi_T9_kind_rep_spec[OF km] gi_T9_kind_rep_spec[OF lm] by blast
  qed
  have onto: "gi_T9_kinds C \<subseteq> gi_T9_left_action C Z ` gi_T9_kinds C"
  proof
    fix k assume km: "k \<in> gi_T9_kinds C"
    let ?B = "gi_T9_kind_rep C k"
    let ?IB = "gi_exact_value_compose I ?B"
    let ?j = "gi_T9_kind C ?IB"
    have bp: "?B \<in> gi_T9_root_pure C gb_unary" using gi_T9_kind_rep_spec[OF km] by blast
    have ibp: "?IB \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_compose_pure[OF ip bp])
    have jm: "?j \<in> gi_T9_kinds C" by (rule gi_T9_pure_kind_member[OF ibp])
    have jp: "gi_T9_kind_rep C ?j \<in> gi_T9_root_pure C gb_unary" using gi_T9_kind_rep_spec[OF jm] by blast
    have jkind: "gi_T9_kind C (gi_T9_kind_rep C ?j) = gi_T9_kind C ?IB"
      using gi_T9_kind_rep_spec[OF jm] by blast
    have transported: "gi_T9_kind C (gi_exact_value_compose Z (gi_T9_kind_rep C ?j)) =
      gi_T9_kind C (gi_exact_value_compose Z ?IB)"
      by (rule gi_T9_left_composition_respects_kind[OF zg jp ibp jkind])
    have cancel: "gi_exact_value_compose Z ?IB = ?B" using inverse bp by blast
    have bk: "gi_T9_kind C ?B = k" using gi_T9_kind_rep_spec[OF km] by blast
    have action_value: "gi_T9_left_action C Z ?j = k"
      using transported by (simp only: gi_T9_left_action_def cancel bk)
    show "k \<in> gi_T9_left_action C Z ` gi_T9_kinds C"
      by (rule image_eqI[where f="gi_T9_left_action C Z" and A="gi_T9_kinds C" and x="?j",
        OF action_value[symmetric] jm])
  qed
  show ?thesis unfolding bij_betw_def using injective into onto by blast
qed

section \<open>Selector collisions preserve the cardinality of selected kinds\<close>

theorem gi_T9_selector_collision_covariance:
  assumes pc: "gi_T9_full_unary_PC C" and l2: "gi_T9_root_L2 C"
    and rm: "Elem r (pp_e_domain Prop)" and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []"
    and ss: "S \<subseteq> gi_T9_kinds C" and ts: "T \<subseteq> gi_T9_kinds C"
    and same: "gi_T9_kind C (gi_T9_kind_selector C S) = gi_T9_kind C (gi_T9_kind_selector C T)"
  obtains Z where "Z \<in> gi_T9_root_group C"
    "bij_betw (gi_T9_left_action C Z) (gi_T9_kinds C) (gi_T9_kinds C)"
    "gi_T9_left_action C Z ` S = T"
proof -
  let ?cS = "gi_T9_kind_selector C S"
  let ?cT = "gi_T9_kind_selector C T"
  have sp: "?cS \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_kind_selector_pure[OF pc ss])
  have tp: "?cT \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_kind_selector_pure[OF pc ts])
  have related: "gi_T9_same_kind C ?cS ?cT" by (rule iffD1[OF gi_T9_kind_eq_iff[OF sp tp] same])
  obtain Z where zg: "Z \<in> gi_T9_root_group C" and equation: "?cS = gi_exact_value_compose ?cT Z"
    using related unfolding gi_T9_same_kind_def by blast
  have zp: "Z \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_group_pure[OF zg])
  have bijective: "bij_betw (gi_T9_left_action C Z) (gi_T9_kinds C) (gi_T9_kinds C)"
    by (rule gi_T9_left_action_bijective[OF zg])
  have membership: "k \<in> S \<longleftrightarrow> gi_T9_left_action C Z k \<in> T"
    if km: "k \<in> gi_T9_kinds C" for k
  proof -
    let ?B = "gi_T9_kind_rep C k"
    let ?ZB = "gi_exact_value_compose Z ?B"
    have bp: "?B \<in> gi_T9_root_pure C gb_unary" using gi_T9_kind_rep_spec[OF km] by blast
    have bk: "gi_T9_kind C ?B = k" using gi_T9_kind_rep_spec[OF km] by blast
    have zbp: "?ZB \<in> gi_T9_root_pure C gb_unary" by (rule gi_T9_compose_pure[OF zp bp])
    have bm: "Elem ?B (pp_e_domain gb_unary)" by (rule gi_T9_root_pure_member[OF bp])
    have brm: "Elem (?B \<acute> r) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF bm rm])
    have application: "?cS \<acute> (?B \<acute> r) = ?cT \<acute> (?ZB \<acute> r)"
      by (simp only: equation gi_T9_value_compose_apply[OF brm] gi_T9_value_compose_apply[OF rm])
    have truth: "pp_e_holds (?cS \<acute> (?B \<acute> r)) [] = pp_e_holds (?cT \<acute> (?ZB \<acute> r)) []"
      by (rule arg_cong[where f="\<lambda>p. pp_e_holds p []", OF application])
    have s_spec: "pp_e_holds (?cS \<acute> (?B \<acute> r)) [] \<longleftrightarrow> k \<in> S"
      using gi_T9_kind_selector_spec[OF pc l2 rm jr ss bp] by (simp only: bk)
    have t_spec: "pp_e_holds (?cT \<acute> (?ZB \<acute> r)) [] \<longleftrightarrow> gi_T9_left_action C Z k \<in> T"
      using gi_T9_kind_selector_spec[OF pc l2 rm jr ts zbp] by (simp only: gi_T9_left_action_def)
    show ?thesis using s_spec t_spec truth by blast
  qed
  have image_equal: "gi_T9_left_action C Z ` S = T"
  proof
    show "gi_T9_left_action C Z ` S \<subseteq> T"
    proof
      fix k assume "k \<in> gi_T9_left_action C Z ` S"
      then obtain j where js: "j \<in> S" and shape: "k = gi_T9_left_action C Z j" by blast
      have jm: "j \<in> gi_T9_kinds C" by (rule subsetD[OF ss js])
      show "k \<in> T" using membership[OF jm] js by (simp only: shape; blast)
    qed
    show "T \<subseteq> gi_T9_left_action C Z ` S"
    proof
      fix k assume kt: "k \<in> T"
      have km: "k \<in> gi_T9_kinds C" by (rule subsetD[OF ts kt])
      have onto: "gi_T9_left_action C Z ` gi_T9_kinds C = gi_T9_kinds C"
        using bijective unfolding bij_betw_def by blast
      have kimage: "k \<in> gi_T9_left_action C Z ` gi_T9_kinds C"
        using km by (simp only: onto)
      obtain j where jm: "j \<in> gi_T9_kinds C" and action_value: "gi_T9_left_action C Z j = k"
        using kimage by (elim imageE) simp
      have js: "j \<in> S" using membership[OF jm] kt action_value by blast
      show "k \<in> gi_T9_left_action C Z ` S"
        by (rule image_eqI[where f="gi_T9_left_action C Z" and A=S and x=j,
          OF action_value[symmetric] js])
    qed
  qed
  show thesis by (rule that[OF zg bijective image_equal])
qed

theorem gi_T9_selector_collision_preserves_card:
  assumes pc: "gi_T9_full_unary_PC C" and l2: "gi_T9_root_L2 C"
    and rm: "Elem r (pp_e_domain Prop)" and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []"
    and ss: "S \<subseteq> gi_T9_kinds C" and ts: "T \<subseteq> gi_T9_kinds C"
    and same: "gi_T9_kind C (gi_T9_kind_selector C S) = gi_T9_kind C (gi_T9_kind_selector C T)"
  shows "card S = card T"
proof -
  obtain Z where bijective: "bij_betw (gi_T9_left_action C Z) (gi_T9_kinds C) (gi_T9_kinds C)"
    and image_equal: "gi_T9_left_action C Z ` S = T"
    using gi_T9_selector_collision_covariance[OF pc l2 rm jr ss ts same] by blast
  have injective: "inj_on (gi_T9_left_action C Z) S"
    using bijective ss unfolding bij_betw_def by (meson inj_on_subset)
  have image_card: "card (gi_T9_left_action C Z ` S) = card S" by (rule card_image[OF injective])
  show ?thesis using image_card by (simp only: image_equal)
qed

section \<open>There cannot be finitely many actual kinds\<close>

theorem gi_T9_native_PC_L2_infinitely_many_kinds:
  assumes pc: "gi_T9_full_unary_PC C" and l2: "gi_T9_root_L2 C"
    and rm: "Elem r (pp_e_domain Prop)" and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []"
  shows "infinite (gi_T9_kinds C)"
proof
  assume finite_K: "finite (gi_T9_kinds C)"
  let ?K = "gi_T9_kinds C"
  let ?I = "{..card ?K}"
  let ?S = "gi_T9_cardinality_subset ?K"
  let ?f = "\<lambda>n. gi_T9_kind C (gi_T9_kind_selector C (?S n))"
  have subset: "?S n \<subseteq> ?K" if member: "n \<in> ?I" for n
  proof -
    have bound: "n \<le> card ?K" using member by simp
    show ?thesis using gi_T9_cardinality_subset_spec[OF bound] by blast
  qed
  have selected_card: "card (?S n) = n" if member: "n \<in> ?I" for n
  proof -
    have bound: "n \<le> card ?K" using member by simp
    show ?thesis using gi_T9_cardinality_subset_spec[OF bound] by blast
  qed
  have range_subset: "?f ` ?I \<subseteq> ?K"
  proof
    fix k assume "k \<in> ?f ` ?I"
    then obtain n where member: "n \<in> ?I" and shape: "k = ?f n" by blast
    have pure: "gi_T9_kind_selector C (?S n) \<in> gi_T9_root_pure C gb_unary"
      by (rule gi_T9_kind_selector_pure[OF pc subset[OF member]])
    show "k \<in> ?K" by (simp only: shape; rule gi_T9_pure_kind_member[OF pure])
  qed
  have injective: "inj_on ?f ?I"
  proof (rule inj_onI)
    fix m n
    assume mm: "m \<in> ?I" and nm: "n \<in> ?I" and same: "?f m = ?f n"
    have same_card: "card (?S m) = card (?S n)"
      by (rule gi_T9_selector_collision_preserves_card[OF pc l2 rm jr subset[OF mm] subset[OF nm] same])
    show "m = n" using same_card by (simp only: selected_card[OF mm] selected_card[OF nm])
  qed
  have image_card: "card (?f ` ?I) = Suc (card ?K)" using injective by (simp add: card_image)
  have upper: "card (?f ` ?I) \<le> card ?K" by (rule card_mono[OF finite_K range_subset])
  show False using upper image_card by simp
qed

theorem gi_T9_native_PC_L2_exponential_group_bound:
  assumes pc: "gi_T9_full_unary_PC C" and l2: "gi_T9_root_L2 C"
    and rm: "Elem r (pp_e_domain Prop)" and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []"
  shows "|Pow (gi_T9_kinds C)| \<le>o |gi_T9_root_group C|"
  by (rule gi_T9_infinite_kinds_group_bound[OF pc l2 rm jr
      gi_T9_native_PC_L2_infinitely_many_kinds[OF pc l2 rm jr]])

section \<open>Infinitude and the group bound from actual native formula inputs\<close>

corollary gi_T9_native_formula_infinitely_many_kinds:
  assumes pc: "gi_T9_full_unary_PC C" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and l2: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2))"
    and exists_fp: "gi_exact_valuation []
      (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_exists_fun_prime))"
  shows "infinite (gi_T9_kinds C)"
proof -
  have semantic_l2: "gi_T9_root_L2 C"
    by (rule gi_T9_native_L2_implies_root_L2[OF rich names typed l2])
  obtain r where rm: "Elem r (pp_e_domain Prop)"
    and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []"
    using gi_T9_native_exists_fun_prime_root_witness[OF rich names typed exists_fp] by blast
  show ?thesis by (rule gi_T9_native_PC_L2_infinitely_many_kinds[OF pc semantic_l2 rm jr])
qed

corollary gi_T9_native_formula_exponential_group_bound:
  assumes pc: "gi_T9_full_unary_PC C" and names: "gi_goodman_names k"
    and typed: "book_env_typed gi_exact_domain G g"
    and l2: "gi_exact_valuation [] (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_L2))"
    and exists_fp: "gi_exact_valuation []
      (gi_exact_goodman_denote C G g (gi_to_book G [] k pp_exists_fun_prime))"
  shows "|Pow (gi_T9_kinds C)| \<le>o |gi_T9_root_group C|"
  by (rule gi_T9_native_formula_infinite_kinds_bound[OF pc names typed l2 exists_fp
      gi_T9_native_formula_infinitely_many_kinds[OF pc names typed l2 exists_fp]])

end

text \<open>
  Full external unary PC and the actual L2 selector specification exclude
  the finite horn of T9 for these actual values and kinds. No assumption
  about the cardinal size or a classification of the reversible group is
  used. All applications in the collision calculation have explicitly
  typed proposition arguments; the unrestricted meta-domain composition
  law from the older abstract locale has not been assumed. The native
  purity locale, full external PC, semantic L2, and typed fun′ witness
  remain hypotheses; no model satisfying them is constructed here.
  The final two corollaries obtain semantic L2 and the typed witness from
  the actual translated native L2 and ∃fun′ formulas. Their external PC
  premise is not weakened to definable or Henkin-representable subsets.
\<close>

end
