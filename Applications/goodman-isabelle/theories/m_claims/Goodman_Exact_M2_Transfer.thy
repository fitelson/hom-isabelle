theory Goodman_Exact_M2_Transfer
  imports Goodman_Legacy_M2.Bacon_PP_Goodman_M2
    Goodman_Integration_Exact_L2.Goodman_Exact_L2_Root_Semantics
begin

section \<open>Goodman's classifiers in Bacon's actual exact unary carrier\<close>

definition gi_exact_M2_view_condition :: "pp_sem_prop set \<Rightarrow> nat list \<Rightarrow> ZF \<Rightarrow> bool" where
  "gi_exact_M2_view_condition S w x \<longleftrightarrow> pp_view (rev w) (pp_n_bacon_extract x) \<in> S"

definition gi_exact_M2_classifier :: "pp_sem_prop set \<Rightarrow> ZF" where
  "gi_exact_M2_classifier S = pp_e_classifier Prop (gi_exact_M2_view_condition S)"

definition gi_exact_M2_invariant_stock :: "ZF set" where
  "gi_exact_M2_invariant_stock =
    {F. Elem F (pp_e_domain gb_unary) \<and> (\<forall>i. pp_b_action gb_unary i F = F)}"

lemma gi_exact_M2_extract_action:
  "pp_n_bacon_extract (pp_b_action Prop i x) = pp_view i (pp_n_bacon_extract x)"
  by (simp only: pp_b_action.simps pp_n_bacon_extract_action pp_prop_action_def)

lemma gi_exact_M2_view_condition_admissible:
  "pp_e_predicate_admissible Prop (gi_exact_M2_view_condition S)"
proof (unfold pp_e_predicate_admissible_def, intro allI impI)
  fix w x y v
  assume xm: "Elem x (pp_e_domain Prop)" and ym: "Elem y (pp_e_domain Prop)"
    and related: "pp_e_eqv Prop w x y" and future: "prefix w v"
  have later: "pp_e_eqv Prop v x y" by (rule pp_e_eqv_persistent[OF related future])
  have action: "pp_b_action Prop (rev v) x = pp_b_action Prop (rev v) y"
    using later by (simp only: pp_e_eqv_iff_action_eq[OF xm ym])
  have views: "pp_view (rev v) (pp_n_bacon_extract x) = pp_view (rev v) (pp_n_bacon_extract y)"
    using arg_cong[OF action, of pp_n_bacon_extract]
    by (simp only: gi_exact_M2_extract_action)
  show "gi_exact_M2_view_condition S v x = gi_exact_M2_view_condition S v y"
    by (simp only: gi_exact_M2_view_condition_def views)
qed

theorem gi_exact_M2_classifier_member:
  "Elem (gi_exact_M2_classifier S) (pp_e_domain gb_unary)"
  unfolding gi_exact_M2_classifier_def
  by (rule pp_e_classifier_in_domain[OF gi_exact_M2_view_condition_admissible])

lemma gi_exact_M2_classifier_apply:
  assumes xm: "Elem x (pp_e_domain Prop)"
  shows "gi_exact_M2_classifier S \<acute> x =
    pp_e_prop (\<lambda>w. pp_view (rev w) (pp_n_bacon_extract x) \<in> S)"
  unfolding gi_exact_M2_classifier_def
  by (simp only: pp_e_classifier_apply[OF xm] gi_exact_M2_view_condition_def)

theorem gi_exact_M2_classifier_raw:
  "pp_e_raw_operator (gi_exact_M2_classifier S) = pp_classifier S"
proof (rule ext, rule set_eqI)
  fix P i
  have pm: "Elem (pp_n_bacon_embed P) (pp_e_domain Prop)"
    using pp_n_bacon_embed_in_domain[of P] by simp
  show "i \<in> pp_e_raw_operator (gi_exact_M2_classifier S) P \<longleftrightarrow> i \<in> pp_classifier S P"
    by (simp add: pp_e_raw_operator_def gi_exact_M2_classifier_apply[OF pm]
      pp_n_bacon_extract_def pp_classifier_def)
qed

section \<open>Raw equivariance implies exact action invariance\<close>

lemma gi_exact_M2_raw_equivariant_commutes:
  assumes fm: "Elem F (pp_e_domain gb_unary)" and pm: "Elem p (pp_e_domain Prop)"
    and equivariant: "pp_equivariant_operator (pp_e_raw_operator F)"
  shows "pp_b_action Prop i (F \<acute> p) = F \<acute> pp_b_action Prop i p"
proof -
  have fp: "Elem (F \<acute> p) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF fm pm])
  have ip: "Elem (pp_b_action Prop i p) (pp_e_domain Prop)" by (rule pp_b_action_closed_all[OF pm])
  have ifp: "Elem (pp_b_action Prop i (F \<acute> p)) (pp_e_domain Prop)"
    by (rule pp_b_action_closed_all[OF fp])
  have fip: "Elem (F \<acute> pp_b_action Prop i p) (pp_e_domain Prop)"
    by (rule pp_e_app_closed[OF fm ip])
  have equiv: "pp_view i (pp_e_raw_operator F (pp_n_bacon_extract p)) =
    pp_e_raw_operator F (pp_view i (pp_n_bacon_extract p))"
    using equivariant unfolding pp_equivariant_operator_def by blast
  have extracted: "pp_n_bacon_extract (pp_b_action Prop i (F \<acute> p)) =
    pp_n_bacon_extract (F \<acute> pp_b_action Prop i p)"
    using equiv
    by (simp only: gi_exact_raw_at_extract[OF pm]
      gi_exact_M2_extract_action[symmetric] gi_exact_raw_at_extract[OF ip])
  have ifp_power: "Elem (pp_b_action Prop i (F \<acute> p)) (Power Nat)"
    using ifp by (simp only: pp_b_domain.simps)
  have fip_power: "Elem (F \<acute> pp_b_action Prop i p) (Power Nat)"
    using fip by (simp only: pp_b_domain.simps)
  show ?thesis by (rule pp_n_bacon_extract_injective_on_domain[OF ifp_power fip_power extracted])
qed

theorem gi_exact_M2_raw_equivariant_invariant:
  assumes fm: "Elem F (pp_e_domain gb_unary)"
    and equivariant: "pp_equivariant_operator (pp_e_raw_operator F)"
  shows "pp_b_action gb_unary i F = F"
proof -
  have ifm: "Elem (pp_b_action gb_unary i F) (pp_e_domain gb_unary)"
    by (rule pp_b_action_closed_all[OF fm])
  show ?thesis
  proof (rule pp_b_function_ext[OF pp_b_arrow_member_function[OF ifm] pp_b_arrow_member_function[OF fm]])
    fix p assume pm: "Elem p (pp_e_domain Prop)"
    obtain q where qm: "Elem q (pp_e_domain Prop)" and iq: "pp_b_action Prop i q = p"
      using pp_b_action_surjective_all[OF pm, of i] by blast
    have app: "pp_b_action gb_unary i F \<acute> pp_b_action Prop i q = pp_b_action Prop i (F \<acute> q)"
      by (rule pp_b_application_substitution_exact[OF fm qm])
    have commutes: "pp_b_action Prop i (F \<acute> q) = F \<acute> pp_b_action Prop i q"
      by (rule gi_exact_M2_raw_equivariant_commutes[OF fm qm equivariant])
    show "pp_b_action gb_unary i F \<acute> p = F \<acute> p"
      using app commutes by (simp only: iq)
  qed
qed

theorem gi_exact_M2_classifier_invariant:
  "pp_b_action gb_unary i (gi_exact_M2_classifier S) = gi_exact_M2_classifier S"
proof (rule gi_exact_M2_raw_equivariant_invariant[OF gi_exact_M2_classifier_member])
  show "pp_equivariant_operator (pp_e_raw_operator (gi_exact_M2_classifier S))"
    by (simp only: gi_exact_M2_classifier_raw; rule pp_classifier_equivariant_operator)
qed

lemma gi_exact_M2_classifier_in_stock:
  "gi_exact_M2_classifier S \<in> gi_exact_M2_invariant_stock"
  unfolding gi_exact_M2_invariant_stock_def
  using gi_exact_M2_classifier_member gi_exact_M2_classifier_invariant by blast

theorem gi_exact_M2_classifier_injective:
  "inj gi_exact_M2_classifier"
proof (rule injI)
  fix S T assume same: "gi_exact_M2_classifier S = gi_exact_M2_classifier T"
  have raw: "pp_classifier S = pp_classifier T"
    using arg_cong[OF same, of pp_e_raw_operator] by (simp only: gi_exact_M2_classifier_raw)
  show "S = T" by (rule injD[OF pp_classifier_injective raw])
qed

theorem gi_exact_M2_invariant_representation:
  assumes stock: "F \<in> gi_exact_M2_invariant_stock"
  shows "F = gi_exact_M2_classifier (pp_operator_index (pp_e_raw_operator F))"
proof -
  have fm: "Elem F (pp_e_domain gb_unary)" and invariant: "\<And>i. pp_b_action gb_unary i F = F"
    using stock unfolding gi_exact_M2_invariant_stock_def by blast+
  have equivariant: "pp_equivariant_operator (pp_e_raw_operator F)"
    by (rule pp_e_raw_operator_equivariant[OF fm invariant])
  have raw: "pp_e_raw_operator F =
    pp_e_raw_operator (gi_exact_M2_classifier (pp_operator_index (pp_e_raw_operator F)))"
    by (simp only: gi_exact_M2_classifier_raw; rule pp_equivariant_operator_is_classifier[OF equivariant])
  show ?thesis by (rule gi_exact_raw_operator_injective[OF fm gi_exact_M2_classifier_member raw])
qed

theorem gi_exact_M2_classifier_bijection:
  "bij_betw gi_exact_M2_classifier (UNIV :: pp_sem_prop set set) gi_exact_M2_invariant_stock"
  unfolding bij_betw_def
proof (rule conjI)
  show "inj_on gi_exact_M2_classifier (UNIV :: pp_sem_prop set set)"
    using gi_exact_M2_classifier_injective by (simp add: inj_on_def inj_def)
  show "gi_exact_M2_classifier ` (UNIV :: pp_sem_prop set set) = gi_exact_M2_invariant_stock"
  proof
    show "gi_exact_M2_classifier ` (UNIV :: pp_sem_prop set set) \<subseteq> gi_exact_M2_invariant_stock"
      using gi_exact_M2_classifier_in_stock by blast
    show "gi_exact_M2_invariant_stock \<subseteq> gi_exact_M2_classifier ` (UNIV :: pp_sem_prop set set)"
    proof
      fix F assume stock: "F \<in> gi_exact_M2_invariant_stock"
      have represented: "F = gi_exact_M2_classifier (pp_operator_index (pp_e_raw_operator F))"
        by (rule gi_exact_M2_invariant_representation[OF stock])
      show "F \<in> gi_exact_M2_classifier ` (UNIV :: pp_sem_prop set set)" using represented by blast
    qed
  qed
qed

section \<open>There are more exact invariant unary values than exact propositions\<close>

lemma gi_exact_M2_proposition_bijection:
  "bij_betw pp_n_bacon_embed (UNIV :: pp_sem_prop set) (gi_exact_domain Prop)"
  unfolding bij_betw_def
proof (rule conjI)
  show "inj_on pp_n_bacon_embed (UNIV :: pp_sem_prop set)"
  proof (rule inj_onI)
    fix p q assume "p \<in> UNIV" "q \<in> UNIV" and same: "pp_n_bacon_embed p = pp_n_bacon_embed q"
    show "p = q" using arg_cong[OF same, of pp_n_bacon_extract] by simp
  qed
  show "pp_n_bacon_embed ` (UNIV :: pp_sem_prop set) = gi_exact_domain Prop"
  proof
    show "pp_n_bacon_embed ` (UNIV :: pp_sem_prop set) \<subseteq> gi_exact_domain Prop"
      using pp_n_bacon_embed_in_domain by (auto simp: gi_exact_domain_member)
    show "gi_exact_domain Prop \<subseteq> pp_n_bacon_embed ` (UNIV :: pp_sem_prop set)"
    proof
      fix p assume member: "p \<in> gi_exact_domain Prop"
      have power: "Elem p (Power Nat)" using member by (simp only: gi_exact_domain_member pp_b_domain.simps)
      have same: "pp_n_bacon_embed (pp_n_bacon_extract p) = p" by (rule pp_n_bacon_embed_extract[OF power])
      show "p \<in> pp_n_bacon_embed ` (UNIV :: pp_sem_prop set)"
        by (rule image_eqI[where x="pp_n_bacon_extract p"];
          (rule same[symmetric] | rule UNIV_I))
    qed
  qed
qed

theorem gi_exact_M2_invariants_outnumber_propositions:
  "gi_exact_domain Prop \<prec> gi_exact_M2_invariant_stock"
proof -
  have prop_eq: "(UNIV :: pp_sem_prop set) \<approx> gi_exact_domain Prop"
    unfolding eqpoll_def by (rule exI[where x=pp_n_bacon_embed], rule gi_exact_M2_proposition_bijection)
  have cantor: "(UNIV :: pp_sem_prop set) \<prec> (UNIV :: pp_sem_prop set set)"
    using lesspoll_Pow_self[of "(UNIV :: pp_sem_prop set)"] by simp
  have class_eq: "(UNIV :: pp_sem_prop set set) \<approx> gi_exact_M2_invariant_stock"
    unfolding eqpoll_def by (rule exI[where x=gi_exact_M2_classifier], rule gi_exact_M2_classifier_bijection)
  have raw_less: "(UNIV :: pp_sem_prop set) \<prec> gi_exact_M2_invariant_stock"
    by (rule lesspoll_eq_trans[OF cantor class_eq])
  show ?thesis by (rule eq_lesspoll_trans[OF eqpoll_sym[OF prop_eq] raw_less])
qed

section \<open>A concrete exact-carrier collision at every proposed fundamental proposition\<close>

theorem gi_exact_M2_collision:
  assumes rm: "R \<in> gi_exact_domain Prop"
  shows "\<exists>F H. F \<in> gi_exact_M2_invariant_stock \<and> H \<in> gi_exact_M2_invariant_stock \<and>
    F \<noteq> H \<and> F \<acute> R = H \<acute> R"
proof -
  let ?P = "pp_n_bacon_extract R"
  let ?F = "gi_exact_M2_classifier {pp_M2_orbit_diagonal ?P}"
  let ?H = "gi_exact_M2_classifier {}"
  have fm: "Elem ?F (pp_e_domain gb_unary)" and hm: "Elem ?H (pp_e_domain gb_unary)"
    by (rule gi_exact_M2_classifier_member)+
  have r: "Elem R (pp_e_domain Prop)" using rm by (simp only: gi_exact_domain_member)
  have raw_equal: "pp_e_raw_operator ?F ?P = pp_e_raw_operator ?H ?P"
    by (simp only: gi_exact_M2_classifier_raw pp_M2_singleton_classifier_vanishes_at_R
      pp_M2_empty_classifier)
  have app_equal: "?F \<acute> R = ?H \<acute> R"
    using raw_equal gi_exact_raw_application_eq_iff[OF fm hm r r] by blast
  have different: "?F \<noteq> ?H"
  proof
    assume same: "?F = ?H"
    have "{pp_M2_orbit_diagonal ?P} = {}"
      by (rule injD[OF gi_exact_M2_classifier_injective same])
    then show False by simp
  qed
  show ?thesis by (rule exI[where x="?F"], rule exI[where x="?H"])
    (use gi_exact_M2_classifier_in_stock[of "{pp_M2_orbit_diagonal ?P}"]
      gi_exact_M2_classifier_in_stock[of "{}"] different app_equal in blast)
qed

theorem gi_exact_M2_evaluation_not_injective:
  assumes rm: "R \<in> gi_exact_domain Prop"
  shows "\<not> inj_on (\<lambda>F. F \<acute> R) gi_exact_M2_invariant_stock"
  using gi_exact_M2_collision[OF rm] unfolding inj_on_def by blast

corollary gi_exact_M2_invariance_QSS_fails:
  assumes rm: "R \<in> gi_exact_domain Prop"
  shows "\<not> (\<forall>F\<in>gi_exact_M2_invariant_stock. \<forall>H\<in>gi_exact_M2_invariant_stock.
    F \<acute> R = H \<acute> R \<longrightarrow> F = H)"
  using gi_exact_M2_collision[OF rm] by blast

text \<open>
  The classifiers are values of Bacon's recursively restricted exact
  unary carrier, and the invariance equation uses its actual action.
  The cardinal comparison and collision now concern those exact values,
  not only their raw representations or a secondary Boolean tree.

  No classifier is asserted to be closed-logically denotable. Invariant
  values are not thereby Pure. The final QSS obstruction says that one
  cannot certify every invariant unary value pure while retaining
  injectivity of evaluation at a fundamental proposition. It is not an
  independent construction of all other background axioms with that
  proposed reading, nor a PP theorem or consistency result.
\<close>

end
