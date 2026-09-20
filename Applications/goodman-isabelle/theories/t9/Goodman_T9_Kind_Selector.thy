theory Goodman_T9_Kind_Selector
  imports Goodman_T9_PC_Selector Goodman_T9_Root_Algebra
begin

section \<open>One unary selector for each external set of kinds\<close>

definition gi_T9_root_L2 where
  "gi_T9_root_L2 C \<longleftrightarrow>
    (\<forall>X\<in>gi_T9_root_pure C gb_unary. \<forall>Y\<in>gi_T9_root_pure C gb_unary.
      \<forall>p q. Elem p (pp_e_domain Prop) \<longrightarrow> Elem q (pp_e_domain Prop) \<longrightarrow>
        pp_e_holds (gi_T9_J_value C \<acute> p) [] \<longrightarrow>
        pp_e_holds (gi_T9_J_value C \<acute> q) [] \<longrightarrow>
        X \<acute> p = Y \<acute> q \<longrightarrow> gi_T9_same_kind C X Y)"

definition gi_T9_kind_selector where
  "gi_T9_kind_selector C S = gi_T9_PC_lowered C (\<Union>S)"

context gi_T9_native_purity
begin

lemma gi_T9_union_kinds_pure:
  assumes subset: "S \<subseteq> gi_T9_kinds C"
  shows "\<Union>S \<subseteq> gi_T9_root_pure C gb_unary"
  using subset unfolding gi_T9_kinds_def gi_T9_kind_def by blast

lemma gi_T9_member_kind_iff:
  assumes kind: "k \<in> gi_T9_kinds C" and xp: "X \<in> gi_T9_root_pure C gb_unary"
  shows "X \<in> k \<longleftrightarrow> gi_T9_kind C X = k"
proof -
  obtain Y where yp: "Y \<in> gi_T9_root_pure C gb_unary" and ky: "k = gi_T9_kind C Y"
    using gi_T9_kind_represented[OF kind] by blast
  have symmetry: "gi_T9_same_kind C Y X \<longleftrightarrow> gi_T9_same_kind C X Y"
    using gi_T9_same_kind_sym[OF yp xp] gi_T9_same_kind_sym[OF xp yp] by blast
  have member: "X \<in> k \<longleftrightarrow> gi_T9_same_kind C Y X"
    using xp by (simp add: ky gi_T9_kind_def)
  show ?thesis using member symmetry gi_T9_kind_eq_iff[OF xp yp] ky by blast
qed

lemma gi_T9_member_union_kinds_iff:
  assumes subset: "S \<subseteq> gi_T9_kinds C" and xp: "X \<in> gi_T9_root_pure C gb_unary"
  shows "X \<in> \<Union>S \<longleftrightarrow> gi_T9_kind C X \<in> S"
proof
  assume "X \<in> \<Union>S"
  then obtain k where ks: "k \<in> S" and xk: "X \<in> k" by blast
  have kg: "k \<in> gi_T9_kinds C" by (rule subsetD[OF subset ks])
  have same: "gi_T9_kind C X = k" using xk gi_T9_member_kind_iff[OF kg xp] by blast
  show "gi_T9_kind C X \<in> S" by (simp only: same; rule ks)
next
  assume ks: "gi_T9_kind C X \<in> S"
  show "X \<in> \<Union>S" using ks gi_T9_kind_self_member[OF xp] by blast
qed

theorem gi_T9_kind_selector_pure:
  assumes pc: "gi_T9_full_unary_PC C" and subset: "S \<subseteq> gi_T9_kinds C"
  shows "gi_T9_kind_selector C S \<in> gi_T9_root_pure C gb_unary"
  unfolding gi_T9_kind_selector_def
  by (rule gi_T9_PC_lowered_pure[OF pc gi_T9_union_kinds_pure[OF subset]])

theorem gi_T9_kind_selector_spec:
  assumes pc: "gi_T9_full_unary_PC C" and l2: "gi_T9_root_L2 C"
    and rm: "Elem r (pp_e_domain Prop)" and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []"
    and subset: "S \<subseteq> gi_T9_kinds C" and bp: "B \<in> gi_T9_root_pure C gb_unary"
  shows "pp_e_holds (gi_T9_kind_selector C S \<acute> (B \<acute> r)) [] \<longleftrightarrow>
    gi_T9_kind C B \<in> S"
proof -
  have bm: "Elem B (pp_e_domain gb_unary)" using bp unfolding gi_T9_root_pure_def by blast
  have brm: "Elem (B \<acute> r) (pp_e_domain Prop)" by (rule pp_e_app_closed[OF bm rm])
  have union: "\<Union>S \<subseteq> gi_T9_root_pure C gb_unary" by (rule gi_T9_union_kinds_pure[OF subset])
  have calculation: "pp_e_holds (gi_T9_kind_selector C S \<acute> (B \<acute> r)) [] \<longleftrightarrow>
    (\<exists>X\<in>\<Union>S. \<exists>q. Elem q (pp_e_domain Prop) \<and>
      pp_e_holds (gi_T9_J_value C \<acute> q) [] \<and> B \<acute> r = X \<acute> q)"
    unfolding gi_T9_kind_selector_def by (rule gi_T9_PC_lowered_spec[OF pc union brm])
  show ?thesis
  proof
    assume truth: "pp_e_holds (gi_T9_kind_selector C S \<acute> (B \<acute> r)) []"
    obtain X q where xu: "X \<in> \<Union>S" and qm: "Elem q (pp_e_domain Prop)"
      and jq: "pp_e_holds (gi_T9_J_value C \<acute> q) []" and collision: "B \<acute> r = X \<acute> q"
      using truth calculation by blast
    have xp: "X \<in> gi_T9_root_pure C gb_unary" by (rule subsetD[OF union xu])
    have same: "gi_T9_same_kind C B X" using l2 bp xp rm qm jr jq collision unfolding gi_T9_root_L2_def by blast
    have equal: "gi_T9_kind C B = gi_T9_kind C X" using same gi_T9_kind_eq_iff[OF bp xp] by blast
    have selected: "gi_T9_kind C X \<in> S" using xu gi_T9_member_union_kinds_iff[OF subset xp] by blast
    show "gi_T9_kind C B \<in> S" by (simp only: equal; rule selected)
  next
    assume selected: "gi_T9_kind C B \<in> S"
    have bu: "B \<in> \<Union>S" using selected gi_T9_member_union_kinds_iff[OF subset bp] by blast
    have rhs: "\<exists>X\<in>\<Union>S. \<exists>q. Elem q (pp_e_domain Prop) \<and>
      pp_e_holds (gi_T9_J_value C \<acute> q) [] \<and> B \<acute> r = X \<acute> q"
      by (rule bexI[where x=B], rule exI[where x=r]) (use bu rm jr in auto)
    show "pp_e_holds (gi_T9_kind_selector C S \<acute> (B \<acute> r)) []" using calculation rhs by blast
  qed
qed

theorem gi_T9_kind_selector_injective:
  assumes pc: "gi_T9_full_unary_PC C" and l2: "gi_T9_root_L2 C"
    and rm: "Elem r (pp_e_domain Prop)" and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []"
  shows "inj_on (gi_T9_kind_selector C) (Pow (gi_T9_kinds C))"
proof (rule inj_onI)
  fix S T
  assume sp: "S \<in> Pow (gi_T9_kinds C)" and tp: "T \<in> Pow (gi_T9_kinds C)"
    and equal: "gi_T9_kind_selector C S = gi_T9_kind_selector C T"
  have ss: "S \<subseteq> gi_T9_kinds C" and ts: "T \<subseteq> gi_T9_kinds C" using sp tp by auto
  have membership: "k \<in> S \<longleftrightarrow> k \<in> T" if kg: "k \<in> gi_T9_kinds C" for k
  proof -
    obtain B where bp: "B \<in> gi_T9_root_pure C gb_unary" and bk: "gi_T9_kind C B = k"
      using gi_T9_kind_represented[OF kg] by blast
    show ?thesis using gi_T9_kind_selector_spec[OF pc l2 rm jr ss bp]
      gi_T9_kind_selector_spec[OF pc l2 rm jr ts bp] by (simp only: bk equal)
  qed
  show "S = T" using ss ts membership by blast
qed

end

text \<open>
  The selector injection now concerns the full external powerset of the
  actual kinds and actual pure unary values. L2 remains an explicit
  semantic premise here; its connection to the source formula is a
  separate lemma. The group-cardinality conclusion is not yet asserted.
\<close>

end
