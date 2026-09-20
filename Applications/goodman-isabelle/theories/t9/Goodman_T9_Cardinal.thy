theory Goodman_T9_Cardinal
  imports Goodman_T9_Kind_Selector
begin

unbundle cardinal_syntax

section \<open>Cardinal arithmetic used in Goodman's T9\<close>

text \<open>
  The two set-theoretic lemmas below adapt the corresponding checked
  arguments in the original Bacon_PP_Goodman_T9.thy (SHA256
  0445bff25dfff379c0047e20c6c3321a10e34060d774876c2c205e2ca7feacfb).
  The final theorems instantiate them with actual exact values: P is the
  root-pure unary domain, K is its set of kinds, and the group consists
  of pure exact operators with pure two-sided inverses. No cardinal
  coding or selector existence is assumed in those final theorems.
\<close>

lemma gi_T9_infinite_product_bound:
  assumes infinite_bound: "\<not> finite D"
    and left_bound: "|A| \<le>o |D|" and right_bound: "|B| \<le>o |D|"
  shows "|A \<times> B| \<le>o |D|"
  using assms by (simp add: card_of_Sigma_ordLeq_infinite)

theorem gi_T9_product_power_dichotomy:
  assumes counting: "|Pow K| \<le>o |K \<times> H|"
  shows "finite K \<or> |Pow K| \<le>o |H|"
proof (cases "finite K")
  case True
  then show ?thesis by blast
next
  case False
  have not_H_le_K: "\<not> |H| \<le>o |K|"
  proof
    assume H_le_K: "|H| \<le>o |K|"
    have product_le_K: "|K \<times> H| \<le>o |K|"
      by (rule gi_T9_infinite_product_bound[OF False ordLeq_refl[OF card_of_Card_order] H_le_K])
    have pow_le_K: "|Pow K| \<le>o |K|" by (rule ordLeq_transitive[OF counting product_le_K])
    have cantor: "|K| <o |Pow K|" by (rule card_of_Pow)
    show False using cantor pow_le_K not_ordLess_ordLeq by blast
  qed
  have K_le_H: "|K| \<le>o |H|"
  proof -
    have wK: "Well_order |K|" by (rule card_of_Well_order)
    have wH: "Well_order |H|" by (rule card_of_Well_order)
    have less: "|K| <o |H|" using not_H_le_K not_ordLeq_iff_ordLess[OF wK wH] by blast
    show ?thesis by (rule ordLess_imp_ordLeq[OF less])
  qed
  have infinite_H: "\<not> finite H"
  proof
    assume finite_H: "finite H"
    have "finite K" by (rule card_of_ordLeq_finite[OF K_le_H finite_H])
    then show False using False by simp
  qed
  have product_le_H: "|K \<times> H| \<le>o |H|"
    by (rule gi_T9_infinite_product_bound[OF infinite_H K_le_H ordLeq_refl[OF card_of_Card_order]])
  have pow_le_H: "|Pow K| \<le>o |H|" by (rule ordLeq_transitive[OF counting product_le_H])
  show ?thesis using pow_le_H by blast
qed

section \<open>A concrete injection from pure values into kinds times the group\<close>

definition gi_T9_cardinal_code where
  "gi_T9_cardinal_code C X = (gi_T9_kind C X, gi_T9_kind_code C (gi_T9_kind C X) X)"

context gi_T9_native_purity
begin

lemma gi_T9_pure_kind_member:
  assumes xp: "X \<in> gi_T9_root_pure C gb_unary"
  shows "gi_T9_kind C X \<in> gi_T9_kinds C"
  by (rule subsetD[OF gi_T9_kind_closed], rule imageI[OF xp])

theorem gi_T9_cardinal_code_injective:
  "inj_on (gi_T9_cardinal_code C) (gi_T9_root_pure C gb_unary)"
proof (rule inj_onI)
  fix X Y
  assume xp: "X \<in> gi_T9_root_pure C gb_unary" and yp: "Y \<in> gi_T9_root_pure C gb_unary"
    and same: "gi_T9_cardinal_code C X = gi_T9_cardinal_code C Y"
  have equal_kind: "gi_T9_kind C X = gi_T9_kind C Y"
    using same by (simp add: gi_T9_cardinal_code_def)
  have pair_code: "gi_T9_kind_code C (gi_T9_kind C X) X = gi_T9_kind_code C (gi_T9_kind C Y) Y"
    using arg_cong[OF same, where f=snd]
    by (simp only: gi_T9_cardinal_code_def snd_conv)
  have code_equal: "gi_T9_kind_code C (gi_T9_kind C X) X = gi_T9_kind_code C (gi_T9_kind C X) Y"
    using pair_code by (simp only: equal_kind)
  have kind_member: "gi_T9_kind C X \<in> gi_T9_kinds C" by (rule gi_T9_pure_kind_member[OF xp])
  have xi: "X \<in> {Z\<in>gi_T9_root_pure C gb_unary. gi_T9_kind C Z = gi_T9_kind C X}"
    using xp by simp
  have yi: "Y \<in> {Z\<in>gi_T9_root_pure C gb_unary. gi_T9_kind C Z = gi_T9_kind C X}"
    using yp equal_kind by auto
  show "X = Y" by (rule inj_onD[OF gi_T9_kind_fibre_code(1)[OF kind_member] code_equal xi yi])
qed

theorem gi_T9_cardinal_code_range:
  "gi_T9_cardinal_code C ` gi_T9_root_pure C gb_unary \<subseteq> gi_T9_kinds C \<times> gi_T9_root_group C"
proof
  fix z
  assume member: "z \<in> gi_T9_cardinal_code C ` gi_T9_root_pure C gb_unary"
  obtain X where xp: "X \<in> gi_T9_root_pure C gb_unary" and shape: "z = gi_T9_cardinal_code C X"
    using member by blast
  have kind_member: "gi_T9_kind C X \<in> gi_T9_kinds C" by (rule gi_T9_pure_kind_member[OF xp])
  have code_member: "gi_T9_kind_code C (gi_T9_kind C X) X \<in> gi_T9_root_group C"
    using gi_T9_kind_code_spec[OF kind_member xp refl] by blast
  show "z \<in> gi_T9_kinds C \<times> gi_T9_root_group C"
    by (simp only: shape gi_T9_cardinal_code_def; rule SigmaI[OF kind_member code_member])
qed

theorem gi_T9_pure_le_kinds_times_group:
  "|gi_T9_root_pure C gb_unary| \<le>o |gi_T9_kinds C \<times> gi_T9_root_group C|"
  using gi_T9_cardinal_code_injective gi_T9_cardinal_code_range card_of_ordLeq by blast

section \<open>The full external powerset gives the other counting inequality\<close>

lemma gi_T9_kind_selector_range:
  assumes pc: "gi_T9_full_unary_PC C"
  shows "gi_T9_kind_selector C ` Pow (gi_T9_kinds C) \<subseteq> gi_T9_root_pure C gb_unary"
proof
  fix x
  assume member: "x \<in> gi_T9_kind_selector C ` Pow (gi_T9_kinds C)"
  obtain S where subset: "S \<subseteq> gi_T9_kinds C" and shape: "x = gi_T9_kind_selector C S"
    using member by blast
  show "x \<in> gi_T9_root_pure C gb_unary" unfolding shape by (rule gi_T9_kind_selector_pure[OF pc subset])
qed

theorem gi_T9_powerset_kinds_le_pure:
  assumes pc: "gi_T9_full_unary_PC C" and l2: "gi_T9_root_L2 C"
    and rm: "Elem r (pp_e_domain Prop)" and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []"
  shows "|Pow (gi_T9_kinds C)| \<le>o |gi_T9_root_pure C gb_unary|"
  using gi_T9_kind_selector_injective[OF pc l2 rm jr] gi_T9_kind_selector_range[OF pc]
    card_of_ordLeq by blast

theorem gi_T9_native_counting_bound:
  assumes pc: "gi_T9_full_unary_PC C" and l2: "gi_T9_root_L2 C"
    and rm: "Elem r (pp_e_domain Prop)" and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []"
  shows "|Pow (gi_T9_kinds C)| \<le>o |gi_T9_kinds C \<times> gi_T9_root_group C|"
  by (rule ordLeq_transitive[OF gi_T9_powerset_kinds_le_pure[OF pc l2 rm jr]
      gi_T9_pure_le_kinds_times_group])

theorem gi_T9_native_cardinal_dichotomy:
  assumes pc: "gi_T9_full_unary_PC C" and l2: "gi_T9_root_L2 C"
    and rm: "Elem r (pp_e_domain Prop)" and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []"
  shows "finite (gi_T9_kinds C) \<or> |Pow (gi_T9_kinds C)| \<le>o |gi_T9_root_group C|"
  by (rule gi_T9_product_power_dichotomy[OF gi_T9_native_counting_bound[OF pc l2 rm jr]])

corollary gi_T9_infinite_kinds_group_bound:
  assumes pc: "gi_T9_full_unary_PC C" and l2: "gi_T9_root_L2 C"
    and rm: "Elem r (pp_e_domain Prop)" and jr: "pp_e_holds (gi_T9_J_value C \<acute> r) []"
    and infinite_kinds: "infinite (gi_T9_kinds C)"
  shows "|Pow (gi_T9_kinds C)| \<le>o |gi_T9_root_group C|"
  using gi_T9_native_cardinal_dichotomy[OF pc l2 rm jr] infinite_kinds by blast

end

text \<open>
  The concrete counting chain is |Pow K| ≤ |P| ≤ |K×G| for the actual
  root-pure exact unary values and their actual reversible-composition
  kinds. The two injections have been constructed from the native purity
  assumptions and the full external PC/L2 selector theorem; no free-action
  assumption or abstract fibre-code premise remains.

  The native-purity locale retains the globally valid logical-purity,
  application-closure and PP core and a rich variable stock. Full external
  unary PC, semantic L2, and a typed fun′ witness remain explicit additional
  hypotheses. This is not a model-existence theorem, nor does it prove
  that PC holds in the countable generated-stock models. Infinitude of
  kinds has not been inferred merely from the counting inequality: the
  final corollary explicitly retains that separate premise.
\<close>

end
