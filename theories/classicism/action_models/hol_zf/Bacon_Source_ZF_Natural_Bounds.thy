theory Bacon_Source_ZF_Natural_Bounds
  imports Bacon_Source_ZF_Function_Graphs "HOL-Cardinals.Cardinal_Order_Relation"
begin

section \<open>An actual infinite set-theoretic carrier\<close>

lemma paper_ZF_nat_values:
  "explode HOLZF.Nat = nat2Nat ` (UNIV :: nat set)"
proof
  show "explode HOLZF.Nat \<subseteq> nat2Nat ` (UNIV :: nat set)"
    by (auto simp: explode_def HOLZF.Nat_def Sep)
next
  show "nat2Nat ` (UNIV :: nat set) \<subseteq> explode HOLZF.Nat"
    by (auto simp: explode_Elem intro: Elem_nat2Nat_Nat)
qed

theorem paper_ZF_nat_values_infinite:
  "infinite (explode HOLZF.Nat)"
proof
  assume finite: "finite (explode HOLZF.Nat)"
  have image_finite: "finite (nat2Nat ` (UNIV :: nat set))"
    using finite by (simp only: paper_ZF_nat_values)
  have injective: "inj_on nat2Nat (UNIV :: nat set)" by (rule inj_nat2Nat)
  have "finite (UNIV :: nat set)" by (rule finite_imageD[OF image_finite injective])
  then show False by simp
qed

section \<open>A cardinal bound supplies the actual bounded coding map\<close>

theorem paper_ZF_cardinal_bounded_encoding:
  assumes bound: "card_of A \<le>o card_of (explode B)"
  obtains encode where "inj_on encode A" "encode ` A \<subseteq> explode B"
proof -
  have witness: "\<exists>encode. inj_on encode A \<and> encode ` A \<subseteq> explode B"
    by (rule iffD2[OF card_of_ordLeq bound])
  then obtain encode where injective: "inj_on encode A" and bounded: "encode ` A \<subseteq> explode B"
    by blast
  show thesis by (rule that[OF injective bounded])
qed

text \<open>
  The natural-number values are exactly the elements of the actual
  HOL-ZF set Nat, not all values of the HOL type ZF. Their infinitude
  follows from the proved injection nat2Nat. A separate cardinal
  comparison supplies a coding function on its specified domain A;
  its behavior outside A is irrelevant.

  Source role: the individual and arrow bounds in Proposition 3.22
  and the fixed-infinite-set discussion on p.52. This is relative to
  the standard HOL-ZF foundation. No model or cardinal bound for an
  arbitrary object/arrow collection is assumed to have been proved.
\<close>

end
