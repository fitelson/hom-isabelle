theory Bacon_Source_ZF_Subset_Carriers
  imports Bacon_Source_ZF_Function_Graphs
begin

section \<open>Actual set codes for subsets of a specified domain\<close>

text \<open>
  Every HOL subset S⊆explode(A) is represented by separation inside A.
  Decoding gives precisely S, and the codes are precisely the members
  of Power(A). Source role: the outgoing-arrow powersets in Example
  3.15 and Definition 3.18, pp.54–55.

  As in the function-graph leaf, A is an explicit HOL-ZF set.
  No claim that arbitrary HOL sets are representable is made.
  This is an actual inverse pair, not an assumed decoder or a PER.
\<close>

definition paper_ZF_encode_subset :: "ZF \<Rightarrow> ZF set \<Rightarrow> ZF" where
  "paper_ZF_encode_subset A S = Sep A (\<lambda>x. x \<in> S)"

theorem paper_ZF_decode_encode_subset:
  assumes subset: "S \<subseteq> explode A"
  shows "explode (paper_ZF_encode_subset A S) = S"
  using subset by (auto simp: paper_ZF_encode_subset_def explode_Elem Sep)

lemma paper_ZF_encode_subset_type:
  "paper_ZF_encode_subset A S \<in> explode (Power A)"
  by (auto simp: paper_ZF_encode_subset_def explode_Elem Power subset_def Sep)

lemma paper_ZF_decode_subset_type:
  assumes member: "C \<in> explode (Power A)"
  shows "explode C \<subseteq> explode A"
  using member by (auto simp: explode_Elem Power subset_def)

theorem paper_ZF_encode_decode_subset:
  assumes member: "C \<in> explode (Power A)"
  shows "paper_ZF_encode_subset A (explode C) = C"
proof -
  have subset: "explode C \<subseteq> explode A" by (rule paper_ZF_decode_subset_type[OF member])
  have decoded: "explode (paper_ZF_encode_subset A (explode C)) = explode C"
    by (rule paper_ZF_decode_encode_subset[OF subset])
  show ?thesis by (rule injD[OF inj_explode decoded])
qed

theorem paper_ZF_subset_carrier_bijection:
  "bij_betw (paper_ZF_encode_subset A) (Pow (explode A)) (explode (Power A))"
proof (unfold bij_betw_def, rule conjI)
  show "inj_on (paper_ZF_encode_subset A) (Pow (explode A))"
  proof (rule inj_onI)
    fix S T
    assume sm: "S \<in> Pow (explode A)" and tm: "T \<in> Pow (explode A)"
      and equal: "paper_ZF_encode_subset A S = paper_ZF_encode_subset A T"
    have ss: "S \<subseteq> explode A" using sm by simp
    have ts: "T \<subseteq> explode A" using tm by simp
    have decoded: "explode (paper_ZF_encode_subset A S) =
      explode (paper_ZF_encode_subset A T)" by (simp only: equal)
    show "S = T" using decoded
      by (simp only: paper_ZF_decode_encode_subset[OF ss] paper_ZF_decode_encode_subset[OF ts])
  qed
next
  show "image (paper_ZF_encode_subset A) (Pow (explode A)) = explode (Power A)"
  proof
    show "image (paper_ZF_encode_subset A) (Pow (explode A)) \<subseteq> explode (Power A)"
      using paper_ZF_encode_subset_type by blast
    show "explode (Power A) \<subseteq> image (paper_ZF_encode_subset A) (Pow (explode A))"
    proof
      fix C
      assume member: "C \<in> explode (Power A)"
      have subset: "explode C \<in> Pow (explode A)"
        using paper_ZF_decode_subset_type[OF member] by simp
      have coded: "paper_ZF_encode_subset A (explode C) \<in>
        image (paper_ZF_encode_subset A) (Pow (explode A))" by (rule imageI[OF subset])
      show "C \<in> image (paper_ZF_encode_subset A) (Pow (explode A))"
        using coded by (simp only: paper_ZF_encode_decode_subset[OF member])
    qed
  qed
qed

end
