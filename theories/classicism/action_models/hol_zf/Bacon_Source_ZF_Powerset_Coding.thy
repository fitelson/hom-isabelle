theory Bacon_Source_ZF_Powerset_Coding
  imports Bacon_Source_ZF_Outgoing_Pairs Bacon_Source_ZF_Subset_Carriers
    Bacon_Classicism_Action_Development.Bacon_Source_Powerset_Action
begin

section \<open>The powerset fiber has an actual internal set code\<close>

text \<open>
  Wᴾ=𝒫(out(W)) is coded by Power(OutCode(W)).
  Source: Bacon–Dorr Example 3.15, p.54, and Definition 3.18,
  p.55. The arrow carrier is the explicitly supplied ZF set A;
  objects may have a different HOL type.

  Separation encodes each subset of the outgoing arrows, and explode
  is the inverse. This is an actual bijection, relative to standard
  HOL-ZF, not an assumed representability or decoding principle.
  No category laws, individual fibers, or all-type family are needed
  for these bounded fiber constructions.
\<close>

definition paper_ZF_powerset_code :: "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> ZF" where
  "paper_ZF_powerset_code A source W = Power (paper_ZF_outgoing_code A source W)"

definition paper_ZF_encode_powerset :: "ZF \<Rightarrow> (ZF \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> ZF set \<Rightarrow> ZF" where
  "paper_ZF_encode_powerset A source W S = paper_ZF_encode_subset (paper_ZF_outgoing_code A source W) S"

lemma paper_ZF_outgoing_code_explode:
  "explode (paper_ZF_outgoing_code A source W) = paper_outgoing (explode A) source W"
  by (auto simp only: explode_Elem paper_ZF_outgoing_code_member paper_outgoing_member)

lemma paper_ZF_powerset_generic_fiber:
  "paper_powerset_fiber (explode A) source W = Pow (explode (paper_ZF_outgoing_code A source W))"
  by (simp only: paper_powerset_fiber_def paper_ZF_outgoing_code_explode)

lemma paper_ZF_encode_powerset_type:
  "paper_ZF_encode_powerset A source W S \<in> explode (paper_ZF_powerset_code A source W)"
  by (simp only: paper_ZF_encode_powerset_def paper_ZF_powerset_code_def;
    rule paper_ZF_encode_subset_type)

lemma paper_ZF_decode_powerset_type:
  assumes member: "p \<in> explode (paper_ZF_powerset_code A source W)"
  shows "explode p \<in> paper_powerset_fiber (explode A) source W"
proof -
  have bounded: "p \<in> explode (Power (paper_ZF_outgoing_code A source W))"
    using member by (simp only: paper_ZF_powerset_code_def)
  have subset: "explode p \<subseteq> explode (paper_ZF_outgoing_code A source W)"
    by (rule paper_ZF_decode_subset_type[OF bounded])
  show ?thesis by (simp only: paper_ZF_powerset_generic_fiber Pow_iff; rule subset)
qed

theorem paper_ZF_decode_encode_powerset:
  assumes member: "S \<in> paper_powerset_fiber (explode A) source W"
  shows "explode (paper_ZF_encode_powerset A source W S) = S"
proof -
  have subset: "S \<subseteq> explode (paper_ZF_outgoing_code A source W)"
    using member by (simp only: paper_ZF_powerset_generic_fiber Pow_iff)
  show ?thesis unfolding paper_ZF_encode_powerset_def by (rule paper_ZF_decode_encode_subset[OF subset])
qed

theorem paper_ZF_encode_decode_powerset:
  assumes member: "p \<in> explode (paper_ZF_powerset_code A source W)"
  shows "paper_ZF_encode_powerset A source W (explode p) = p"
  unfolding paper_ZF_encode_powerset_def
  by (rule paper_ZF_encode_decode_subset[OF member[unfolded paper_ZF_powerset_code_def]])

theorem paper_ZF_powerset_fiber_bijection:
  "bij_betw (paper_ZF_encode_powerset A source W)
    (paper_powerset_fiber (explode A) source W) (explode (paper_ZF_powerset_code A source W))"
proof -
  have encoding: "paper_ZF_encode_powerset A source W =
    paper_ZF_encode_subset (paper_ZF_outgoing_code A source W)"
    by (rule ext, simp only: paper_ZF_encode_powerset_def)
  show ?thesis by (simp only: encoding paper_ZF_powerset_generic_fiber paper_ZF_powerset_code_def;
    rule paper_ZF_subset_carrier_bijection)
qed

end
