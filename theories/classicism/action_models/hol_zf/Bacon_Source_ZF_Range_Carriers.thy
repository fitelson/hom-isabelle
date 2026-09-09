theory Bacon_Source_ZF_Range_Carriers
  imports Bacon_Source_ZF_Subset_Carriers
    Bacon_Classicism_Action_Development.Bacon_Source_Image_Action_Inverse
begin

section \<open>Code the encoded range, not the whole ambient fiber\<close>

text \<open>
  Given an explicit bound B(W), define C(W)={fW(d) | d∈D(W)}
  by separation inside B(W). Source role: profile images and their
  subactions in Definition 3.17 and Proposition 3.22, pp.55 and 57.
  The equality to the entire image requires the displayed boundedness
  hypothesis; otherwise separation could truncate that image.

  D(W) may have an arbitrary HOL carrier. Only its encoded image is
  bounded by an actual ZF set. These are standard HOL-ZF constructions,
  not arbitrary-set representability, a full ambient-fiber identification,
  or an assumed action-model decoder.
\<close>

definition paper_ZF_range_code ::
  "('o \<Rightarrow> ZF) \<Rightarrow> ('o \<Rightarrow> 'x \<Rightarrow> ZF) \<Rightarrow> ('o \<Rightarrow> 'x set) \<Rightarrow> 'o \<Rightarrow> ZF" where
  "paper_ZF_range_code B f D W = Sep (B W) (\<lambda>z. \<exists>d\<in>D W. f W d = z)"

definition paper_ZF_range_decode ::
  "('o \<Rightarrow> 'x \<Rightarrow> ZF) \<Rightarrow> ('o \<Rightarrow> 'x set) \<Rightarrow> 'o \<Rightarrow> ZF \<Rightarrow> 'x" where
  "paper_ZF_range_decode f D W = paper_action_image_inverse f D W"

lemma paper_ZF_range_code_subset:
  "explode (paper_ZF_range_code B f D W) \<subseteq> explode (B W)"
  by (auto simp only: paper_ZF_range_code_def explode_Elem Sep)

theorem paper_ZF_range_code_explode:
  assumes bounded: "\<And>d. d \<in> D W \<Longrightarrow> f W d \<in> explode (B W)"
  shows "explode (paper_ZF_range_code B f D W) = image (f W) (D W)"
  using bounded by (auto simp: paper_ZF_range_code_def explode_Elem Sep)

lemma paper_ZF_range_encode_type:
  assumes bounded: "\<And>d. d \<in> D W \<Longrightarrow> f W d \<in> explode (B W)"
    and member: "d \<in> D W"
  shows "f W d \<in> explode (paper_ZF_range_code B f D W)"
  by (simp only: paper_ZF_range_code_explode[where B=B and f=f and D=D and W=W, OF bounded]; rule imageI[OF member])

lemma paper_ZF_range_as_action_image:
  assumes bounded: "\<And>d. d \<in> D W \<Longrightarrow> f W d \<in> explode (B W)"
  shows "explode (paper_ZF_range_code B f D W) = paper_action_image f D W"
  by (simp only: paper_ZF_range_code_explode[where B=B and f=f and D=D and W=W, OF bounded] paper_action_image_def)

theorem paper_ZF_range_fiber_bijection:
  assumes bounded: "\<And>d. d \<in> D W \<Longrightarrow> f W d \<in> explode (B W)"
    and injective: "inj_on (f W) (D W)"
  shows "bij_betw (f W) (D W) (explode (paper_ZF_range_code B f D W))"
  unfolding bij_betw_def by (rule conjI[OF injective]; simp only: paper_ZF_range_code_explode[where B=B and f=f and D=D and W=W, OF bounded])

lemma paper_ZF_range_decode_type:
  assumes bounded: "\<And>d. d \<in> D W \<Longrightarrow> f W d \<in> explode (B W)"
    and member: "z \<in> explode (paper_ZF_range_code B f D W)"
  shows "paper_ZF_range_decode f D W z \<in> D W"
proof -
  have image_member: "z \<in> paper_action_image f D W"
    using member by (simp only: paper_ZF_range_as_action_image[where B=B and f=f and D=D and W=W, OF bounded])
  show ?thesis unfolding paper_ZF_range_decode_def by (rule paper_action_image_inverse_type[OF image_member])
qed

lemma paper_ZF_range_decode_encode:
  assumes injective: "inj_on (f W) (D W)" and member: "d \<in> D W"
  shows "paper_ZF_range_decode f D W (f W d) = d"
  unfolding paper_ZF_range_decode_def by (rule paper_action_image_inverse_left[where e=f and X=D and A=W, OF injective member])

lemma paper_ZF_range_encode_decode:
  assumes bounded: "\<And>d. d \<in> D W \<Longrightarrow> f W d \<in> explode (B W)"
    and member: "z \<in> explode (paper_ZF_range_code B f D W)"
  shows "f W (paper_ZF_range_decode f D W z) = z"
proof -
  have image_member: "z \<in> paper_action_image f D W"
    using member by (simp only: paper_ZF_range_as_action_image[where B=B and f=f and D=D and W=W, OF bounded])
  show ?thesis unfolding paper_ZF_range_decode_def by (rule paper_action_image_inverse_right[OF image_member])
qed

text \<open>
  The inverse is specified only on the encoded range. Its right inverse
  and typing need image membership; its left inverse additionally needs
  fiberwise injectivity. No injectivity of category transports is imposed.
\<close>

end
