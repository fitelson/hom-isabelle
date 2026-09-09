theory Bacon_Book_ZF_Proposition_Restriction
  imports Bacon_Book_ZF_Arrow_Restriction
begin

section \<open>Proposition counterparts are truncations of truth sets\<close>

context book_full_C_canonical_frame
begin

definition full_ZF_proposition_restrict where
  "full_ZF_proposition_restrict v p = Sep p (\<lambda>z. le v (full_world_decode z))"

lemma full_ZF_world_subset_restriction:
  assumes subset: "P \<subseteq> worlds"
  shows "paper_ZF_image_code full_world_set book_ZF_world_code (P \<inter> {u\<in>worlds. le v u}) =
    full_ZF_proposition_restrict v (paper_ZF_image_code full_world_set book_ZF_world_code P)"
proof -
  have smaller: "P \<inter> {u\<in>worlds. le v u} \<subseteq> worlds" by blast
  have elements: "explode (full_ZF_proposition_restrict v (paper_ZF_image_code full_world_set book_ZF_world_code P)) =
    {z \<in> book_ZF_world_code ` P. le v (full_world_decode z)}"
    unfolding full_ZF_proposition_restrict_def
    using full_world_subset_code_elements[OF subset]
    by (auto simp: explode_Elem Sep)
  have image: "{z \<in> book_ZF_world_code ` P. le v (full_world_decode z)} =
    book_ZF_world_code ` (P \<inter> {u\<in>worlds. le v u})"
    using subset full_world_decode_code by auto
  show ?thesis by (rule injD[OF inj_explode]; simp only: full_world_subset_code_elements[OF smaller] elements image)
qed

lemma full_ZF_source_proposition_subset:
  "book_full_C_proposition_h \<Sigma> B G actual w X \<subseteq> worlds"
  unfolding book_full_C_proposition_h_def book_full_C_proposition_profile_def by blast

theorem full_ZF_h_proposition_restriction:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and wv: "le w v"
    and member: "X \<in> book_C_identity_domain (fst w) G (snd w) Prop"
  shows "full_ZF_h Prop v (book_C_term_counterpart G w v Prop X) =
    full_ZF_proposition_restrict v (full_ZF_h Prop w X)"
  by (simp only: full_ZF_h.simps proposition_h_naturality[OF ww vw wv member]
    full_ZF_world_subset_restriction[OF full_ZF_source_proposition_subset])

theorem full_ZF_i_proposition_restriction:
  assumes ww: "w \<in> worlds" and vw: "v \<in> worlds" and wv: "le w v"
    and member: "p \<in> explode (full_ZF_D Prop w)"
  shows "full_ZF_i Prop w v p = full_ZF_proposition_restrict v p"
proof -
  have inverse: "full_ZF_j Prop w p \<in> book_C_identity_domain (fst w) G (snd w) Prop"
    by (rule full_ZF_j_type[OF member])
  show ?thesis unfolding full_ZF_i_def
    by (simp only: full_ZF_h_proposition_restriction[OF ww vw wv inverse] full_ZF_hj[OF member])
qed

theorem full_ZF_proposition_future:
  assumes member: "p \<in> explode (full_ZF_D Prop w)"
  shows "explode p \<subseteq> explode (full_ZF_future w)"
proof -
  obtain X where shape: "p = full_ZF_h Prop w X"
    using member unfolding full_ZF_D_elements by blast
  have profile: "book_full_C_proposition_h \<Sigma> B G actual w X \<subseteq> {v\<in>worlds. le w v}"
    unfolding book_full_C_proposition_h_def book_full_C_proposition_profile_def by blast
  show ?thesis
  proof (rule subsetI)
    fix z
    assume zm: "z \<in> explode p"
    obtain v where vm: "v \<in> book_full_C_proposition_h \<Sigma> B G actual w X" and zs: "z = book_ZF_world_code v"
      using zm by (simp only: shape full_ZF_h.simps full_world_subset_code_elements[OF full_ZF_source_proposition_subset]; blast)
    have vw: "v \<in> worlds" and access: "le w v" using profile vm by blast+
    show "z \<in> explode (full_ZF_future w)"
      by (simp only: zs explode_Elem full_ZF_future_world_member[OF vw]; rule access)
  qed
qed

theorem full_ZF_individual_domain:
  "full_ZF_D Ind w = book_ZF_term_class_domain G w Ind"
  by (rule injD[OF inj_explode]; simp only: full_ZF_D_elements full_ZF_h.simps book_ZF_term_class_domain_elements)

end

text \<open>
  The t-counterpart is literal separation by the later future, and
  every t-value is a subset of its world's future. At e the domain is
  exactly the encoded term-class domain. Thus Dᵉ=Tᵉ holds in the coded
  realization; it is not a claim that an arbitrary HOL carrier embeds
  identically into ZF. These identifications concern Bacon's actual
  recursively constructed family, with no additional model premise.
\<close>

end
