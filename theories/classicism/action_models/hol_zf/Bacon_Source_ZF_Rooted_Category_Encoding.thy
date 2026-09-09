theory Bacon_Source_ZF_Rooted_Category_Encoding
  imports Bacon_Source_ZF_Encoded_Category
    Bacon_Classicism_Action_Development.Bacon_Source_Rooted_Category
begin

section \<open>Recoding preserves every root arrow\<close>

text \<open>
  A root R has at least one arrow to every object, not exactly one.
  Source: Bacon–Dorr p.55, before Definition 3.18, and the
  recoding step for Proposition 3.22, pp.57 and 72.
  Encoding an original R→W witness gives a coded witness.

  The correspondence below retains the ENTIRE collection of R→W
  arrows. It does not choose a distinguished root arrow, change the
  object set, or replace weak initiality by initiality. Only the
  supplied bounded injective arrow encoding and category are used.
\<close>

context paper_ZF_category_encoding
begin

theorem paper_ZF_root_arrows_image:
  "{z\<in>coded_arrows. coded_source z = R \<and> coded_target z = W} =
    image encode {h\<in>arrows. source h = R \<and> target h = W}"
proof
  show "{z\<in>coded_arrows. coded_source z = R \<and> coded_target z = W} \<subseteq>
    image encode {h\<in>arrows. source h = R \<and> target h = W}"
  proof
    fix z
    assume member: "z \<in> {z\<in>coded_arrows. coded_source z = R \<and> coded_target z = W}"
    have za: "z \<in> coded_arrows" and zs: "coded_source z = R" and zt: "coded_target z = W"
      using member by blast+
    have original: "decode_arrow z \<in> arrows" by (rule paper_ZF_decode_arrow_type[OF za])
    have origin: "source (decode_arrow z) = R" using zs by (simp only: paper_ZF_recode_source_def)
    have finish: "target (decode_arrow z) = W" using zt by (simp only: paper_ZF_recode_target_def)
    have root_arrow: "decode_arrow z \<in> {h\<in>arrows. source h = R \<and> target h = W}"
      using original origin finish by blast
    have encoded: "encode (decode_arrow z) \<in> image encode {h\<in>arrows. source h = R \<and> target h = W}"
      by (rule imageI[OF root_arrow])
    show "z \<in> image encode {h\<in>arrows. source h = R \<and> target h = W}"
      using encoded by (simp only: paper_ZF_encode_decode_arrow[OF za])
  qed
next
  show "image encode {h\<in>arrows. source h = R \<and> target h = W} \<subseteq>
    {z\<in>coded_arrows. coded_source z = R \<and> coded_target z = W}"
  proof
    fix z
    assume member: "z \<in> image encode {h\<in>arrows. source h = R \<and> target h = W}"
    obtain h where ha: "h \<in> arrows" and hs: "source h = R" and ht: "target h = W"
      and shape: "z = encode h" using member by blast
    show "z \<in> {z\<in>coded_arrows. coded_source z = R \<and> coded_target z = W}"
      by (simp only: shape mem_Collect_eq paper_ZF_coded_source_on[OF ha] paper_ZF_coded_target_on[OF ha]
        hs ht; simp only: paper_ZF_encode_arrow_type[OF ha]; simp)
  qed
qed

theorem paper_ZF_root_arrows_bijection:
  "bij_betw encode {h\<in>arrows. source h = R \<and> target h = W}
    {z\<in>coded_arrows. coded_source z = R \<and> coded_target z = W}"
proof (unfold bij_betw_def, rule conjI)
  show "inj_on encode {h\<in>arrows. source h = R \<and> target h = W}"
    by (rule inj_on_subset[OF encode_injective]; blast)
next
  show "image encode {h\<in>arrows. source h = R \<and> target h = W} =
    {z\<in>coded_arrows. coded_source z = R \<and> coded_target z = W}"
    by (rule paper_ZF_root_arrows_image[symmetric])
qed

theorem paper_ZF_encoded_rooted_category:
  assumes rooted: "paper_rooted_category objects arrows source target compose identity R"
  shows "paper_rooted_category objects coded_arrows coded_source coded_target coded_compose coded_identity R"
proof -
  interpret Original: paper_rooted_category objects arrows source target compose identity R by (rule rooted)
  show ?thesis
  proof (unfold paper_rooted_category_def, rule conjI[OF paper_ZF_encoded_category], unfold_locales)
    show "R \<in> objects" by (rule Original.root_object)
  next
    fix W
    assume object: "W \<in> objects"
    obtain h where ha: "h \<in> arrows" and hs: "source h = R" and ht: "target h = W"
      using Original.root_reaches[OF object] by blast
    have coded: "encode h \<in> coded_arrows" by (rule paper_ZF_encode_arrow_type[OF ha])
    have origin: "coded_source (encode h) = R" by (simp only: paper_ZF_coded_source_on[OF ha] hs)
    have finish: "coded_target (encode h) = W" by (simp only: paper_ZF_coded_target_on[OF ha] ht)
    show "\<exists>z\<in>coded_arrows. coded_source z = R \<and> coded_target z = W"
      by (rule bexI[where x="encode h"], rule conjI[OF origin finish], rule coded)
  qed
qed

end

end
