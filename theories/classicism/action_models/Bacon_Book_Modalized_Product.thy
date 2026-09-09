theory Bacon_Book_Modalized_Product
  imports Bacon_Book_Modalized_Set
begin

section \<open>The componentwise product of modalized sets\<close>

theorem book_modalized_product:
  assumes first: "book_modalized_set W le A iA" and second: "book_modalized_set W le B iB"
  shows "book_modalized_set W le (\<lambda>w. A w \<times> B w)
    (\<lambda>w v p. (iA w v (fst p), iB w v (snd p)))"
proof -
  interpret X: book_modalized_set W le A iA by (rule first)
  interpret Y: book_modalized_set W le B iB by (rule second)
  show ?thesis
  proof unfold_locales
    fix w v p
    assume ww: "w \<in> W" and vw: "v \<in> W" and related: "le w v" and member: "p \<in> A w \<times> B w"
    have pa: "fst p \<in> A w" and pb: "snd p \<in> B w" using member by auto
    show "(iA w v (fst p), iB w v (snd p)) \<in> A v \<times> B v"
      by (rule SigmaI[OF X.counterpart_type[OF ww vw related pa] Y.counterpart_type[OF ww vw related pb]])
  next
    fix w p
    assume ww: "w \<in> W" and member: "p \<in> A w \<times> B w"
    have pa: "fst p \<in> A w" and pb: "snd p \<in> B w" using member by auto
    show "(iA w w (fst p), iB w w (snd p)) = p"
      by (simp only: X.counterpart_identity[OF ww pa] Y.counterpart_identity[OF ww pb]; cases p; simp)
  next
    fix w v u p
    assume ww: "w \<in> W" and vw: "v \<in> W" and uw: "u \<in> W" and wv: "le w v" and vu: "le v u"
      and member: "p \<in> A w \<times> B w"
    have pa: "fst p \<in> A w" and pb: "snd p \<in> B w" using member by auto
    show "(iA w u (fst p), iB w u (snd p)) =
      (iA v u (fst (iA w v (fst p), iB w v (snd p))),
       iB v u (snd (iA w v (fst p), iB w v (snd p))))"
      by (simp only: fst_conv snd_conv X.counterpart_compose[OF ww vw uw wv vu pa]
        Y.counterpart_compose[OF ww vw uw wv vu pb])
  qed
qed

text \<open>
  Example 17.2, p.360: (A×B)_w=A_w×B_w, with the two
  counterpart maps acting componentwise. The construction requires
  actual modalized-set endpoints, not nonempty or disjoint fibers.
\<close>

end
