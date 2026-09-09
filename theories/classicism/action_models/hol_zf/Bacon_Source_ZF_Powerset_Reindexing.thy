theory Bacon_Source_ZF_Powerset_Reindexing
  imports Bacon_Source_ZF_Encoded_Category Bacon_Source_ZF_Powerset_Action
begin

section \<open>Arrow recoding commutes with the outgoing powerset action\<close>

text \<open>
  Encoding arrows sends a subset S of the original arrows to e[S].
  Precomposition satisfies e[fᴾ(S)]=e(f)ᴾ(e[S]). Source role:
  Example 3.15, p.54. The injection is required only on the supplied
  arrows; every original composite used below belongs to that set.
\<close>

context paper_ZF_category_encoding
begin

lemma paper_ZF_encoded_outgoing_subset:
  assumes subset: "S \<subseteq> paper_outgoing arrows source W"
  shows "image encode S \<subseteq> paper_outgoing coded_arrows coded_source W"
proof
  fix z
  assume member: "z \<in> image encode S"
  obtain h where hs: "h \<in> S" and shape: "z = encode h" using member by blast
  have ha: "h \<in> arrows" and origin: "source h = W"
    using subset hs by (auto simp: paper_outgoing_member)
  show "z \<in> paper_outgoing coded_arrows coded_source W"
    by (simp only: shape paper_outgoing_member paper_ZF_encode_arrow_type[OF ha] paper_ZF_coded_source_on[OF ha] origin; simp)
qed

theorem paper_ZF_powerset_reindex:
  assumes arrow: "f \<in> arrows" and subset: "S \<subseteq> arrows"
  shows "image encode (paper_powerset_transport arrows source target compose f S) =
    paper_powerset_transport coded_arrows coded_source coded_target coded_compose (encode f) (image encode S)"
proof
  show "image encode (paper_powerset_transport arrows source target compose f S) \<subseteq>
      paper_powerset_transport coded_arrows coded_source coded_target coded_compose (encode f) (image encode S)"
  proof
    fix z
    assume member: "z \<in> image encode (paper_powerset_transport arrows source target compose f S)"
    obtain h where hm: "h \<in> paper_powerset_transport arrows source target compose f S"
      and shape: "z = encode h" using member by blast
    have ha: "h \<in> arrows" and origin: "source h = target f" and composite: "compose h f \<in> S"
      using hm by (auto simp only: paper_powerset_transport_member)
    have image_member: "encode (compose h f) \<in> image encode S" by (rule imageI[OF composite])
    show "z \<in> paper_powerset_transport coded_arrows coded_source coded_target coded_compose (encode f) (image encode S)"
      using image_member by (simp only: shape paper_powerset_transport_member paper_ZF_encode_arrow_type[OF ha]
        paper_ZF_coded_source_on[OF ha] paper_ZF_coded_target_on[OF arrow] origin paper_ZF_encode_compose_on[OF arrow ha]; simp)
  qed
next
  show "paper_powerset_transport coded_arrows coded_source coded_target coded_compose (encode f) (image encode S) \<subseteq>
      image encode (paper_powerset_transport arrows source target compose f S)"
  proof
    fix z
    assume member: "z \<in> paper_powerset_transport coded_arrows coded_source coded_target coded_compose (encode f) (image encode S)"
    have za: "z \<in> coded_arrows" and origin: "coded_source z = coded_target (encode f)"
      and composite: "coded_compose z (encode f) \<in> image encode S"
      using member by (auto simp only: paper_powerset_transport_member)
    let ?h = "decode_arrow z"
    have ha: "?h \<in> arrows" by (rule paper_ZF_decode_arrow_type[OF za])
    have shape: "z = encode ?h" by (rule paper_ZF_encode_decode_arrow[OF za, symmetric])
    have hs: "source ?h = target f"
      using origin by (simp only: paper_ZF_recode_source_def paper_ZF_coded_target_on[OF arrow])
    have meeting: "target f = source ?h" by (rule hs[symmetric])
    have ca: "compose ?h f \<in> arrows" by (rule compose_arrow[OF arrow ha meeting])
    have coded_composite: "coded_compose z (encode f) = encode (compose ?h f)"
    proof -
      have "coded_compose z (encode f) = coded_compose (encode ?h) (encode f)"
        by (rule arg_cong[OF shape])
      also have "... = encode (compose ?h f)"
        by (rule paper_ZF_encode_compose_on[OF arrow ha])
      finally show ?thesis .
    qed
    have coded_member: "encode (compose ?h f) \<in> image encode S"
      using composite by (simp only: coded_composite)
    obtain k where km: "k \<in> S" and codes: "encode (compose ?h f) = encode k" using coded_member by blast
    have ka: "k \<in> arrows" by (rule subsetD[OF subset km])
    have equal: "compose ?h f = k" by (rule inj_onD[OF encode_injective codes ca ka])
    have cs: "compose ?h f \<in> S" by (simp only: equal; rule km)
    have hm: "?h \<in> paper_powerset_transport arrows source target compose f S"
      by (simp only: paper_powerset_transport_member; rule conjI[OF ha conjI[OF hs cs]])
    show "z \<in> image encode (paper_powerset_transport arrows source target compose f S)"
    proof -
      have "encode ?h \<in> image encode (paper_powerset_transport arrows source target compose f S)"
        by (rule imageI[OF hm])
      then show ?thesis by (subst shape, assumption)
    qed
  qed
qed

end

end
