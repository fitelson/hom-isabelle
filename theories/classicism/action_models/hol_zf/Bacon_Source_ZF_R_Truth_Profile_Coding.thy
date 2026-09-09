theory Bacon_Source_ZF_R_Truth_Profile_Coding
  imports Bacon_Source_ZF_Powerset_Reindexing
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Subcategory
    Bacon_Classicism_Action_Development.Bacon_Source_BBK_Selected_Truth_Profile
begin

section \<open>Actual codes for R-model proposition profiles\<close>

text \<open>
  Encode p∈Mₜ by the set of coded selected arrows e(h) for which
  VN(hₜ(p)) holds. The code is separated inside the coded outgoing
  domain at M. Source: Definition 3.10, p.50, and the proposition
  step of Proposition 3.22, p.72.

  This is the first source-model-aware coding step: independent R
  model validity is legitimate input, while no H/C proof judgment is
  assumed. Arrow representability remains explicit. The eventual
  proposition stock is the image of this map, not the whole powerset.
\<close>

definition paper_ZF_R_truth_profile_code ::
  "ZF \<Rightarrow> (('c,'v) paper_R_bbk_arrow \<Rightarrow> ZF) \<Rightarrow> ('c,'v) paper_R_bbk_arrow set \<Rightarrow>
    ('c,'v) paper_bbk_model_data \<Rightarrow> 'v \<Rightarrow> ZF" where
  "paper_ZF_R_truth_profile_code B e Arrows M p =
    paper_ZF_encode_powerset (paper_ZF_image_code B e Arrows)
      (paper_ZF_recode_source Arrows e paper_arrow_source) M
      (image e (paper_bbk_truth_profile_on Arrows M p))"

locale paper_ZF_R_profile_encoding =
  fixes signature :: "'c ssignature" and stock :: sgcontext
    and objects :: "('c,'v) paper_bbk_model_data set" and arrows :: "('c,'v) paper_R_bbk_arrow set"
    and encode :: "('c,'v) paper_R_bbk_arrow \<Rightarrow> ZF" and Bound :: ZF
  assumes R_category: "paper_R_bbk_subcategory signature stock objects arrows"
    and encode_injective: "inj_on encode arrows"
    and encode_bounded: "image encode arrows \<subseteq> explode Bound"
begin

sublocale Encoding: paper_ZF_category_encoding objects arrows paper_arrow_source paper_arrow_target
  "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain" encode Bound
proof -
  interpret Original: paper_category objects arrows paper_arrow_source paper_arrow_target
    "paper_typed_compose paper_bbk_domain" "paper_typed_identity paper_bbk_domain"
    by (rule paper_R_bbk_subcategory_category[OF R_category])
  show "paper_ZF_category_encoding objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) encode Bound"
    by unfold_locales (rule encode_injective, rule encode_bounded)
qed

abbreviation proposition_code where
  "proposition_code \<equiv> paper_ZF_R_truth_profile_code Bound encode arrows"

lemma paper_ZF_R_truth_profile_code_elements:
  "explode (proposition_code M p) = image encode (paper_bbk_truth_profile_on arrows M p)"
proof -
  have subset: "image encode (paper_bbk_truth_profile_on arrows M p) \<subseteq>
      paper_outgoing Encoding.coded_arrows Encoding.coded_source M"
    by (rule Encoding.paper_ZF_encoded_outgoing_subset[OF paper_bbk_truth_profile_on_outgoing])
  have member: "image encode (paper_bbk_truth_profile_on arrows M p) \<in>
      paper_powerset_fiber Encoding.coded_arrows Encoding.coded_source M"
    using subset by (simp only: paper_powerset_fiber_def Pow_iff)
  show ?thesis unfolding paper_ZF_R_truth_profile_code_def
    by (rule paper_ZF_decode_encode_powerset[OF member])
qed

lemma paper_ZF_R_truth_profile_code_member:
  "Elem z (proposition_code M p) \<longleftrightarrow>
    (\<exists>h\<in>arrows. paper_arrow_source h = M \<and>
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop p) \<and> z = encode h)"
  by (simp only: explode_Elem[symmetric] paper_ZF_R_truth_profile_code_elements;
    auto simp only: paper_bbk_truth_profile_on_member)

lemma paper_ZF_R_truth_profile_code_type:
  "proposition_code M p \<in> explode (paper_ZF_powerset_code
    (paper_ZF_image_code Bound encode arrows) Encoding.coded_source M)"
  unfolding paper_ZF_R_truth_profile_code_def by (rule paper_ZF_encode_powerset_type)

lemma paper_ZF_R_truth_profile_code_on:
  assumes arrow: "h \<in> arrows"
  shows "Elem (encode h) (proposition_code M p) \<longleftrightarrow> h \<in> paper_bbk_truth_profile_on arrows M p"
proof
  assume member: "Elem (encode h) (proposition_code M p)"
  have coded: "encode h \<in> image encode (paper_bbk_truth_profile_on arrows M p)"
    using member by (simp only: explode_Elem[symmetric] paper_ZF_R_truth_profile_code_elements)
  obtain k where km: "k \<in> paper_bbk_truth_profile_on arrows M p" and equal: "encode h = encode k"
    using coded by blast
  have ka: "k \<in> arrows" using km by (simp only: paper_bbk_truth_profile_on_member; blast)
  have same: "h = k" by (rule inj_onD[OF encode_injective equal arrow ka])
  show "h \<in> paper_bbk_truth_profile_on arrows M p" by (simp only: same; rule km)
next
  assume member: "h \<in> paper_bbk_truth_profile_on arrows M p"
  show "Elem (encode h) (proposition_code M p)"
    by (simp only: explode_Elem[symmetric] paper_ZF_R_truth_profile_code_elements; rule imageI[OF member])
qed

theorem paper_ZF_R_truth_profile_code_injective:
  assumes quasi: "paper_bbk_quasi_fregean_on objects arrows" and object: "M \<in> objects"
  shows "inj_on (proposition_code M) (paper_bbk_domain M Prop)"
proof (rule inj_onI)
  fix p q
  assume pm: "p \<in> paper_bbk_domain M Prop" and qm: "q \<in> paper_bbk_domain M Prop"
    and equal: "proposition_code M p = proposition_code M q"
  have profiles: "paper_bbk_truth_profile_on arrows M p = paper_bbk_truth_profile_on arrows M q"
  proof (rule set_eqI)
    fix h
    show "(h \<in> paper_bbk_truth_profile_on arrows M p) = (h \<in> paper_bbk_truth_profile_on arrows M q)"
    proof (cases "h \<in> arrows")
      case True
      have codes: "Elem (encode h) (proposition_code M p) = Elem (encode h) (proposition_code M q)"
        by (simp only: equal)
      show ?thesis using codes by (simp only: paper_ZF_R_truth_profile_code_on[OF True])
    next
      case False
      then show ?thesis by (simp only: paper_bbk_truth_profile_on_member; blast)
    qed
  qed
  have injective: "inj_on (paper_bbk_truth_profile_on arrows M) (paper_bbk_domain M Prop)"
    using quasi object unfolding paper_bbk_quasi_fregean_on_def by blast
  show "p = q" by (rule inj_onD[OF injective profiles pm qm])
qed

end

end
