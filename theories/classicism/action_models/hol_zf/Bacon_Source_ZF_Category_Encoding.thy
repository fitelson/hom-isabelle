theory Bacon_Source_ZF_Category_Encoding
  imports Bacon_Source_ZF_Embedded_Carriers
    Bacon_Classicism_Action_Development.Bacon_Source_Category
begin

section \<open>Recoding a supplied arrow carrier inside an explicit set\<close>

text \<open>
  Given e injective on the supplied arrows and e[arrows]⊆explode(B),
  use the exact image code as the new arrow set. Objects are unchanged.
  The source and target of e(h) are those of h; composition and identities
  are encoded from the original operations. Source role: the small-category
  representation required by Proposition 3.22, pp.57 and 72.

  The representation hypothesis is explicit. No arbitrary HOL-set
  smallness, assumed coded category, value recoding, or Goodman theory
  is used. All decoding equations below are guarded by actual arrow
  membership. The arbitrary off-carrier inverse is never used unguarded
  in a category law.
\<close>

definition paper_ZF_recode_source :: "'a set \<Rightarrow> ('a \<Rightarrow> ZF) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> ZF \<Rightarrow> 'o" where
  "paper_ZF_recode_source Arrows e s z = s (inv_into Arrows e z)"

definition paper_ZF_recode_target :: "'a set \<Rightarrow> ('a \<Rightarrow> ZF) \<Rightarrow> ('a \<Rightarrow> 'o) \<Rightarrow> ZF \<Rightarrow> 'o" where
  "paper_ZF_recode_target Arrows e t z = t (inv_into Arrows e z)"

definition paper_ZF_recode_compose :: "'a set \<Rightarrow> ('a \<Rightarrow> ZF) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_ZF_recode_compose Arrows e c z w = e (c (inv_into Arrows e z) (inv_into Arrows e w))"

definition paper_ZF_recode_identity :: "('a \<Rightarrow> ZF) \<Rightarrow> ('o \<Rightarrow> 'a) \<Rightarrow> 'o \<Rightarrow> ZF" where
  "paper_ZF_recode_identity e i W = e (i W)"

locale paper_ZF_category_encoding = paper_category objects arrows source target compose identity
  for objects :: "'o set" and arrows :: "'a set"
    and source :: "'a \<Rightarrow> 'o" and target :: "'a \<Rightarrow> 'o"
    and compose :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and identity :: "'o \<Rightarrow> 'a" +
  fixes encode :: "'a \<Rightarrow> ZF" and Bound :: ZF
  assumes encode_injective: "inj_on encode arrows"
    and encode_bounded: "image encode arrows \<subseteq> explode Bound"
begin

abbreviation coded_arrows where "coded_arrows \<equiv> explode (paper_ZF_image_code Bound encode arrows)"
abbreviation decode_arrow where "decode_arrow \<equiv> inv_into arrows encode"
abbreviation coded_source where "coded_source \<equiv> paper_ZF_recode_source arrows encode source"
abbreviation coded_target where "coded_target \<equiv> paper_ZF_recode_target arrows encode target"
abbreviation coded_compose where "coded_compose \<equiv> paper_ZF_recode_compose arrows encode compose"
abbreviation coded_identity where "coded_identity \<equiv> paper_ZF_recode_identity encode identity"

lemma paper_ZF_coded_arrows_image:
  "coded_arrows = image encode arrows"
  by (rule paper_ZF_image_code_elements[OF encode_bounded subset_refl])

lemma paper_ZF_encode_arrow_type:
  "f \<in> arrows \<Longrightarrow> encode f \<in> coded_arrows"
  by (simp only: paper_ZF_coded_arrows_image; rule imageI; assumption)

lemma paper_ZF_decode_arrow_type:
  "f \<in> coded_arrows \<Longrightarrow> decode_arrow f \<in> arrows"
  by (rule paper_ZF_image_inverse_type[OF encode_injective encode_bounded subset_refl]; assumption)

lemma paper_ZF_decode_encode_arrow:
  "f \<in> arrows \<Longrightarrow> decode_arrow (encode f) = f"
  by (rule inv_into_f_f[where A=arrows and f=encode, OF encode_injective]; assumption)

lemma paper_ZF_encode_decode_arrow:
  "f \<in> coded_arrows \<Longrightarrow> encode (decode_arrow f) = f"
  by (rule paper_ZF_image_inverse_right[OF encode_bounded subset_refl]; assumption)

lemma paper_ZF_coded_source_on:
  assumes arrow: "f \<in> arrows"
  shows "coded_source (encode f) = source f"
  by (simp only: paper_ZF_recode_source_def paper_ZF_decode_encode_arrow[OF arrow])

lemma paper_ZF_coded_target_on:
  assumes arrow: "f \<in> arrows"
  shows "coded_target (encode f) = target f"
  by (simp only: paper_ZF_recode_target_def paper_ZF_decode_encode_arrow[OF arrow])

lemma paper_ZF_coded_identity_type:
  assumes object: "W \<in> objects"
  shows "coded_identity W \<in> coded_arrows"
  unfolding paper_ZF_recode_identity_def by (rule paper_ZF_encode_arrow_type[OF identity_arrow[OF object]])

lemma paper_ZF_decode_coded_identity:
  assumes object: "W \<in> objects"
  shows "decode_arrow (coded_identity W) = identity W"
  unfolding paper_ZF_recode_identity_def by (rule paper_ZF_decode_encode_arrow[OF identity_arrow[OF object]])

lemma paper_ZF_decoded_meeting:
  assumes meeting: "coded_target f = coded_source g"
  shows "target (decode_arrow f) = source (decode_arrow g)"
  using meeting by (simp only: paper_ZF_recode_target_def paper_ZF_recode_source_def)

lemma paper_ZF_coded_compose_type:
  assumes fa: "f \<in> coded_arrows" and ga: "g \<in> coded_arrows" and meeting: "coded_target f = coded_source g"
  shows "coded_compose g f \<in> coded_arrows"
  unfolding paper_ZF_recode_compose_def
  by (rule paper_ZF_encode_arrow_type, rule compose_arrow[
    OF paper_ZF_decode_arrow_type[OF fa] paper_ZF_decode_arrow_type[OF ga] paper_ZF_decoded_meeting[OF meeting]])

lemma paper_ZF_decode_coded_compose:
  assumes fa: "f \<in> coded_arrows" and ga: "g \<in> coded_arrows" and meeting: "coded_target f = coded_source g"
  shows "decode_arrow (coded_compose g f) = compose (decode_arrow g) (decode_arrow f)"
  unfolding paper_ZF_recode_compose_def
  by (rule paper_ZF_decode_encode_arrow, rule compose_arrow[
    OF paper_ZF_decode_arrow_type[OF fa] paper_ZF_decode_arrow_type[OF ga] paper_ZF_decoded_meeting[OF meeting]])

lemma paper_ZF_encode_compose_on:
  assumes fa: "f \<in> arrows" and ga: "g \<in> arrows"
  shows "coded_compose (encode g) (encode f) = encode (compose g f)"
  by (simp only: paper_ZF_recode_compose_def paper_ZF_decode_encode_arrow[OF fa] paper_ZF_decode_encode_arrow[OF ga])

end

end
