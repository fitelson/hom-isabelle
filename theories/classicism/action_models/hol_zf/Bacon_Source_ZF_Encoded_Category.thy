theory Bacon_Source_ZF_Encoded_Category
  imports Bacon_Source_ZF_Category_Encoding
begin

section \<open>The encoded arrows satisfy every category law\<close>

text \<open>
  The exact image of the original arrows, with decoded endpoints and
  encoded composition, is a category on the same objects. All inverse
  uses are on valid arrows, including intermediate composites and
  identities. Source role: the small-category carrier preparation for
  Proposition 3.22, pp.57 and 72. Representability is not inferred from
  arbitrary HOL sethood; it is the explicit bounded-injection premise.
\<close>

context paper_ZF_category_encoding
begin

theorem paper_ZF_encoded_category:
  "paper_category objects coded_arrows coded_source coded_target coded_compose coded_identity"
proof (rule paper_category.intro)
  fix f
  assume fa: "f \<in> coded_arrows"
  show "coded_source f \<in> objects" unfolding paper_ZF_recode_source_def
    by (rule source_object[OF paper_ZF_decode_arrow_type[OF fa]])
next
  fix f
  assume fa: "f \<in> coded_arrows"
  show "coded_target f \<in> objects" unfolding paper_ZF_recode_target_def
    by (rule target_object[OF paper_ZF_decode_arrow_type[OF fa]])
next
  fix W
  assume wo: "W \<in> objects"
  show "coded_identity W \<in> coded_arrows" by (rule paper_ZF_coded_identity_type[OF wo])
next
  fix W
  assume wo: "W \<in> objects"
  show "coded_source (coded_identity W) = W"
    by (simp only: paper_ZF_recode_identity_def paper_ZF_coded_source_on[OF identity_arrow[OF wo]] identity_source[OF wo])
next
  fix W
  assume wo: "W \<in> objects"
  show "coded_target (coded_identity W) = W"
    by (simp only: paper_ZF_recode_identity_def paper_ZF_coded_target_on[OF identity_arrow[OF wo]] identity_target[OF wo])
next
  fix f g
  assume fa: "f \<in> coded_arrows" and ga: "g \<in> coded_arrows" and meeting: "coded_target f = coded_source g"
  show "coded_compose g f \<in> coded_arrows" by (rule paper_ZF_coded_compose_type[OF fa ga meeting])
next
  fix f g
  assume fa: "f \<in> coded_arrows" and ga: "g \<in> coded_arrows" and meeting: "coded_target f = coded_source g"
  show "coded_source (coded_compose g f) = coded_source f"
    by (simp only: paper_ZF_recode_source_def paper_ZF_decode_coded_compose[OF fa ga meeting];
      rule compose_source[OF paper_ZF_decode_arrow_type[OF fa] paper_ZF_decode_arrow_type[OF ga]
        paper_ZF_decoded_meeting[OF meeting]])
next
  fix f g
  assume fa: "f \<in> coded_arrows" and ga: "g \<in> coded_arrows" and meeting: "coded_target f = coded_source g"
  show "coded_target (coded_compose g f) = coded_target g"
    by (simp only: paper_ZF_recode_target_def paper_ZF_decode_coded_compose[OF fa ga meeting];
      rule compose_target[OF paper_ZF_decode_arrow_type[OF fa] paper_ZF_decode_arrow_type[OF ga]
        paper_ZF_decoded_meeting[OF meeting]])
next
  fix f g h
  assume fa: "f \<in> coded_arrows" and ga: "g \<in> coded_arrows" and ha: "h \<in> coded_arrows"
    and fg: "coded_target f = coded_source g" and gh: "coded_target g = coded_source h"
  have fd: "decode_arrow f \<in> arrows" by (rule paper_ZF_decode_arrow_type[OF fa])
  have gd: "decode_arrow g \<in> arrows" by (rule paper_ZF_decode_arrow_type[OF ga])
  have hd: "decode_arrow h \<in> arrows" by (rule paper_ZF_decode_arrow_type[OF ha])
  have fgd: "target (decode_arrow f) = source (decode_arrow g)" by (rule paper_ZF_decoded_meeting[OF fg])
  have ghd: "target (decode_arrow g) = source (decode_arrow h)" by (rule paper_ZF_decoded_meeting[OF gh])
  have gf: "compose (decode_arrow g) (decode_arrow f) \<in> arrows" by (rule compose_arrow[OF fd gd fgd])
  have hg: "compose (decode_arrow h) (decode_arrow g) \<in> arrows" by (rule compose_arrow[OF gd hd ghd])
  show "coded_compose h (coded_compose g f) = coded_compose (coded_compose h g) f"
    by (simp only: paper_ZF_recode_compose_def paper_ZF_decode_encode_arrow[OF gf]
      paper_ZF_decode_encode_arrow[OF hg] compose_assoc[OF fd gd hd fgd ghd])
next
  fix f
  assume fa: "f \<in> coded_arrows"
  have fd: "decode_arrow f \<in> arrows" by (rule paper_ZF_decode_arrow_type[OF fa])
  have wo: "target (decode_arrow f) \<in> objects" by (rule target_object[OF fd])
  show "coded_compose (coded_identity (coded_target f)) f = f"
    by (simp only: paper_ZF_recode_compose_def paper_ZF_recode_identity_def paper_ZF_recode_target_def
      paper_ZF_decode_encode_arrow[OF identity_arrow[OF wo]] identity_left[OF fd] paper_ZF_encode_decode_arrow[OF fa])
next
  fix f
  assume fa: "f \<in> coded_arrows"
  have fd: "decode_arrow f \<in> arrows" by (rule paper_ZF_decode_arrow_type[OF fa])
  have wo: "source (decode_arrow f) \<in> objects" by (rule source_object[OF fd])
  show "coded_compose f (coded_identity (coded_source f)) = f"
    by (simp only: paper_ZF_recode_compose_def paper_ZF_recode_identity_def paper_ZF_recode_source_def
      paper_ZF_decode_encode_arrow[OF identity_arrow[OF wo]] identity_right[OF fd] paper_ZF_encode_decode_arrow[OF fa])
qed

end

theorem paper_ZF_recode_category:
  assumes category: "paper_category Obj Arrows source target compose identity"
    and injective: "inj_on e Arrows" and bound: "image e Arrows \<subseteq> explode B"
  shows "paper_category Obj (explode (paper_ZF_image_code B e Arrows))
    (paper_ZF_recode_source Arrows e source) (paper_ZF_recode_target Arrows e target)
    (paper_ZF_recode_compose Arrows e compose) (paper_ZF_recode_identity e identity)"
proof -
  interpret Original: paper_category Obj Arrows source target compose identity by (rule category)
  interpret Encoding: paper_ZF_category_encoding Obj Arrows source target compose identity e B
    by unfold_locales (rule injective, rule bound)
  show ?thesis by (rule Encoding.paper_ZF_encoded_category)
qed

end
