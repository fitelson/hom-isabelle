theory Bacon_Source_ZF_R_Arrow_Naturality
  imports Bacon_Source_ZF_R_Type_Recursion
begin

section \<open>Original typed maps still compose after arrow recoding\<close>

context paper_ZF_R_profile_encoding
begin

lemma paper_ZF_R_old_type_transport_compose:
  assumes first: "f \<in> Encoding.coded_arrows" and second: "i \<in> Encoding.coded_arrows"
    and meeting: "Encoding.coded_target f = Encoding.coded_source i"
    and member: "d \<in> paper_bbk_domain (Encoding.coded_source f) \<rho>"
  shows "paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<rho>) (Encoding.coded_compose i f) d =
    paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<rho>) i
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<rho>) f d)"
proof -
  have original_member: "d \<in> paper_bbk_domain (paper_arrow_source (Encoding.decode_arrow f)) \<rho>"
    using member by (simp only: paper_ZF_recode_source_def)
  have composite: "paper_arrow_map (paper_typed_compose paper_bbk_domain
      (Encoding.decode_arrow i) (Encoding.decode_arrow f)) \<rho> d =
    paper_arrow_map (Encoding.decode_arrow i) \<rho> (paper_arrow_map (Encoding.decode_arrow f) \<rho> d)"
    by (rule paper_typed_compose_map_on[
      where D=paper_bbk_domain and f="Encoding.decode_arrow f" and \<sigma>=\<rho>, OF original_member])
  show ?thesis by (simp only: paper_ZF_recode_transport_def
    Encoding.paper_ZF_decode_coded_compose[OF first second meeting]; rule composite)
qed

end

section \<open>Raw translated bodies are natural without child transport laws\<close>

text \<open>
  Along f:M→N, the translated body of fσ→τ(d) at (i,z)
  equals the body of d at (i∘f,z). The target object is the
  same on both sides, and z is unchanged. Source: Example 3.16(ii),
  p.54, and the translated-application equation on p.72.

  This is precomposition, not the separate coherence calculation that
  advances an argument along a later arrow. Neither a child inverse
  law nor naturality of either child record is needed here. The only
  value-typing guard is the original head d at source(f). Both bodies
  are undefined off their actual pair domains. No own-type recursion
  invariant or exponential-membership assumption is used.
\<close>

lemma paper_ZF_R_arrow_body_off_pairs:
  assumes outside: "(h,z) \<notin> paper_exponential_pairs (explode (paper_ZF_image_code ArrowBound encode Arrows))
    (paper_ZF_recode_source Arrows encode paper_arrow_source) (paper_ZF_recode_target Arrows encode paper_arrow_target)
    (\<lambda>N. explode (paper_ZF_rep_domain X N)) M"
  shows "paper_ZF_R_arrow_body \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y M d (h,z) = undefined"
  by (simp only: paper_ZF_R_arrow_body_def Let_def prod.case if_not_P[OF outside])

theorem paper_ZF_R_arrow_body_naturality:
  fixes X Y :: "'c paper_ZF_R_representation" and f d :: ZF
  assumes encoding: "paper_ZF_R_profile_encoding \<Sigma> G Obj Arrows encode ArrowBound"
    and arrow: "f \<in> explode (paper_ZF_image_code ArrowBound encode Arrows)"
    and member: "d \<in> paper_bbk_domain (paper_ZF_recode_source Arrows encode paper_arrow_source f) (Arr \<sigma> \<tau>)"
  shows "paper_ZF_R_arrow_body \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y
      (paper_ZF_recode_target Arrows encode paper_arrow_target f)
      (paper_ZF_recode_transport Arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>)) f d) =
    paper_exponential_transport (explode (paper_ZF_image_code ArrowBound encode Arrows))
      (paper_ZF_recode_source Arrows encode paper_arrow_source)
      (paper_ZF_recode_target Arrows encode paper_arrow_target)
      (paper_ZF_recode_compose Arrows encode (paper_typed_compose paper_bbk_domain))
      (\<lambda>N. explode (paper_ZF_rep_domain X N)) f
      (paper_ZF_R_arrow_body \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y
        (paper_ZF_recode_source Arrows encode paper_arrow_source f) d)"
proof -
  interpret Source: paper_ZF_R_profile_encoding \<Sigma> G Obj Arrows encode ArrowBound by (rule encoding)
  interpret Coded: paper_category Obj Source.Encoding.coded_arrows Source.Encoding.coded_source
    Source.Encoding.coded_target Source.Encoding.coded_compose Source.Encoding.coded_identity
    by (rule Source.Encoding.paper_ZF_encoded_category)
  let ?body = "paper_ZF_R_arrow_body \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y"
  let ?map = "paper_ZF_recode_transport Arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>))"
  show ?thesis
  proof (rule ext)
    fix p :: "ZF \<times> ZF"
    obtain i z where shape: "p = (i,z)" by (cases p) auto
    show "?body (Source.Encoding.coded_target f) (?map f d) p =
      paper_exponential_transport Source.Encoding.coded_arrows Source.Encoding.coded_source
        Source.Encoding.coded_target Source.Encoding.coded_compose (\<lambda>N. explode (paper_ZF_rep_domain X N)) f
        (?body (Source.Encoding.coded_source f) d) p"
    proof (cases "(i,z) \<in> paper_exponential_pairs Source.Encoding.coded_arrows Source.Encoding.coded_source
      Source.Encoding.coded_target (\<lambda>N. explode (paper_ZF_rep_domain X N)) (Source.Encoding.coded_target f)")
      case True
      have ia: "i \<in> Source.Encoding.coded_arrows"
        and origin: "Source.Encoding.coded_source i = Source.Encoding.coded_target f"
        using True by (auto simp only: paper_exponential_pairs_iff)
      have meeting: "Source.Encoding.coded_target f = Source.Encoding.coded_source i"
        by (rule origin[symmetric])
      have pair: "Elem (Opair i z) (paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode Arrows)
        Source.Encoding.coded_source Source.Encoding.coded_target (paper_ZF_rep_domain X) (Source.Encoding.coded_target f))"
        by (rule iffD2[OF paper_ZF_pair_code_iff_exponential True])
      have precomposed: "Elem (Opair (Source.Encoding.coded_compose i f) z)
        (paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode Arrows) Source.Encoding.coded_source
          Source.Encoding.coded_target (paper_ZF_rep_domain X) (Source.Encoding.coded_source f))"
        by (rule paper_ZF_pair_precompose[OF Source.Encoding.paper_ZF_encoded_category arrow pair])
      have target_same: "Source.Encoding.coded_target (Source.Encoding.coded_compose i f) = Source.Encoding.coded_target i"
        by (rule Coded.compose_target[OF arrow ia meeting])
      have maps: "?map (Source.Encoding.coded_compose i f) d = ?map i (?map f d)"
        by (rule Source.paper_ZF_R_old_type_transport_compose[OF arrow ia meeting member])
      show ?thesis
        by (simp only: shape paper_exponential_transport_on[OF True]
          paper_ZF_R_arrow_body_on[OF pair] paper_ZF_R_arrow_body_on[OF precomposed] target_same maps)
    next
      case False
      show ?thesis by (simp only: shape paper_exponential_transport_off[OF False]
        paper_ZF_R_arrow_body_off_pairs[OF False])
    qed
  qed
qed

section \<open>Graph encoding commutes with the actual code transport\<close>

theorem paper_ZF_R_arrow_encode_naturality:
  fixes X Y :: "'c paper_ZF_R_representation" and f d :: ZF
  assumes encoding: "paper_ZF_R_profile_encoding \<Sigma> G Obj Arrows encode ArrowBound"
    and arrow: "f \<in> explode (paper_ZF_image_code ArrowBound encode Arrows)"
    and member: "d \<in> paper_bbk_domain (paper_ZF_recode_source Arrows encode paper_arrow_source f) (Arr \<sigma> \<tau>)"
  shows "paper_ZF_R_arrow_encode \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y
      (paper_ZF_recode_target Arrows encode paper_arrow_target f)
      (paper_ZF_recode_transport Arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>)) f d) =
    paper_ZF_exponential_transport_code (paper_ZF_image_code ArrowBound encode Arrows)
      (paper_ZF_recode_source Arrows encode paper_arrow_source)
      (paper_ZF_recode_target Arrows encode paper_arrow_target)
      (paper_ZF_recode_compose Arrows encode (paper_typed_compose paper_bbk_domain)) (paper_ZF_rep_domain X) f
      (paper_ZF_R_arrow_encode \<Sigma> G ArrowBound encode Arrows \<sigma> \<tau> X Y
        (paper_ZF_recode_source Arrows encode paper_arrow_source f) d)"
proof -
  interpret Source: paper_ZF_R_profile_encoding \<Sigma> G Obj Arrows encode ArrowBound by (rule encoding)
  show ?thesis
    by (simp only: paper_ZF_R_arrow_encode_def paper_ZF_R_arrow_body_naturality[OF encoding arrow member];
      rule paper_ZF_encode_exponential_transport[OF Source.Encoding.paper_ZF_encoded_category arrow])
qed

end
