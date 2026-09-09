theory Bacon_Source_ZF_R_Individual_Base
  imports Bacon_Source_ZF_R_Type_Recursion
begin

section \<open>The literal individual base of the recursive record\<close>

text \<open>
  Proposition 3.22 starts with fᵉM(a)=a. The recursively chosen
  individual domain is exactly Mₑ when that set lies in the supplied
  individual bound. Source: p.72. The locale fixes that bound but does
  not assume its adequacy or any all-type representation invariant.
  Each theorem states the bound it uses; original values are ZF values.
\<close>

locale paper_ZF_R_type_encoding =
  paper_ZF_R_profile_encoding signature stock objects arrows encode ArrowBound
  for signature :: "'c ssignature" and stock :: sgcontext
    and objects :: "('c,ZF) paper_bbk_model_data set" and arrows :: "('c,ZF) paper_R_bbk_arrow set"
    and encode :: "('c,ZF) paper_R_bbk_arrow \<Rightarrow> ZF" and ArrowBound :: ZF +
  fixes IndividualBound :: ZF
begin

abbreviation type_representation where
  "type_representation \<equiv> paper_ZF_R_type_representation signature stock IndividualBound ArrowBound encode arrows"

lemma paper_ZF_R_Ind_fields:
  "paper_ZF_rep_bound (type_representation Ind) = (\<lambda>_. IndividualBound)"
  "paper_ZF_rep_domain (type_representation Ind) = paper_ZF_identity_fiber_code IndividualBound (\<lambda>M. paper_bbk_domain M Ind)"
  "paper_ZF_rep_encode (type_representation Ind) = (\<lambda>M d. d)"
  "paper_ZF_rep_transport (type_representation Ind) = paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Ind)"
  by (simp_all only: paper_ZF_R_type_representation.simps paper_ZF_R_individual_representation_def
    paper_ZF_type_representation.select_convs)

lemma paper_ZF_R_Ind_elements:
  assumes bounded: "paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
  shows "explode (paper_ZF_rep_domain (type_representation Ind) M) = paper_bbk_domain M Ind"
  by (simp only: paper_ZF_R_Ind_fields;
    rule paper_ZF_identity_fiber_elements[where D="\<lambda>M. paper_bbk_domain M Ind" and W=M, OF bounded])

lemma paper_ZF_R_Ind_bound:
  assumes bounded: "paper_bbk_domain M Ind \<subseteq> explode IndividualBound" and member: "d \<in> paper_bbk_domain M Ind"
  shows "paper_ZF_rep_encode (type_representation Ind) M d \<in> explode (paper_ZF_rep_bound (type_representation Ind) M)"
  by (simp only: paper_ZF_R_Ind_fields; rule subsetD[OF bounded member])

theorem paper_ZF_R_Ind_bijection:
  assumes bounded: "paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
  shows "bij_betw (paper_ZF_rep_encode (type_representation Ind) M) (paper_bbk_domain M Ind)
    (explode (paper_ZF_rep_domain (type_representation Ind) M))"
  by (simp only: paper_ZF_R_Ind_fields(3) paper_ZF_R_Ind_elements[OF bounded]; simp add: bij_betw_def)

lemma paper_ZF_R_Ind_range:
  assumes bounded: "paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
  shows "explode (paper_ZF_rep_domain (type_representation Ind) M) =
    image (paper_ZF_rep_encode (type_representation Ind) M) (paper_bbk_domain M Ind)"
  by (simp only: paper_ZF_R_Ind_elements[OF bounded] paper_ZF_R_Ind_fields(3); simp)

lemma paper_ZF_R_Ind_inverse:
  assumes member: "d \<in> paper_bbk_domain M Ind"
  shows "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N Ind) (type_representation Ind) M d = d"
proof -
  have injective: "inj_on (\<lambda>x::ZF. x) (paper_bbk_domain M Ind)" by simp
  have inverse: "inv_into (paper_bbk_domain M Ind) (\<lambda>x. x) ((\<lambda>x. x) d) = d"
    by (rule inv_into_f_f[where A="paper_bbk_domain M Ind" and f="\<lambda>x. x" and x=d, OF injective member])
  show ?thesis using inverse by (simp only: paper_ZF_rep_inverse_def paper_ZF_R_Ind_fields)
qed

lemma paper_ZF_R_Ind_decode_encode:
  assumes member: "d \<in> paper_bbk_domain M Ind"
  shows "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N Ind) (type_representation Ind) M
    (paper_ZF_rep_encode (type_representation Ind) M d) = d"
  by (simp only: paper_ZF_R_Ind_fields(3); rule paper_ZF_R_Ind_inverse[OF member])

lemma paper_ZF_R_Ind_inverse_type:
  assumes bounded: "paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and member: "z \<in> explode (paper_ZF_rep_domain (type_representation Ind) M)"
  shows "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N Ind) (type_representation Ind) M z \<in> paper_bbk_domain M Ind"
proof -
  have original: "z \<in> paper_bbk_domain M Ind" using member by (simp only: paper_ZF_R_Ind_elements[OF bounded])
  show ?thesis by (simp only: paper_ZF_R_Ind_inverse[OF original]; rule original)
qed

lemma paper_ZF_R_Ind_encode_decode:
  assumes bounded: "paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and member: "z \<in> explode (paper_ZF_rep_domain (type_representation Ind) M)"
  shows "paper_ZF_rep_encode (type_representation Ind) M
    (paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N Ind) (type_representation Ind) M z) = z"
proof -
  have original: "z \<in> paper_bbk_domain M Ind" using member by (simp only: paper_ZF_R_Ind_elements[OF bounded])
  show ?thesis by (simp only: paper_ZF_R_Ind_inverse[OF original] paper_ZF_R_Ind_fields(3))
qed

theorem paper_ZF_R_Ind_action:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
  shows "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity
    (\<lambda>M. explode (paper_ZF_rep_domain (type_representation Ind) M)) (paper_ZF_rep_transport (type_representation Ind))"
proof -
  have original: "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
      Encoding.coded_compose Encoding.coded_identity (\<lambda>M. paper_bbk_domain M Ind)
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Ind))"
    by (rule paper_ZF_reindex_action[
      OF paper_R_bbk_selected_type_action[where \<sigma>=Ind, OF R_category] encode_injective encode_bounded])
  show ?thesis by (simp only: paper_ZF_R_Ind_fields; rule paper_ZF_identity_base_action[OF original bounded])
qed

theorem paper_ZF_R_Ind_forward_map:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
  shows "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    (\<lambda>M. paper_bbk_domain M Ind) (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Ind))
    (\<lambda>M. explode (paper_ZF_rep_domain (type_representation Ind) M)) (paper_ZF_rep_transport (type_representation Ind))
    (paper_ZF_rep_encode (type_representation Ind))"
proof (rule paper_action_mapI)
  fix M d
  assume object: "M \<in> objects" and member: "d \<in> paper_bbk_domain M Ind"
  show "paper_ZF_rep_encode (type_representation Ind) M d \<in> explode (paper_ZF_rep_domain (type_representation Ind) M)"
    by (simp only: paper_ZF_R_Ind_fields(3) paper_ZF_R_Ind_elements[OF bounded[OF object]]; rule member)
next
  fix h d
  assume "h \<in> Encoding.coded_arrows" and "d \<in> paper_bbk_domain (Encoding.coded_source h) Ind"
  show "paper_ZF_rep_encode (type_representation Ind) (Encoding.coded_target h)
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Ind) h d) =
      paper_ZF_rep_transport (type_representation Ind) h
        (paper_ZF_rep_encode (type_representation Ind) (Encoding.coded_source h) d)"
    by (simp only: paper_ZF_R_Ind_fields)
qed

theorem paper_ZF_R_Ind_inverse_map:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
  shows "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    (\<lambda>M. explode (paper_ZF_rep_domain (type_representation Ind) M)) (paper_ZF_rep_transport (type_representation Ind))
    (\<lambda>M. paper_bbk_domain M Ind) (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Ind))
    (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M Ind) (type_representation Ind))"
proof -
  interpret Coded: paper_category objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity by (rule Encoding.paper_ZF_encoded_category)
  interpret Values: paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity
    "\<lambda>M. explode (paper_ZF_rep_domain (type_representation Ind) M)" "paper_ZF_rep_transport (type_representation Ind)"
    by (rule paper_ZF_R_Ind_action[OF bounded])
  show ?thesis
  proof (rule paper_action_mapI)
    fix M d
    assume object: "M \<in> objects" and member: "d \<in> explode (paper_ZF_rep_domain (type_representation Ind) M)"
    have original: "d \<in> paper_bbk_domain M Ind" using member by (simp only: paper_ZF_R_Ind_elements[OF bounded[OF object]])
    show "paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M Ind) (type_representation Ind) M d \<in> paper_bbk_domain M Ind"
      by (simp only: paper_ZF_R_Ind_inverse[OF original]; rule original)
  next
    fix h d
    assume arrow: "h \<in> Encoding.coded_arrows"
      and member: "d \<in> explode (paper_ZF_rep_domain (type_representation Ind) (Encoding.coded_source h))"
    have source_bound: "paper_bbk_domain (Encoding.coded_source h) Ind \<subseteq> explode IndividualBound"
      by (rule bounded[OF Coded.source_object[OF arrow]])
    have target_bound: "paper_bbk_domain (Encoding.coded_target h) Ind \<subseteq> explode IndividualBound"
      by (rule bounded[OF Coded.target_object[OF arrow]])
    have original: "d \<in> paper_bbk_domain (Encoding.coded_source h) Ind"
      using member by (simp only: paper_ZF_R_Ind_elements[OF source_bound])
    have transported: "paper_ZF_rep_transport (type_representation Ind) h d \<in> paper_bbk_domain (Encoding.coded_target h) Ind"
      using Values.transport_type[OF arrow member] by (simp only: paper_ZF_R_Ind_elements[OF target_bound])
    show "paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M Ind) (type_representation Ind) (Encoding.coded_target h)
        (paper_ZF_rep_transport (type_representation Ind) h d) =
        paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h Ind) h
          (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M Ind) (type_representation Ind) (Encoding.coded_source h) d)"
      by (simp only: paper_ZF_R_Ind_inverse[OF transported] paper_ZF_R_Ind_inverse[OF original];
        simp only: paper_ZF_R_Ind_fields)
  qed
qed

end

end
