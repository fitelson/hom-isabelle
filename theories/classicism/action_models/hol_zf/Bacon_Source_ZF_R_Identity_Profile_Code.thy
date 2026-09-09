theory Bacon_Source_ZF_R_Identity_Profile_Code
  imports Bacon_Source_ZF_R_Negation_Profile_Code Bacon_Source_ZF_R_All_Type_Representation
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Identity_Profile
begin

section \<open>The identity truth-profile code tests transported equality\<close>

text \<open>
  The code of =σ applied to a,b∈Mσ contains exactly the outgoing
  arrows whose σ-maps identify a and b. Source: Definition 3.1(iii.f),
  p.44, Definition 3.10, p.50, and the =σ clause on p.56.
  No injectivity of those arrow maps is assumed. Quasi-Fregeanness
  is not needed to code the old equality test itself.
\<close>

context paper_ZF_R_profile_encoding
begin

theorem paper_ZF_R_identity_profile_code:
  assumes object: "M \<in> objects" and sr: "paper_R_type \<sigma>"
    and am: "a \<in> paper_bbk_domain M \<sigma>" and bm: "b \<in> paper_bbk_domain M \<sigma>"
  shows "proposition_code M (paper_R_binary_logical_application signature stock (paper_bbk_domain M)
      (paper_bbk_denote M) \<sigma> (SEq \<sigma>) a b) =
    Sep (paper_ZF_outgoing_code (paper_ZF_image_code Bound encode arrows) Encoding.coded_source M)
      (\<lambda>k. paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) k a =
        paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) k b)"
proof -
  let ?v = "paper_R_binary_logical_application signature stock (paper_bbk_domain M) (paper_bbk_denote M) \<sigma> (SEq \<sigma>) a b"
  have profile: "paper_bbk_truth_profile_on arrows M ?v =
      {h\<in>arrows. paper_arrow_source h = M \<and> paper_arrow_map h \<sigma> a = paper_arrow_map h \<sigma> b}"
    by (rule paper_R_identity_truth_profile[OF R_category object sr am bm])
  show ?thesis
  proof (rule iffD2[OF Ext], intro allI)
    fix k
    show "Elem k (proposition_code M ?v) =
      Elem k (Sep (paper_ZF_outgoing_code (paper_ZF_image_code Bound encode arrows) Encoding.coded_source M)
        (\<lambda>k. paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) k a =
          paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) k b))"
    proof (cases "k \<in> Encoding.coded_arrows")
      case True
      have ka: "Encoding.decode_arrow k \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF True])
      have coded: "Elem k (proposition_code M ?v) = (Encoding.decode_arrow k \<in> paper_bbk_truth_profile_on arrows M ?v)"
        using paper_ZF_R_truth_profile_code_on[where M=M and p="?v", OF ka]
        by (simp only: Encoding.paper_ZF_encode_decode_arrow[OF True])
      show ?thesis by (simp only: coded profile mem_Collect_eq Sep paper_ZF_outgoing_code_member
        paper_ZF_recode_transport_def paper_ZF_recode_source_def True ka; blast)
    next
      case False
      have absent: "\<not> Elem k (proposition_code M ?v)" by (rule paper_ZF_R_truth_profile_code_outside[OF False])
      show ?thesis using False absent by (simp only: Sep paper_ZF_outgoing_code_member; blast)
    qed
  qed
qed

end

context paper_ZF_R_type_encoding
begin

lemma paper_ZF_R_transport_equality_reflection:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and sr: "paper_R_type \<sigma>" and object: "M \<in> objects"
    and arrow: "k \<in> Encoding.coded_arrows" and source: "Encoding.coded_source k = M"
    and am: "a \<in> paper_bbk_domain M \<sigma>" and bm: "b \<in> paper_bbk_domain M \<sigma>"
  shows "(paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) k a =
      paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) k b) \<longleftrightarrow>
    (paper_ZF_rep_transport (type_representation \<sigma>) k (paper_ZF_rep_encode (type_representation \<sigma>) M a) =
      paper_ZF_rep_transport (type_representation \<sigma>) k (paper_ZF_rep_encode (type_representation \<sigma>) M b))"
proof -
  let ?R = "type_representation \<sigma>"
  let ?N = "Encoding.coded_target k"
  let ?u = "paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) k"
  have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<sigma> ?R"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional sr])
  have no: "?N \<in> objects" unfolding paper_ZF_recode_target_def
    by (rule Encoding.target_object[OF Encoding.paper_ZF_decode_arrow_type[OF arrow]])
  have old_action: "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
      Encoding.coded_compose Encoding.coded_identity (\<lambda>N. paper_bbk_domain N \<sigma>)
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>))"
    by (rule paper_ZF_reindex_action[OF paper_R_bbk_selected_type_action[where \<sigma>=\<sigma>, OF R_category]
      encode_injective encode_bounded])
  interpret Old: paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity "\<lambda>N. paper_bbk_domain N \<sigma>"
    "paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>)" by (rule old_action)
  have a_source: "a \<in> paper_bbk_domain (Encoding.coded_source k) \<sigma>" and b_source: "b \<in> paper_bbk_domain (Encoding.coded_source k) \<sigma>"
    using am bm by (simp_all only: source)
  have at: "?u a \<in> paper_bbk_domain ?N \<sigma>" by (rule Old.transport_type[OF arrow a_source])
  have bt: "?u b \<in> paper_bbk_domain ?N \<sigma>" by (rule Old.transport_type[OF arrow b_source])
  have af: "paper_ZF_rep_encode ?R ?N (?u a) = paper_ZF_rep_transport ?R k (paper_ZF_rep_encode ?R M a)"
    using paper_action_map_equivariant[OF paper_ZF_R_type_invariant_forward[OF invariant] arrow a_source]
    by (simp only: source)
  have bf: "paper_ZF_rep_encode ?R ?N (?u b) = paper_ZF_rep_transport ?R k (paper_ZF_rep_encode ?R M b)"
    using paper_action_map_equivariant[OF paper_ZF_R_type_invariant_forward[OF invariant] arrow b_source]
    by (simp only: source)
  have injective: "inj_on (paper_ZF_rep_encode ?R ?N) (paper_bbk_domain ?N \<sigma>)"
    by (rule paper_ZF_R_type_invariant_injective[OF invariant no])
  show ?thesis
  proof
    assume equal: "?u a = ?u b"
    have images: "paper_ZF_rep_encode ?R ?N (?u a) = paper_ZF_rep_encode ?R ?N (?u b)" by (simp only: equal)
    show "paper_ZF_rep_transport ?R k (paper_ZF_rep_encode ?R M a) = paper_ZF_rep_transport ?R k (paper_ZF_rep_encode ?R M b)"
      using images by (simp only: af bf)
  next
    assume equal: "paper_ZF_rep_transport ?R k (paper_ZF_rep_encode ?R M a) = paper_ZF_rep_transport ?R k (paper_ZF_rep_encode ?R M b)"
    have images: "paper_ZF_rep_encode ?R ?N (?u a) = paper_ZF_rep_encode ?R ?N (?u b)" by (simp only: af bf; rule equal)
    show "?u a = ?u b" by (rule inj_onD[OF injective images at bt])
  qed
qed

theorem paper_ZF_R_identity_code_at_values:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and sr: "paper_R_type \<sigma>" and object: "M \<in> objects"
    and am: "a \<in> paper_bbk_domain M \<sigma>" and bm: "b \<in> paper_bbk_domain M \<sigma>"
  shows "proposition_code M (paper_R_binary_logical_application signature stock (paper_bbk_domain M)
      (paper_bbk_denote M) \<sigma> (SEq \<sigma>) a b) =
    Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source M)
      (\<lambda>k. paper_ZF_rep_transport (type_representation \<sigma>) k (paper_ZF_rep_encode (type_representation \<sigma>) M a) =
        paper_ZF_rep_transport (type_representation \<sigma>) k (paper_ZF_rep_encode (type_representation \<sigma>) M b))"
proof -
  have original: "proposition_code M (paper_R_binary_logical_application signature stock (paper_bbk_domain M)
      (paper_bbk_denote M) \<sigma> (SEq \<sigma>) a b) =
      Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source M)
        (\<lambda>k. paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) k a =
          paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) k b)"
    by (rule paper_ZF_R_identity_profile_code[OF object sr am bm])
  show ?thesis
  proof (simp only: original; rule iffD2[OF Ext], intro allI)
    fix k
    show "Elem k (Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source M)
        (\<lambda>k. paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) k a =
          paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) k b)) =
      Elem k (Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source M)
        (\<lambda>k. paper_ZF_rep_transport (type_representation \<sigma>) k (paper_ZF_rep_encode (type_representation \<sigma>) M a) =
          paper_ZF_rep_transport (type_representation \<sigma>) k (paper_ZF_rep_encode (type_representation \<sigma>) M b)))"
    proof (cases "k \<in> Encoding.coded_arrows \<and> Encoding.coded_source k = M")
      case True
      have ka: "k \<in> Encoding.coded_arrows" and ks: "Encoding.coded_source k = M" using True by blast+
      show ?thesis by (simp only: Sep paper_ZF_outgoing_code_member
        paper_ZF_R_transport_equality_reflection[OF bounded fregean functional sr object ka ks am bm])
    next
      case False
      then show ?thesis by (simp only: Sep paper_ZF_outgoing_code_member; blast)
    qed
  qed
qed

end

end
