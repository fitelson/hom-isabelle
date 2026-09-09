theory Bacon_Source_ZF_R_Assignment_Naturality
  imports Bacon_Source_ZF_R_Representation_Assignments Bacon_Source_ZF_Action_Assignments
begin

section \<open>Encoding and decoding assignments commute with every arrow\<close>

text \<open>
  For h:M→N, the pointwise equations
  hρ(fρM(a))=fρN(hρold(a)) and their image-guarded inverses
  give h·(fM·g)=fN·(hold·g), and the corresponding decoding
  equation. Source: the assignment translation on p.72 and the
  abstraction clause of Definition 3.19, p.56.

  Each assigned name supplies its own R type. None stays None,
  so these equations neither complete an assignment nor change its
  adequacy. The arrow may be any coded category arrow, not just a
  root arrow. No interpretation or action-model totality is assumed.
\<close>

context paper_ZF_R_type_encoding
begin

theorem paper_ZF_R_encode_assignment_naturality:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and arrow: "h \<in> Encoding.coded_arrows"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_source h)) stock g"
  shows "paper_ZF_action_transport_assignment stock (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_source h) g) =
    paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h)
      (paper_hom_assignment stock (paper_arrow_map (Encoding.decode_arrow h)) g)"
proof -
  have source_object: "Encoding.coded_source h \<in> objects"
    unfolding paper_ZF_recode_source_def
    by (rule Encoding.source_object[OF Encoding.paper_ZF_decode_arrow_type[OF arrow]])
  show ?thesis
  proof (rule ext)
    fix n
    show "paper_ZF_action_transport_assignment stock (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) h
        (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_source h) g) n =
      paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h)
        (paper_hom_assignment stock (paper_arrow_map (Encoding.decode_arrow h)) g) n"
    proof (cases "g n")
      case None
      show ?thesis by (simp only: paper_ZF_action_transport_assignment_def paper_hom_assignment_def
        paper_ZF_R_encode_assignment_apply None option.map)
    next
      case (Some a)
      have member: "a \<in> paper_bbk_domain (Encoding.coded_source h) (stock n)"
        by (rule named_env_value[OF typed Some])
      have rt: "paper_R_type (stock n)" by (rule paper_ZF_R_original_member_type[OF source_object member])
      have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound (stock n) (type_representation (stock n))"
        by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
      have natural: "paper_ZF_rep_encode (type_representation (stock n)) (Encoding.coded_target h)
          (paper_ZF_recode_transport arrows encode (\<lambda>f. paper_arrow_map f (stock n)) h a) =
        paper_ZF_rep_transport (type_representation (stock n)) h
          (paper_ZF_rep_encode (type_representation (stock n)) (Encoding.coded_source h) a)"
        by (rule paper_action_map_equivariant[OF paper_ZF_R_type_invariant_forward[OF invariant] arrow member])
      have point: "paper_ZF_rep_transport (type_representation (stock n)) h
          (paper_ZF_rep_encode (type_representation (stock n)) (Encoding.coded_source h) a) =
        paper_ZF_rep_encode (type_representation (stock n)) (Encoding.coded_target h)
          (paper_arrow_map (Encoding.decode_arrow h) (stock n) a)"
        using natural by (simp only: paper_ZF_recode_transport_def; rule sym)
      show ?thesis by (simp only: paper_ZF_action_transport_assignment_def paper_hom_assignment_def
        paper_ZF_R_encode_assignment_apply Some option.map point)
    qed
  qed
qed

theorem paper_ZF_R_decode_assignment_naturality:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and arrow: "h \<in> Encoding.coded_arrows"
    and typed: "named_env_typed (\<lambda>\<rho>. explode (paper_ZF_rep_domain (type_representation \<rho>) (Encoding.coded_source h))) stock g"
  shows "paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation (Encoding.coded_target h)
      (paper_ZF_action_transport_assignment stock (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) h g) =
    paper_hom_assignment stock (paper_arrow_map (Encoding.decode_arrow h))
      (paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation (Encoding.coded_source h) g)"
proof (rule ext)
  fix n
  show "paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation (Encoding.coded_target h)
      (paper_ZF_action_transport_assignment stock (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) h g) n =
    paper_hom_assignment stock (paper_arrow_map (Encoding.decode_arrow h))
      (paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation (Encoding.coded_source h) g) n"
  proof (cases "g n")
    case None
    show ?thesis by (simp only: paper_ZF_R_decode_assignment_apply paper_ZF_action_transport_assignment_def
      paper_hom_assignment_def None option.map)
  next
    case (Some z)
    have member: "z \<in> explode (paper_ZF_rep_domain (type_representation (stock n)) (Encoding.coded_source h))"
      by (rule named_env_value[OF typed Some])
    have rt: "paper_R_type (stock n)" by (rule paper_ZF_R_type_representation_member_R[OF member])
    have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound (stock n) (type_representation (stock n))"
      by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
    have original_action: "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
        Encoding.coded_compose Encoding.coded_identity (\<lambda>M. paper_bbk_domain M (stock n))
        (paper_ZF_recode_transport arrows encode (\<lambda>f. paper_arrow_map f (stock n)))"
      by (rule paper_ZF_reindex_action[
        OF paper_R_bbk_selected_type_action[where \<sigma>="stock n", OF R_category] encode_injective encode_bounded])
    have inverse_map: "paper_action_map objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
        (\<lambda>M. explode (paper_ZF_rep_domain (type_representation (stock n)) M))
        (paper_ZF_rep_transport (type_representation (stock n)))
        (\<lambda>M. paper_bbk_domain M (stock n))
        (paper_ZF_recode_transport arrows encode (\<lambda>f. paper_arrow_map f (stock n)))
        (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n)) (type_representation (stock n)))"
      by (rule paper_ZF_R_type_invariant_inverse_map[OF invariant original_action])
    have natural: "paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n)) (type_representation (stock n))
        (Encoding.coded_target h) (paper_ZF_rep_transport (type_representation (stock n)) h z) =
      paper_ZF_recode_transport arrows encode (\<lambda>f. paper_arrow_map f (stock n)) h
        (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n)) (type_representation (stock n))
          (Encoding.coded_source h) z)"
      by (rule paper_action_map_equivariant[OF inverse_map arrow member])
    have point: "paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n)) (type_representation (stock n))
        (Encoding.coded_target h) (paper_ZF_rep_transport (type_representation (stock n)) h z) =
      paper_arrow_map (Encoding.decode_arrow h) (stock n)
        (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n)) (type_representation (stock n))
          (Encoding.coded_source h) z)"
      using natural by (simp only: paper_ZF_recode_transport_def)
    show ?thesis by (simp only: paper_ZF_R_decode_assignment_apply paper_ZF_action_transport_assignment_def
      paper_hom_assignment_def Some option.map point)
  qed
qed

end

end
