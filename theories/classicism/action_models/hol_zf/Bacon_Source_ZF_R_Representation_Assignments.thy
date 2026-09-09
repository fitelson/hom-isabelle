theory Bacon_Source_ZF_R_Representation_Assignments
  imports Bacon_Source_ZF_R_Representation_Assignment_Syntax Bacon_Source_ZF_R_All_Type_Representation
begin

section \<open>Typed partial assignments correspond fiber by fiber\<close>

text \<open>
  At each original object M, forward and inverse partial assignments
  preserve typing and are mutually inverse. The old domains are those
  of an independently validated R model; the new domains are the actual
  recursive representation domains.

  Forward typing recovers R types from old-domain membership. Inverse
  typing recovers them from the raw recursion's empty domains outside R,
  before invoking any R-type invariant. No all-type inverse law is
  assumed at non-R types. Source role: Proposition 3.22, p.72, and
  the adequate partial assignments in Definitions 3.1 and 3.19.
  These are assignment results only, not term interpretation or totality.
\<close>

context paper_ZF_R_type_encoding
begin

lemma paper_ZF_R_original_member_type:
  assumes object: "M \<in> objects" and member: "a \<in> paper_bbk_domain M \<rho>"
  shows "paper_R_type \<rho>"
proof -
  have valid: "paper_R_bbk_data_valid signature stock M"
    by (rule paper_R_bbk_subcategory_models[OF R_category object])
  interpret Model: paper_R_bbk_model signature stock "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF valid])
  show ?thesis by (rule Model.paper_R_domain_member_type[OF member])
qed

theorem paper_ZF_R_encode_assignment_typed:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and object: "M \<in> objects" and typed: "named_env_typed (paper_bbk_domain M) stock g"
  shows "named_env_typed (\<lambda>\<rho>. explode (paper_ZF_rep_domain (type_representation \<rho>) M)) stock
    (paper_ZF_R_encode_assignment stock type_representation M g)"
  unfolding paper_ZF_R_encode_assignment_def
proof (rule paper_hom_assignment_typed[where D="paper_bbk_domain M", OF _ typed])
  fix \<rho> a
  assume member: "a \<in> paper_bbk_domain M \<rho>"
  have rt: "paper_R_type \<rho>" by (rule paper_ZF_R_original_member_type[OF object member])
  have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<rho> (type_representation \<rho>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
  show "paper_ZF_rep_encode (type_representation \<rho>) M a \<in>
    explode (paper_ZF_rep_domain (type_representation \<rho>) M)"
    by (rule paper_ZF_R_type_invariant_encode_type[OF invariant object member])
qed

theorem paper_ZF_R_decode_assignment_typed:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and object: "M \<in> objects"
    and typed: "named_env_typed (\<lambda>\<rho>. explode (paper_ZF_rep_domain (type_representation \<rho>) M)) stock g"
  shows "named_env_typed (paper_bbk_domain M) stock
    (paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation M g)"
  unfolding paper_ZF_R_decode_assignment_def
proof (rule paper_hom_assignment_typed[
    where D="\<lambda>\<rho>. explode (paper_ZF_rep_domain (type_representation \<rho>) M)" and E="paper_bbk_domain M",
    OF _ typed])
  fix \<rho> z
  assume member: "z \<in> explode (paper_ZF_rep_domain (type_representation \<rho>) M)"
  have rt: "paper_R_type \<rho>" by (rule paper_ZF_R_type_representation_member_R[OF member])
  have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<rho> (type_representation \<rho>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
  show "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<rho>) (type_representation \<rho>) M z \<in> paper_bbk_domain M \<rho>"
    by (rule paper_ZF_R_type_invariant_decode_type[OF invariant object member])
qed

section \<open>Round trips preserve both values and undefined entries\<close>

theorem paper_ZF_R_decode_encode_assignment:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and object: "M \<in> objects" and typed: "named_env_typed (paper_bbk_domain M) stock g"
  shows "paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation M
    (paper_ZF_R_encode_assignment stock type_representation M g) = g"
proof (rule ext)
  fix n
  show "paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation M
    (paper_ZF_R_encode_assignment stock type_representation M g) n = g n"
  proof (cases "g n")
    case None
    show ?thesis by (simp only: paper_ZF_R_decode_assignment_apply paper_ZF_R_encode_assignment_apply None option.map)
  next
    case (Some a)
    have member: "a \<in> paper_bbk_domain M (stock n)" by (rule named_env_value[OF typed Some])
    have rt: "paper_R_type (stock n)" by (rule paper_ZF_R_original_member_type[OF object member])
    have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound (stock n) (type_representation (stock n))"
      by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
    have inverse: "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N (stock n)) (type_representation (stock n)) M
      (paper_ZF_rep_encode (type_representation (stock n)) M a) = a"
      by (rule paper_ZF_R_type_invariant_decode_encode[OF invariant object member])
    show ?thesis by (simp only: paper_ZF_R_decode_assignment_apply paper_ZF_R_encode_assignment_apply Some option.map inverse)
  qed
qed

theorem paper_ZF_R_encode_decode_assignment:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and object: "M \<in> objects"
    and typed: "named_env_typed (\<lambda>\<rho>. explode (paper_ZF_rep_domain (type_representation \<rho>) M)) stock g"
  shows "paper_ZF_R_encode_assignment stock type_representation M
    (paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation M g) = g"
proof (rule ext)
  fix n
  show "paper_ZF_R_encode_assignment stock type_representation M
    (paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation M g) n = g n"
  proof (cases "g n")
    case None
    show ?thesis by (simp only: paper_ZF_R_encode_assignment_apply paper_ZF_R_decode_assignment_apply None option.map)
  next
    case (Some z)
    have member: "z \<in> explode (paper_ZF_rep_domain (type_representation (stock n)) M)"
      by (rule named_env_value[OF typed Some])
    have rt: "paper_R_type (stock n)" by (rule paper_ZF_R_type_representation_member_R[OF member])
    have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound (stock n) (type_representation (stock n))"
      by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
    have inverse: "paper_ZF_rep_encode (type_representation (stock n)) M
      (paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N (stock n)) (type_representation (stock n)) M z) = z"
      by (rule paper_ZF_R_type_invariant_encode_decode[OF invariant object member])
    show ?thesis by (simp only: paper_ZF_R_encode_assignment_apply paper_ZF_R_decode_assignment_apply Some option.map inverse)
  qed
qed

end

end
