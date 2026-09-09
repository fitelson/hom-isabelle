theory Bacon_Source_ZF_R_Lambda_Input
  imports Bacon_Source_ZF_R_Assignment_Naturality Bacon_Source_ZF_R_Eval_Basic_Correspondence
begin

section \<open>Each new abstraction input is an encoded old body assignment\<close>

text \<open>
  For i:M→N and z in the selected input fiber at N, let
  a=(fσN)⁻¹(z). Transport the old assignment g along i and update
  n:σ to a. Encoding that assignment gives precisely
  (i·(fM·g))[n↦z]. Source: Definition 3.19, p.56, and the
  representation equation of Proposition 3.22, p.72.
  The old g need be adequate only for λn.B. No freshness or
  completion is required, and repeated binders keep their shadowing.
\<close>

context paper_ZF_R_type_encoding
begin

lemma paper_ZF_R_coded_homomorphism:
  assumes arrow: "i \<in> Encoding.coded_arrows"
  shows "paper_R_bbk_homomorphism signature stock
    (paper_bbk_domain (Encoding.coded_source i)) (paper_bbk_denote (Encoding.coded_source i))
    (paper_bbk_domain (Encoding.coded_target i)) (paper_bbk_denote (Encoding.coded_target i))
    (paper_arrow_map (Encoding.decode_arrow i))"
proof -
  have original: "Encoding.decode_arrow i \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF arrow])
  have morphism: "paper_R_bbk_data_morphism signature stock
      (paper_arrow_source (Encoding.decode_arrow i)) (paper_arrow_target (Encoding.decode_arrow i))
      (paper_arrow_map (Encoding.decode_arrow i))"
    by (rule paper_R_bbk_arrows_morphism[OF paper_R_bbk_subcategory_arrow[OF R_category original]])
  show ?thesis using paper_R_bbk_data_morphism_raw[OF morphism]
    by (simp only: paper_ZF_recode_source_def paper_ZF_recode_target_def)
qed

theorem paper_ZF_R_lambda_input_assignment:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and arrow: "i \<in> Encoding.coded_arrows"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_source i)) stock g"
    and member: "z \<in> explode (paper_ZF_rep_domain (type_representation (stock n)) (Encoding.coded_target i))"
  shows "(paper_ZF_action_transport_assignment stock (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) i
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_source i) g))(n := Some z) =
    paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target i)
      ((paper_hom_assignment stock (paper_arrow_map (Encoding.decode_arrow i)) g)
        (n := Some (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n))
          (type_representation (stock n)) (Encoding.coded_target i) z)))"
proof -
  have object: "Encoding.coded_target i \<in> objects" by (rule paper_ZF_R_eval_target_object[OF arrow])
  have rt: "paper_R_type (stock n)" by (rule paper_ZF_R_type_representation_member_R[OF member])
  have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound (stock n) (type_representation (stock n))"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
  have inverse: "paper_ZF_rep_encode (type_representation (stock n)) (Encoding.coded_target i)
      (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n)) (type_representation (stock n))
        (Encoding.coded_target i) z) = z"
    by (rule paper_ZF_R_type_invariant_encode_decode[OF invariant object member])
  show ?thesis by (simp only: paper_ZF_R_encode_assignment_naturality[OF bounded fregean functional arrow typed]
    paper_ZF_R_encode_assignment_update inverse)
qed

theorem paper_ZF_R_lambda_old_input:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and arrow: "i \<in> Encoding.coded_arrows"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_source i)) stock g"
    and adequate: "named_adequate g (NLam n B)"
    and member: "z \<in> explode (paper_ZF_rep_domain (type_representation (stock n)) (Encoding.coded_target i))"
  shows "named_env_typed (paper_bbk_domain (Encoding.coded_target i)) stock
      ((paper_hom_assignment stock (paper_arrow_map (Encoding.decode_arrow i)) g)
        (n := Some (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n))
          (type_representation (stock n)) (Encoding.coded_target i) z))) \<and>
    named_adequate ((paper_hom_assignment stock (paper_arrow_map (Encoding.decode_arrow i)) g)
      (n := Some (paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n))
        (type_representation (stock n)) (Encoding.coded_target i) z))) B"
proof -
  let ?k = "paper_hom_assignment stock (paper_arrow_map (Encoding.decode_arrow i)) g"
  let ?a = "paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n)) (type_representation (stock n)) (Encoding.coded_target i) z"
  have object: "Encoding.coded_target i \<in> objects" by (rule paper_ZF_R_eval_target_object[OF arrow])
  have rt: "paper_R_type (stock n)" by (rule paper_ZF_R_type_representation_member_R[OF member])
  have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound (stock n) (type_representation (stock n))"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
  have am: "?a \<in> paper_bbk_domain (Encoding.coded_target i) (stock n)"
    by (rule paper_ZF_R_type_invariant_decode_type[OF invariant object member])
  have kt: "named_env_typed (paper_bbk_domain (Encoding.coded_target i)) stock ?k"
    by (rule paper_R_bbk_homomorphism_assignment_typed[OF paper_ZF_R_coded_homomorphism[OF arrow] typed])
  have updated: "named_env_typed (paper_bbk_domain (Encoding.coded_target i)) stock (?k(n := Some ?a))"
    by (rule named_assignment_update_typed[where D="paper_bbk_domain (Encoding.coded_target i)" and G=stock and n=n,
      OF kt am])
  have ka: "named_adequate ?k (NLam n B)" by (rule iffD2[OF paper_hom_assignment_adequate_iff adequate])
  have body: "named_adequate (?k(n := Some ?a)) B" by (rule iffD2[OF named_binder_update_adequate_iff ka])
  show ?thesis by (rule conjI[OF updated body])
qed

end

end
