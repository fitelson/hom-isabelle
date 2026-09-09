theory Bacon_Source_ZF_R_Identity_Correspondence
  imports Bacon_Source_ZF_R_Identity_Profile_Code Bacon_Source_ZF_R_Binary_Logical_Graphs
begin

section \<open>The encoded primitive identity is the literal nested graph\<close>

text \<open>
  At the outer pair ⟨i,a⟩ and inner pair ⟨j,b⟩, the identity
  value returns {k:target(j)→V | kσ(jσ(a))=kσ(b)}.
  Source: Definition 3.19, p.56, and Proposition 3.22, p.72.
  The source identity profile gives equality of old transported values.
  Child σ-encoding injectivity reflects that equality after recoding.

  The shared binary graph theorem performs both Lambda extensionality
  steps on their complete actual PairCode domains. Its result callback
  is discharged here by the proved identity profile, not assumed as a
  semantic clause. No category-arrow map is assumed injective, and no
  logical-stock membership, evaluator equation, or totality is assumed.
\<close>

context paper_ZF_R_type_encoding
begin

theorem paper_ZF_R_Eq_empty_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and sr: "paper_R_type \<sigma>" and object: "M \<in> objects"
  shows "paper_ZF_rep_encode (type_representation (Arr \<sigma> (Arr \<sigma> Prop))) M
      (paper_bbk_denote M Map.empty (NLogical (SEq \<sigma>))) =
    paper_ZF_logical_value (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) M (SEq \<sigma>)"
proof -
  let ?result = "\<lambda>N x y. Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source N)
    (\<lambda>k. paper_ZF_rep_transport (type_representation \<sigma>) k x = paper_ZF_rep_transport (type_representation \<sigma>) k y)"
  have clause: "proposition_code N (paper_R_binary_logical_application signature stock (paper_bbk_domain N)
      (paper_bbk_denote N) \<sigma> (SEq \<sigma>) x y) =
      ?result N (paper_ZF_rep_encode (type_representation \<sigma>) N x) (paper_ZF_rep_encode (type_representation \<sigma>) N y)"
    if no: "N \<in> objects" and xm: "x \<in> paper_bbk_domain N \<sigma>" and ym: "y \<in> paper_bbk_domain N \<sigma>" for N x y
    by (rule paper_ZF_R_identity_code_at_values[OF bounded fregean functional sr no xm ym])
  have graph: "paper_ZF_rep_encode (type_representation (Arr \<sigma> (Arr \<sigma> Prop))) M
      (paper_bbk_denote M Map.empty (NLogical (SEq \<sigma>))) =
    paper_ZF_pair_lambda (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source Encoding.coded_target
      (paper_ZF_rep_domain (type_representation \<sigma>)) M
      (\<lambda>i a. paper_ZF_pair_lambda (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source Encoding.coded_target
        (paper_ZF_rep_domain (type_representation \<sigma>)) (Encoding.coded_target i)
        (\<lambda>j b. ?result (Encoding.coded_target j) (paper_ZF_rep_transport (type_representation \<sigma>) j a) b))"
    by (rule paper_ZF_R_binary_logical_graph[where result="?result" and l="SEq \<sigma>" and \<sigma>=\<sigma>,
      OF bounded fregean functional sr paper_logical_type.simps(6) object clause])
  show ?thesis by (simp only: paper_ZF_logical_value.simps; rule graph)
qed

theorem paper_ZF_R_Eq_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and sr: "paper_R_type \<sigma>" and object: "M \<in> objects"
    and typed: "named_env_typed (paper_bbk_domain M) stock g"
  shows "paper_ZF_rep_encode (type_representation (Arr \<sigma> (Arr \<sigma> Prop))) M
      (paper_bbk_denote M g (NLogical (SEq \<sigma>))) =
    paper_ZF_logical_value (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) M (SEq \<sigma>)"
proof -
  interpret Model: paper_R_bbk_model signature stock "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF R_category object]])
  have lr: "paper_R_type (paper_logical_type (SEq \<sigma>))" using sr by simp
  show ?thesis by (simp only: Model.paper_R_logical_denote_empty[OF lr typed];
    rule paper_ZF_R_Eq_empty_correspondence[OF bounded fregean functional sr object])
qed

corollary paper_ZF_R_eval_Eq:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and sr: "paper_R_type \<sigma>" and arrow: "h \<in> Encoding.coded_arrows"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
  shows "paper_ZF_R_constructed_eval Root (NLogical (SEq \<sigma>)) h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation (Arr \<sigma> (Arr \<sigma> Prop))) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g (NLogical (SEq \<sigma>))))"
  by (simp only: paper_ZF_action_eval.simps
    paper_ZF_R_Eq_correspondence[OF bounded fregean functional sr paper_ZF_R_eval_target_object[OF arrow] typed])

end

end
