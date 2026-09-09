theory Bacon_Source_ZF_R_Boolean_Correspondence
  imports Bacon_Source_ZF_R_Binary_Logical_Graphs Bacon_Source_ZF_R_Boolean_Profile_Code
begin

section \<open>The independent ∧ and ∨ graphs equal the represented logical values\<close>

text \<open>
  For outer (i,p) and inner (j,q), ∧ returns jₜ(p)∩q and ∨
  returns jₜ(p)∪q, exactly as in Definition 3.19, p.56.
  The nested graph theorem ranges over every pair in both actual
  dependent domains. Its first argument is transported by j.

  Each primitive-specific callback is discharged by the proved old
  all-domain truth and coded profile equation. Neither selected-stock
  membership, evaluator correspondence, logical closure nor totality
  is an assumption. These are two logical cases of Proposition 3.22's
  representation, not completion of every evaluator case.
\<close>

context paper_ZF_R_type_encoding
begin

theorem paper_ZF_R_And_empty_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and object: "M \<in> objects"
  shows "paper_ZF_rep_encode (type_representation (Arr Prop (Arr Prop Prop))) M
      (paper_bbk_denote M Map.empty (NLogical SAnd)) =
    paper_ZF_logical_value (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) M SAnd"
proof -
  have pr: "paper_R_type Prop" by simp
  have graph: "paper_ZF_rep_encode (type_representation (Arr Prop (Arr Prop Prop))) M
      (paper_bbk_denote M Map.empty (NLogical SAnd)) =
    paper_ZF_pair_lambda (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source Encoding.coded_target
      (paper_ZF_rep_domain (type_representation Prop)) M
      (\<lambda>i p. paper_ZF_pair_lambda (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source Encoding.coded_target
        (paper_ZF_rep_domain (type_representation Prop)) (Encoding.coded_target i)
        (\<lambda>j q. Sep (paper_ZF_rep_transport (type_representation Prop) j p) (\<lambda>k. Elem k q)))"
  proof (rule paper_ZF_R_binary_logical_graph[
      where \<sigma>=Prop and l=SAnd and result="\<lambda>N p q. Sep p (\<lambda>j. Elem j q)",
      OF bounded fregean functional pr paper_logical_type.simps(2) object])
    fix N x y
    assume no: "N \<in> objects" and xm: "x \<in> paper_bbk_domain N Prop" and ym: "y \<in> paper_bbk_domain N Prop"
    show "proposition_code N (paper_R_binary_logical_application signature stock (paper_bbk_domain N)
        (paper_bbk_denote N) Prop SAnd x y) = Sep (paper_ZF_rep_encode (type_representation Prop) N x)
          (\<lambda>j. Elem j (paper_ZF_rep_encode (type_representation Prop) N y))"
      using paper_ZF_R_conjunction_profile_code[OF no xm ym]
      by (simp only: paper_ZF_R_Prop_fields(3))
  qed
  show ?thesis by (simp only: paper_ZF_logical_value.simps; rule graph)
qed

theorem paper_ZF_R_And_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and object: "M \<in> objects" and typed: "named_env_typed (paper_bbk_domain M) stock g"
  shows "paper_ZF_rep_encode (type_representation (Arr Prop (Arr Prop Prop))) M (paper_bbk_denote M g (NLogical SAnd)) =
    paper_ZF_logical_value (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) M SAnd"
proof -
  interpret Model: paper_R_bbk_model signature stock "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF R_category object]])
  have lr: "paper_R_type (paper_logical_type SAnd)" by simp
  show ?thesis by (simp only: Model.paper_R_logical_denote_empty[OF lr typed];
    rule paper_ZF_R_And_empty_correspondence[OF bounded fregean functional object])
qed

corollary paper_ZF_R_eval_And:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and arrow: "h \<in> Encoding.coded_arrows"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
  shows "paper_ZF_R_constructed_eval Root (NLogical SAnd) h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation (Arr Prop (Arr Prop Prop))) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g (NLogical SAnd)))"
  by (simp only: paper_ZF_action_eval.simps
    paper_ZF_R_And_correspondence[OF bounded fregean functional paper_ZF_R_eval_target_object[OF arrow] typed])

theorem paper_ZF_R_Or_empty_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and object: "M \<in> objects"
  shows "paper_ZF_rep_encode (type_representation (Arr Prop (Arr Prop Prop))) M
      (paper_bbk_denote M Map.empty (NLogical SOr)) =
    paper_ZF_logical_value (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) M SOr"
proof -
  have pr: "paper_R_type Prop" by simp
  have graph: "paper_ZF_rep_encode (type_representation (Arr Prop (Arr Prop Prop))) M
      (paper_bbk_denote M Map.empty (NLogical SOr)) =
    paper_ZF_pair_lambda (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source Encoding.coded_target
      (paper_ZF_rep_domain (type_representation Prop)) M
      (\<lambda>i p. paper_ZF_pair_lambda (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source Encoding.coded_target
        (paper_ZF_rep_domain (type_representation Prop)) (Encoding.coded_target i)
        (\<lambda>j q. union (paper_ZF_rep_transport (type_representation Prop) j p) q))"
  proof (rule paper_ZF_R_binary_logical_graph[
      where \<sigma>=Prop and l=SOr and result="\<lambda>N p q. union p q",
      OF bounded fregean functional pr paper_logical_type.simps(3) object])
    fix N x y
    assume no: "N \<in> objects" and xm: "x \<in> paper_bbk_domain N Prop" and ym: "y \<in> paper_bbk_domain N Prop"
    show "proposition_code N (paper_R_binary_logical_application signature stock (paper_bbk_domain N)
        (paper_bbk_denote N) Prop SOr x y) = union (paper_ZF_rep_encode (type_representation Prop) N x)
          (paper_ZF_rep_encode (type_representation Prop) N y)"
      using paper_ZF_R_disjunction_profile_code[OF no xm ym]
      by (simp only: paper_ZF_R_Prop_fields(3))
  qed
  show ?thesis by (simp only: paper_ZF_logical_value.simps; rule graph)
qed

theorem paper_ZF_R_Or_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and object: "M \<in> objects" and typed: "named_env_typed (paper_bbk_domain M) stock g"
  shows "paper_ZF_rep_encode (type_representation (Arr Prop (Arr Prop Prop))) M (paper_bbk_denote M g (NLogical SOr)) =
    paper_ZF_logical_value (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) M SOr"
proof -
  interpret Model: paper_R_bbk_model signature stock "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF R_category object]])
  have lr: "paper_R_type (paper_logical_type SOr)" by simp
  show ?thesis by (simp only: Model.paper_R_logical_denote_empty[OF lr typed];
    rule paper_ZF_R_Or_empty_correspondence[OF bounded fregean functional object])
qed

corollary paper_ZF_R_eval_Or:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and arrow: "h \<in> Encoding.coded_arrows"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
  shows "paper_ZF_R_constructed_eval Root (NLogical SOr) h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation (Arr Prop (Arr Prop Prop))) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g (NLogical SOr)))"
  by (simp only: paper_ZF_action_eval.simps
    paper_ZF_R_Or_correspondence[OF bounded fregean functional paper_ZF_R_eval_target_object[OF arrow] typed])

end

end
