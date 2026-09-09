theory Bacon_Source_ZF_R_Root_Truth_Correspondence
  imports Bacon_Source_ZF_R_Constructed_Model Bacon_Source_ZF_R_Proposition_Identity_Truth
begin

section \<open>Truth at corresponding adequate partial assignments\<close>

context paper_ZF_R_type_encoding
begin

abbreviation paper_ZF_R_constructed_holds where
  "paper_ZF_R_constructed_holds Root \<equiv>
    paper_ZF_action_holds (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) (paper_ZF_R_root_constant Root) stock"

lemma paper_ZF_R_holds_encoded:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
    and language: "paper_R_in_language signature stock A Prop"
    and arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = Root"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
    and adequate: "named_adequate g A"
  shows "paper_ZF_R_constructed_holds Root h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) A =
    paper_bbk_valuation (Encoding.coded_target h) (paper_bbk_denote (Encoding.coded_target h) g A)"
proof -
  let ?M = "Encoding.coded_target h"
  let ?p = "paper_bbk_denote ?M g A"
  have object: "?M \<in> objects" by (rule paper_ZF_R_eval_target_object[OF arrow])
  have member: "?p \<in> paper_bbk_domain ?M Prop"
    by (rule paper_R_bbk_data_denote_type[OF paper_R_bbk_subcategory_models[OF R_category object] language typed adequate])
  have evaluated: "paper_ZF_R_constructed_eval Root A h
      (paper_ZF_R_encode_assignment stock type_representation ?M g) = Some (proposition_code ?M ?p)"
    using paper_ZF_R_eval_correspondence[OF bounded fregean functional rooted language arrow source typed adequate]
    by (simp only: paper_ZF_R_Prop_fields(3))
  show ?thesis
    by (simp only: paper_ZF_action_holds_def evaluated option.inject;
      simp add: paper_ZF_R_proposition_identity_truth[OF object member])
qed

lemma paper_ZF_R_holds_decoded:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
    and language: "paper_R_in_language signature stock A Prop"
    and arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = Root"
    and typed: "paper_ZF_action_env_typed (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      stock (Encoding.coded_target h) g"
    and adequate: "named_adequate g A"
  shows "paper_ZF_R_constructed_holds Root h g A =
    paper_bbk_valuation (Encoding.coded_target h) (paper_bbk_denote (Encoding.coded_target h)
      (paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation (Encoding.coded_target h) g) A)"
proof -
  let ?M = "Encoding.coded_target h"
  let ?k = "paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation ?M g"
  have object: "?M \<in> objects" by (rule paper_ZF_R_eval_target_object[OF arrow])
  have nt: "named_env_typed (\<lambda>\<rho>. explode (paper_ZF_rep_domain (type_representation \<rho>) ?M)) stock g"
    by (rule paper_ZF_action_env_named[OF typed])
  have old_typed: "named_env_typed (paper_bbk_domain ?M) stock ?k"
    by (rule paper_ZF_R_decode_assignment_typed[OF bounded fregean functional object nt])
  have old_adequate: "named_adequate ?k A"
    by (simp only: paper_ZF_R_decode_assignment_adequate_iff; rule adequate)
  have inverse: "paper_ZF_R_encode_assignment stock type_representation ?M ?k = g"
    by (rule paper_ZF_R_encode_decode_assignment[OF bounded fregean functional object nt])
  show ?thesis using paper_ZF_R_holds_encoded[OF bounded fregean functional rooted language arrow source old_typed old_adequate]
    by (simp only: inverse)
qed

section \<open>All-assignment truth, including open formulas\<close>

text \<open>
  The quantified assignments on both sides may be partial and have
  different domains; only adequacy for A is required. The forward and
  inverse assignment maps preserve those domains exactly. No completion
  or uniform finite bound on the free variables is introduced.
  At the root this is the truth comparison used in Proposition 3.22.
\<close>

theorem paper_ZF_R_arrow_validity_iff:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
    and language: "paper_R_in_language signature stock A Prop"
    and arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = Root"
  shows "(\<forall>g. paper_ZF_action_env_typed (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      stock (Encoding.coded_target h) g \<longrightarrow> named_adequate g A \<longrightarrow>
        paper_ZF_R_constructed_holds Root h g A) =
    (\<forall>g. named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g \<longrightarrow>
      named_adequate g A \<longrightarrow> paper_bbk_valuation (Encoding.coded_target h)
        (paper_bbk_denote (Encoding.coded_target h) g A))"
proof -
  let ?M = "Encoding.coded_target h"
  let ?D = "\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>)"
  have object: "?M \<in> objects" by (rule paper_ZF_R_eval_target_object[OF arrow])
  show ?thesis
  proof (rule iffI)
    assume truth: "\<forall>g. paper_ZF_action_env_typed ?D stock ?M g \<longrightarrow> named_adequate g A \<longrightarrow>
      paper_ZF_R_constructed_holds Root h g A"
    show "\<forall>g. named_env_typed (paper_bbk_domain ?M) stock g \<longrightarrow> named_adequate g A \<longrightarrow>
      paper_bbk_valuation ?M (paper_bbk_denote ?M g A)"
    proof (intro allI impI)
      fix g
      assume typed: "named_env_typed (paper_bbk_domain ?M) stock g" and adequate: "named_adequate g A"
      let ?k = "paper_ZF_R_encode_assignment stock type_representation ?M g"
      have kt: "paper_ZF_action_env_typed ?D stock ?M ?k"
        by (rule paper_ZF_R_representation_env_supported;
          rule paper_ZF_R_encode_assignment_typed[OF bounded fregean functional object typed])
      have ka: "named_adequate ?k A"
        by (simp only: paper_ZF_R_encode_assignment_adequate_iff; rule adequate)
      have holds: "paper_ZF_R_constructed_holds Root h ?k A" using truth kt ka by blast
      show "paper_bbk_valuation ?M (paper_bbk_denote ?M g A)"
        using holds by (simp only: paper_ZF_R_holds_encoded[OF bounded fregean functional rooted language arrow source typed adequate])
    qed
  next
    assume truth: "\<forall>g. named_env_typed (paper_bbk_domain ?M) stock g \<longrightarrow> named_adequate g A \<longrightarrow>
      paper_bbk_valuation ?M (paper_bbk_denote ?M g A)"
    show "\<forall>g. paper_ZF_action_env_typed ?D stock ?M g \<longrightarrow> named_adequate g A \<longrightarrow>
      paper_ZF_R_constructed_holds Root h g A"
    proof (intro allI impI)
      fix g
      assume typed: "paper_ZF_action_env_typed ?D stock ?M g" and adequate: "named_adequate g A"
      let ?k = "paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation ?M g"
      have nt: "named_env_typed (\<lambda>\<rho>. explode (?D \<rho> ?M)) stock g"
        by (rule paper_ZF_action_env_named[OF typed])
      have kt: "named_env_typed (paper_bbk_domain ?M) stock ?k"
        by (rule paper_ZF_R_decode_assignment_typed[OF bounded fregean functional object nt])
      have ka: "named_adequate ?k A"
        by (simp only: paper_ZF_R_decode_assignment_adequate_iff; rule adequate)
      have old_truth: "paper_bbk_valuation ?M (paper_bbk_denote ?M ?k A)" using truth kt ka by blast
      show "paper_ZF_R_constructed_holds Root h g A"
        by (simp only: paper_ZF_R_holds_decoded[OF bounded fregean functional rooted language arrow source typed adequate]; rule old_truth)
    qed
  qed
qed

corollary paper_ZF_R_root_validity_iff:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
    and language: "paper_R_in_language signature stock A Prop"
  shows "(\<forall>g. paper_ZF_action_env_typed (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>)) stock Root g \<longrightarrow>
      named_adequate g A \<longrightarrow> paper_ZF_R_constructed_holds Root (Encoding.coded_identity Root) g A) =
    (\<forall>g. named_env_typed (paper_bbk_domain Root) stock g \<longrightarrow> named_adequate g A \<longrightarrow>
      paper_bbk_valuation Root (paper_bbk_denote Root g A))"
proof -
  interpret Coded: paper_category objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity by (rule Encoding.paper_ZF_encoded_category)
  have object: "Root \<in> objects" by (rule paper_rooted_category.root_object[OF rooted])
  have arrow: "Encoding.coded_identity Root \<in> Encoding.coded_arrows" by (rule Coded.identity_arrow[OF object])
  have source: "Encoding.coded_source (Encoding.coded_identity Root) = Root" by (rule Coded.identity_source[OF object])
  have target: "Encoding.coded_target (Encoding.coded_identity Root) = Root" by (rule Coded.identity_target[OF object])
  show ?thesis using paper_ZF_R_arrow_validity_iff[OF bounded fregean functional rooted language arrow source]
    by (simp only: target)
qed

end

end
