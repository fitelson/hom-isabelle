theory Bacon_Source_ZF_R_Constructed_Model
  imports Bacon_Source_ZF_R_Eval_Correspondence Bacon_Source_ZF_Action_Model
    Bacon_Source_ZF_R_Action_Assignments
begin

section \<open>Evaluation at every new adequate partial assignment\<close>

context paper_ZF_R_type_encoding
begin

lemma paper_ZF_R_eval_decoded:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
    and language: "paper_R_in_language signature stock A \<rho>"
    and arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = Root"
    and typed: "paper_ZF_action_env_typed (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      stock (Encoding.coded_target h) g"
    and adequate: "named_adequate g A"
  shows "paper_ZF_R_constructed_eval Root A h g =
    Some (paper_ZF_rep_encode (type_representation \<rho>) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h)
        (paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation (Encoding.coded_target h) g) A))"
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
  show ?thesis
    using paper_ZF_R_eval_correspondence[OF bounded fregean functional rooted language arrow source old_typed old_adequate]
    by (simp only: inverse)
qed

lemma paper_ZF_R_eval_total_typed:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
    and language: "paper_R_in_language signature stock A \<rho>"
    and arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = Root"
    and typed: "paper_ZF_action_env_typed (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      stock (Encoding.coded_target h) g"
    and adequate: "named_adequate g A"
  shows "\<exists>v. paper_ZF_R_constructed_eval Root A h g = Some v \<and>
    v \<in> explode (paper_ZF_rep_domain (type_representation \<rho>) (Encoding.coded_target h))"
proof -
  let ?M = "Encoding.coded_target h"
  let ?k = "paper_ZF_R_decode_assignment stock paper_bbk_domain type_representation ?M g"
  let ?v = "paper_bbk_denote ?M ?k A"
  have object: "?M \<in> objects" by (rule paper_ZF_R_eval_target_object[OF arrow])
  have valid: "paper_R_bbk_data_valid signature stock ?M"
    by (rule paper_R_bbk_subcategory_models[OF R_category object])
  have nt: "named_env_typed (\<lambda>\<rho>. explode (paper_ZF_rep_domain (type_representation \<rho>) ?M)) stock g"
    by (rule paper_ZF_action_env_named[OF typed])
  have old_typed: "named_env_typed (paper_bbk_domain ?M) stock ?k"
    by (rule paper_ZF_R_decode_assignment_typed[OF bounded fregean functional object nt])
  have old_adequate: "named_adequate ?k A"
    by (simp only: paper_ZF_R_decode_assignment_adequate_iff; rule adequate)
  have old_value: "?v \<in> paper_bbk_domain ?M \<rho>"
    by (rule paper_R_bbk_data_denote_type[OF valid language old_typed old_adequate])
  have rt: "paper_R_type \<rho>" by (rule paper_R_language_result_type[OF language])
  have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<rho> (type_representation \<rho>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
  have new_value: "paper_ZF_rep_encode (type_representation \<rho>) ?M ?v \<in>
      explode (paper_ZF_rep_domain (type_representation \<rho>) ?M)"
    by (rule paper_ZF_R_type_invariant_encode_type[OF invariant object old_value])
  have evaluated: "paper_ZF_R_constructed_eval Root A h g = Some (paper_ZF_rep_encode (type_representation \<rho>) ?M ?v)"
    by (rule paper_ZF_R_eval_decoded[OF bounded fregean functional rooted language arrow source typed adequate])
  show ?thesis by (rule exI; rule conjI[OF evaluated new_value])
qed

section \<open>The recursive construction is an actual action model\<close>

text \<open>
  This discharges the independent Definition 3.20 predicate, not merely
  its premodel clauses. Each adequate partial assignment is decoded,
  the structural evaluator correspondence is applied, and the exact
  assignment round trip returns the original input. This covers every
  root arrow, not a chosen arrow or a unique-root convention.

  The original selected category consists of independent R models whose
  values are ZF sets. Arrow coding and the individual bound remain
  explicit. No arbitrary-HOL representability, action-model totality,
  or logical-stock membership premise is added.
\<close>

theorem paper_ZF_R_constructed_model:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
  shows "paper_ZF_action_model signature stock objects (paper_ZF_image_code ArrowBound encode arrows)
    Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity Root
    (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
    (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) (paper_ZF_R_root_constant Root)"
proof (unfold paper_ZF_action_model_def, intro conjI)
  have object: "Root \<in> objects" by (rule paper_rooted_category.root_object[OF rooted])
  show "paper_R_rich stock"
    by (rule paper_R_bbk_data_stock_rich[OF paper_R_bbk_subcategory_models[OF R_category object]])
next
  show "paper_ZF_action_premodel signature objects (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity Root
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) (paper_ZF_R_root_constant Root)"
    by (rule paper_ZF_R_constructed_premodel[OF bounded fregean functional rooted])
next
  show "\<forall>A \<rho> h g. paper_R_in_language signature stock A \<rho> \<longrightarrow>
      h \<in> Encoding.coded_arrows \<longrightarrow> Encoding.coded_source h = Root \<longrightarrow>
      paper_ZF_action_env_typed (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>)) stock (Encoding.coded_target h) g \<longrightarrow>
      named_adequate g A \<longrightarrow>
      (\<exists>v. paper_ZF_R_constructed_eval Root A h g = Some v \<and>
        v \<in> explode (paper_ZF_rep_domain (type_representation \<rho>) (Encoding.coded_target h)))"
    by (intro allI impI; rule paper_ZF_R_eval_total_typed[OF bounded fregean functional rooted]; assumption)
qed

corollary paper_ZF_R_intensional_constructed_model:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and intensional: "paper_R_intensional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
  shows "paper_ZF_action_model signature stock objects (paper_ZF_image_code ArrowBound encode arrows)
    Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity Root
    (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
    (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) (paper_ZF_R_root_constant Root)"
proof -
  have conditions: "paper_bbk_quasi_fregean_on objects arrows \<and>
      paper_R_quasi_functional_on signature stock objects arrows"
    by (rule paper_R_intensional_implies_quasi_conditions[OF intensional])
  show ?thesis by (rule paper_ZF_R_constructed_model[
    OF bounded conjunct1[OF conditions] conjunct2[OF conditions] rooted])
qed

end

end
