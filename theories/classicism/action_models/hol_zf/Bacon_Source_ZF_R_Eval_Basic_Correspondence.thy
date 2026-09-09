theory Bacon_Source_ZF_R_Eval_Basic_Correspondence
  imports Bacon_Source_ZF_Partial_Interpretation Bacon_Source_ZF_Premodel_Application
    Bacon_Source_ZF_R_Constructed_Premodel Bacon_Source_ZF_R_Canonical_Application
    Bacon_Source_ZF_R_Representation_Assignments
begin

section \<open>Basic cases for the independent evaluator on the constructed data\<close>

text \<open>
  The evaluator below is an abbreviation for the independently defined
  Definition 3.19 recursion, instantiated with the constructed category,
  domains, transports and root constants. It is NOT defined through
  the original BBK denotation. We prove its variable and declared-constant
  cases, and the application induction step, toward the correspondence
  in Proposition 3.22, p.72.

  All statements use encoded old typed adequate partial assignments.
  Root arrows are arbitrary, not selected or assumed unique.
  Application uses the constructed premodel's actual graph definedness.
  No action-model predicate or interpretation-totality assumption appears.
  Logical constants and abstraction remain separate proof cases.
\<close>

context paper_ZF_R_type_encoding
begin

abbreviation paper_ZF_R_constructed_eval ::
  "('c,ZF) paper_bbk_model_data \<Rightarrow> 'c paper_named_term \<Rightarrow> ZF \<Rightarrow> ZF named_assignment \<Rightarrow> ZF option" where
  "paper_ZF_R_constructed_eval Root \<equiv>
    paper_ZF_action_eval (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) (paper_ZF_R_root_constant Root) stock"

lemma paper_ZF_R_eval_target_object:
  assumes arrow: "h \<in> Encoding.coded_arrows"
  shows "Encoding.coded_target h \<in> objects"
  by (simp only: paper_ZF_recode_target_def;
    rule Encoding.target_object[OF Encoding.paper_ZF_decode_arrow_type[OF arrow]])

theorem paper_ZF_R_eval_Var:
  assumes arrow: "h \<in> Encoding.coded_arrows"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
    and adequate: "named_adequate g (NVar n :: 'c paper_named_term)"
  shows "paper_ZF_R_constructed_eval Root (NVar n) h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation (stock n)) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g (NVar n)))"
proof -
  have object: "Encoding.coded_target h \<in> objects" by (rule paper_ZF_R_eval_target_object[OF arrow])
  interpret Model: paper_R_bbk_model signature stock "paper_bbk_domain (Encoding.coded_target h)"
    "paper_bbk_denote (Encoding.coded_target h)" "paper_bbk_valuation (Encoding.coded_target h)"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF R_category object]])
  have free: "n \<in> named_fv (NVar n :: 'c paper_named_term)" by simp
  obtain a where assigned: "g n = Some a" by (rule named_adequate_value[OF adequate free])
  have original: "paper_bbk_denote (Encoding.coded_target h) g (NVar n) = a"
    by (rule Model.denote_var[OF typed assigned])
  show ?thesis by (simp only: paper_ZF_action_eval.simps paper_ZF_R_encode_assignment_apply assigned option.map original)
qed

theorem paper_ZF_R_eval_Const:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and root: "Root \<in> objects" and declared: "c \<in> signature \<rho>" and rt: "paper_R_type \<rho>"
    and arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = Root"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
  shows "paper_ZF_R_constructed_eval Root (NConst c \<rho>) h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation \<rho>) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g (NConst c \<rho>)))"
proof -
  have object: "Encoding.coded_target h \<in> objects" by (rule paper_ZF_R_eval_target_object[OF arrow])
  have constant_value: "paper_bbk_denote (Encoding.coded_target h) g (NConst c \<rho>) =
    paper_bbk_denote (Encoding.coded_target h) Map.empty (NConst c \<rho>)"
    by (rule paper_ZF_R_original_constant_denote_empty[OF object declared rt typed])
  show ?thesis
    by (simp only: paper_ZF_action_eval.simps
      paper_ZF_R_root_constant_transport[OF bounded fregean functional root declared rt arrow source] constant_value)
qed

section \<open>The application step uses only the two stated induction hypotheses\<close>

theorem paper_ZF_R_eval_App:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rooted: "paper_rooted_category objects arrows paper_arrow_source paper_arrow_target
      (paper_typed_compose paper_bbk_domain) (paper_typed_identity paper_bbk_domain) Root"
    and arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = Root"
    and fl: "paper_R_in_language signature stock F (Arr \<sigma> \<tau>)"
    and bl: "paper_R_in_language signature stock B \<sigma>"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
    and adequate: "named_adequate g (NApp F B)"
    and head_IH: "paper_ZF_R_constructed_eval Root F h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
      Some (paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) (Encoding.coded_target h)
        (paper_bbk_denote (Encoding.coded_target h) g F))"
    and argument_IH: "paper_ZF_R_constructed_eval Root B h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
      Some (paper_ZF_rep_encode (type_representation \<sigma>) (Encoding.coded_target h)
        (paper_bbk_denote (Encoding.coded_target h) g B))"
  shows "paper_ZF_R_constructed_eval Root (NApp F B) h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation \<tau>) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g (NApp F B)))"
proof -
  let ?M = "Encoding.coded_target h"
  let ?d = "paper_bbk_denote ?M g F"
  let ?a = "paper_bbk_denote ?M g B"
  let ?f = "paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) ?M ?d"
  let ?b = "paper_ZF_rep_encode (type_representation \<sigma>) ?M ?a"
  have object: "?M \<in> objects" by (rule paper_ZF_R_eval_target_object[OF arrow])
  interpret Model: paper_R_bbk_model signature stock "paper_bbk_domain ?M" "paper_bbk_denote ?M" "paper_bbk_valuation ?M"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF R_category object]])
  have rt: "paper_R_type (Arr \<sigma> \<tau>)" by (rule paper_R_language_result_type[OF fl])
  have sr: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF rt])
  have fa: "named_adequate g F" and ba: "named_adequate g B" using adequate by (auto simp: named_adequate_def)
  have dm: "?d \<in> paper_bbk_domain ?M (Arr \<sigma> \<tau>)" by (rule Model.denote_type[OF fl typed fa])
  have am: "?a \<in> paper_bbk_domain ?M \<sigma>" by (rule Model.denote_type[OF bl typed ba])
  have fi: "paper_ZF_R_type_invariant objects arrows encode ArrowBound (Arr \<sigma> \<tau>) (type_representation (Arr \<sigma> \<tau>))"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
  have bi: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<sigma> (type_representation \<sigma>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional sr])
  have fm: "?f \<in> explode (paper_ZF_rep_domain (type_representation (Arr \<sigma> \<tau>)) ?M)"
    by (rule paper_ZF_R_type_invariant_encode_type[OF fi object dm])
  have bm: "?b \<in> explode (paper_ZF_rep_domain (type_representation \<sigma>) ?M)"
    by (rule paper_ZF_R_type_invariant_encode_type[OF bi object am])
  have premodel: "paper_ZF_action_premodel signature objects (paper_ZF_image_code ArrowBound encode arrows)
    Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity Root
    (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
    (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) (paper_ZF_R_root_constant Root)"
    by (rule paper_ZF_R_constructed_premodel[OF bounded fregean functional rooted])
  have graph: "isFun ?f" and pair: "Elem (Opair (Encoding.coded_identity ?M) ?b) (Domain ?f)"
    by (rule paper_ZF_premodel_application_graph[OF premodel object rt fm bm])+
  have evaluated: "paper_ZF_R_constructed_eval Root (NApp F B) h
      (paper_ZF_R_encode_assignment stock type_representation ?M g) =
    Some (app ?f (Opair (Encoding.coded_identity ?M) ?b))"
    by (rule paper_ZF_action_eval_application[OF head_IH argument_IH graph pair])
  have original: "paper_R_application signature stock (paper_bbk_domain ?M) (paper_bbk_denote ?M) \<sigma> \<tau> ?d ?a =
    paper_bbk_denote ?M g (NApp F B)"
    by (rule Model.paper_R_application_denote[OF fl bl typed adequate])
  have application: "app ?f (Opair (Encoding.coded_identity ?M) ?b) =
    paper_ZF_rep_encode (type_representation \<tau>) ?M (paper_bbk_denote ?M g (NApp F B))"
    using paper_ZF_R_application_correspondence[OF bounded fregean functional rt object dm am]
    by (simp only: paper_ZF_action_apply_def original)
  show ?thesis by (simp only: evaluated application)
qed

end

end
