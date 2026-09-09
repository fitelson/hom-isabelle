theory Bacon_Source_ZF_R_Eval_Lambda_Correspondence
  imports Bacon_Source_ZF_R_Lambda_Graph
begin

section \<open>The abstraction step of the independent evaluator correspondence\<close>

text \<open>
  At h:Root→M, the interpreted λn.B is the actual graph on all
  outgoing pairs (i,z). Each z has an old preimage at target(i), and
  the body assignment is the encoding of the old transported assignment
  updated with that preimage. A uniform induction hypothesis for B
  therefore proves every body value exists. Those values coincide with
  the applications of fσ→τM(⟦λn.B⟧ᵍM), so equality of Lambda
  graphs finishes the step. Source: Definition 3.19, p.56, and
  Proposition 3.22's term induction, p.72.

  Only the STRICT BODY correspondence is assumed below, uniformly
  over root arrows and old typed adequate partial assignments. There
  is no whole-abstraction correspondence, lambda-stock membership,
  action-model predicate, interpretation totality or distinct-binder
  premise. No claim of the complete term induction is made here.
\<close>

context paper_ZF_R_type_encoding
begin

theorem paper_ZF_R_eval_Lam:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and body: "paper_R_in_language signature stock B \<tau>"
    and binder_type: "paper_R_type (stock n)" and codomain: "\<tau> \<noteq> Ind"
    and arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = Root"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
    and adequate: "named_adequate g (NLam n B)"
    and body_IH: "\<And>j k. j \<in> Encoding.coded_arrows \<Longrightarrow> Encoding.coded_source j = Root \<Longrightarrow>
      named_env_typed (paper_bbk_domain (Encoding.coded_target j)) stock k \<Longrightarrow> named_adequate k B \<Longrightarrow>
      paper_ZF_R_constructed_eval Root B j
        (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target j) k) =
      Some (paper_ZF_rep_encode (type_representation \<tau>) (Encoding.coded_target j)
        (paper_bbk_denote (Encoding.coded_target j) k B))"
  shows "paper_ZF_R_constructed_eval Root (NLam n B) h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation (Arr (stock n) \<tau>)) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g (NLam n B)))"
proof -
  interpret Coded: paper_category objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity by (rule Encoding.paper_ZF_encoded_category)
  let ?M = "Encoding.coded_target h"
  let ?g = "paper_ZF_R_encode_assignment stock type_representation ?M g"
  let ?T = "\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)"
  let ?P = "paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode arrows)
    Encoding.coded_source Encoding.coded_target (paper_ZF_rep_domain (type_representation (stock n))) ?M"
  let ?V = "paper_ZF_action_abstraction_body Encoding.coded_compose ?T stock n
    (paper_ZF_R_constructed_eval Root B) h ?g"
  let ?F = "paper_ZF_rep_encode (type_representation (Arr (stock n) \<tau>)) ?M (paper_bbk_denote ?M g (NLam n B))"
  have abstraction: "paper_R_in_language signature stock (NLam n B) (Arr (stock n) \<tau>)"
    by (rule paper_R_abstraction_language[OF body binder_type codomain])
  have rt: "paper_R_type (Arr (stock n) \<tau>)" by (rule paper_R_language_result_type[OF abstraction])
  have points: "?V z = Some (app ?F z)" if member: "Elem z ?P" for z
  proof -
    obtain i a where ia: "i \<in> Encoding.coded_arrows" and origin: "Encoding.coded_source i = ?M"
      and am: "a \<in> explode (paper_ZF_rep_domain (type_representation (stock n)) (Encoding.coded_target i))"
      and shape: "z = Opair i a"
      by (rule paper_ZF_pair_codeE[OF member])
    have meeting: "Encoding.coded_target h = Encoding.coded_source i" by (rule origin[symmetric])
    have composite: "Encoding.coded_compose i h \<in> Encoding.coded_arrows"
      by (rule Coded.compose_arrow[OF arrow ia meeting])
    have cs: "Encoding.coded_source (Encoding.coded_compose i h) = Root"
      by (simp only: Coded.compose_source[OF arrow ia meeting] source)
    have ct: "Encoding.coded_target (Encoding.coded_compose i h) = Encoding.coded_target i"
      by (rule Coded.compose_target[OF arrow ia meeting])
    have old_typed: "named_env_typed (paper_bbk_domain (Encoding.coded_source i)) stock g"
      by (simp only: origin; rule typed)
    let ?a = "paper_ZF_rep_inverse (\<lambda>M. paper_bbk_domain M (stock n))
      (type_representation (stock n)) (Encoding.coded_target i) a"
    let ?k = "(paper_hom_assignment stock (paper_arrow_map (Encoding.decode_arrow i)) g)(n := Some ?a)"
    have old_input: "named_env_typed (paper_bbk_domain (Encoding.coded_target i)) stock ?k \<and> named_adequate ?k B"
      by (rule paper_ZF_R_lambda_old_input[OF bounded fregean functional ia old_typed adequate am])
    have kt: "named_env_typed (paper_bbk_domain (Encoding.coded_target (Encoding.coded_compose i h))) stock ?k"
      by (simp only: ct; rule conjunct1[OF old_input])
    have ka: "named_adequate ?k B" by (rule conjunct2[OF old_input])
    have evaluated_body: "paper_ZF_R_constructed_eval Root B (Encoding.coded_compose i h)
        (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target (Encoding.coded_compose i h)) ?k) =
      Some (paper_ZF_rep_encode (type_representation \<tau>) (Encoding.coded_target (Encoding.coded_compose i h))
        (paper_bbk_denote (Encoding.coded_target (Encoding.coded_compose i h)) ?k B))"
      by (rule body_IH[OF composite cs kt ka])
    have input_eq: "(paper_ZF_action_transport_assignment stock ?T i ?g)(n := Some a) =
      paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target i) ?k"
      using paper_ZF_R_lambda_input_assignment[OF bounded fregean functional ia old_typed am]
      by (simp only: origin)
    have body_some: "?V z = Some (paper_ZF_rep_encode (type_representation \<tau>) (Encoding.coded_target i)
        (paper_bbk_denote (Encoding.coded_target i) ?k B))"
      using evaluated_body by (simp only: shape paper_ZF_action_abstraction_body_pair input_eq ct)
    have graph_value: "app ?F (Opair i a) = paper_ZF_rep_encode (type_representation \<tau>) (Encoding.coded_target i)
        (paper_bbk_denote (Encoding.coded_target i) ?k B)"
      using paper_ZF_R_lambda_graph_value[OF bounded fregean functional body binder_type codomain ia old_typed adequate am]
      by (simp only: origin)
    show "?V z = Some (app ?F z)" using body_some by (simp only: shape graph_value)
  qed
  have defined: "?V z \<noteq> None" if member: "z \<in> explode ?P" for z
  proof -
    have coded: "Elem z ?P" using member by (simp only: explode_Elem)
    show ?thesis by (simp only: points[OF coded]; simp)
  qed
  have evaluated: "paper_ZF_R_constructed_eval Root (NLam n B) h ?g = Some (Lambda ?P (\<lambda>z. the (?V z)))"
    by (simp only: paper_ZF_action_eval.simps; rule paper_ZF_action_abstract_defined; rule defined; assumption)
  obtain b where graph: "?F = Lambda ?P b"
    using paper_ZF_R_encoded_arrow_Lambda[where M="?M" and d="paper_bbk_denote ?M g (NLam n B)", OF rt]
    by (elim exE)
  have graph_eq: "Lambda ?P (\<lambda>z. the (?V z)) = ?F"
  proof (rule paper_ZF_Lambda_from_app[OF graph])
    fix z
    assume member: "Elem z ?P"
    show "the (?V z) = app ?F z" by (simp only: points[OF member]; simp)
  qed
  show ?thesis by (simp only: evaluated graph_eq)
qed

end

end
