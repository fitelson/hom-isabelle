theory Bacon_Source_ZF_R_Quantifier_Correspondence
  imports Bacon_Source_ZF_R_Quantifier_Profile_Code Bacon_Source_ZF_R_Negation_Correspondence
begin

section \<open>The outer quantifier graph decodes only its predicate child\<close>

context paper_ZF_R_type_encoding
begin

lemma paper_ZF_R_quantifier_body_value:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type \<sigma>" and object: "M \<in> objects"
    and pair: "Elem (Opair i F) (paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target
      (paper_ZF_rep_domain (type_representation (Arr \<sigma> Prop))) M)"
  shows "paper_ZF_R_arrow_body signature stock ArrowBound encode arrows (Arr \<sigma> Prop) Prop
      (type_representation (Arr \<sigma> Prop)) (type_representation Prop) M
      (paper_bbk_denote M Map.empty (NLogical (if universal then SAll \<sigma> else SEx \<sigma>))) (i,F) =
    Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source (Encoding.coded_target i))
      (\<lambda>j. if universal then \<forall>a\<in>explode (paper_ZF_rep_domain (type_representation \<sigma>) (Encoding.coded_target j)).
          Elem (Encoding.coded_identity (Encoding.coded_target j)) (app F (Opair j a))
        else \<exists>a\<in>explode (paper_ZF_rep_domain (type_representation \<sigma>) (Encoding.coded_target j)).
          Elem (Encoding.coded_identity (Encoding.coded_target j)) (app F (Opair j a)))"
proof -
  let ?N = "Encoding.coded_target i"
  let ?X = "type_representation (Arr \<sigma> Prop)"
  let ?d = "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N (Arr \<sigma> Prop)) ?X ?N F"
  let ?l = "if universal then SAll \<sigma> else SEx \<sigma>"
  have arrow: "i \<in> Encoding.coded_arrows" and source: "Encoding.coded_source i = M"
    and fm: "F \<in> explode (paper_ZF_rep_domain ?X ?N)"
    using pair by (auto simp only: paper_ZF_pair_code_member)
  have no: "?N \<in> objects" by (rule paper_ZF_R_eval_target_object[OF arrow])
  have pr: "paper_R_type (Arr \<sigma> Prop)" using rt by simp
  have qr: "paper_R_type (paper_logical_type ?l)" using rt by (cases universal; simp)
  have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound (Arr \<sigma> Prop) ?X"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional pr])
  have dm: "?d \<in> paper_bbk_domain ?N (Arr \<sigma> Prop)"
    by (rule paper_ZF_R_type_invariant_decode_type[OF invariant no fm])
  have encoded: "paper_ZF_rep_encode ?X ?N ?d = F"
    by (rule paper_ZF_R_type_invariant_encode_decode[OF invariant no fm])
  have moved: "paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr (Arr \<sigma> Prop) Prop)) i
      (paper_bbk_denote M Map.empty (NLogical ?l)) = paper_bbk_denote ?N Map.empty (NLogical ?l)"
    using paper_ZF_R_logical_transport_empty[OF arrow source qr] by (cases universal; simp)
  show ?thesis
    by (simp only: paper_ZF_R_arrow_body_on[OF pair] moved paper_ZF_R_Prop_fields(3)
      paper_ZF_R_quantifier_profile_code[OF bounded fregean functional rt no dm] encoded)
qed

section \<open>Full higher-type ∀ and ∃ graph correspondence\<close>

text \<open>
  Both graphs have the full actual pair domain (i,F), where F belongs
  to the represented predicate fiber at target(i). The child σ→t
  bijection provides its original predicate d. Inside the resulting
  proposition, the independent σ bijection covers every target value.
  No arrow is required to be surjective, and no logical-stock membership,
  evaluator clause, or action-model totality premise is used.
  Source: Definition 3.19, p.56, and Proposition 3.22, p.72.
\<close>

theorem paper_ZF_R_quantifier_empty_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type \<sigma>" and object: "M \<in> objects"
  shows "paper_ZF_rep_encode (type_representation (Arr (Arr \<sigma> Prop) Prop)) M
      (paper_bbk_denote M Map.empty (NLogical (if universal then SAll \<sigma> else SEx \<sigma>))) =
    paper_ZF_logical_value (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) M
      (if universal then SAll \<sigma> else SEx \<sigma>)"
proof -
  let ?X = "type_representation (Arr \<sigma> Prop)"
  let ?Y = "type_representation Prop"
  let ?l = "if universal then SAll \<sigma> else SEx \<sigma>"
  let ?d = "paper_bbk_denote M Map.empty (NLogical ?l)"
  let ?P = "paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode arrows)
    Encoding.coded_source Encoding.coded_target (paper_ZF_rep_domain ?X) M"
  let ?b = "paper_ZF_R_arrow_body signature stock ArrowBound encode arrows (Arr \<sigma> Prop) Prop ?X ?Y M ?d"
  let ?c = "\<lambda>z. Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows)
    Encoding.coded_source (Encoding.coded_target (Fst z)))
      (\<lambda>j. if universal then \<forall>a\<in>explode (paper_ZF_rep_domain (type_representation \<sigma>) (Encoding.coded_target j)).
          Elem (Encoding.coded_identity (Encoding.coded_target j)) (app (Snd z) (Opair j a))
        else \<exists>a\<in>explode (paper_ZF_rep_domain (type_representation \<sigma>) (Encoding.coded_target j)).
          Elem (Encoding.coded_identity (Encoding.coded_target j)) (app (Snd z) (Opair j a)))"
  have ar: "paper_R_type (Arr (Arr \<sigma> Prop) Prop)" using rt by simp
  have left_graph: "paper_ZF_rep_encode (type_representation (Arr (Arr \<sigma> Prop) Prop)) M ?d =
      Lambda ?P (\<lambda>z. if Elem z ?P then ?b (Fst z,Snd z) else undefined)"
    by (simp only: paper_ZF_R_type_representation_arrow[OF ar] paper_ZF_R_arrow_representation_def
      paper_ZF_type_representation.select_convs paper_ZF_R_arrow_encode_def paper_ZF_encode_exponential_graph)
  have graphs: "Lambda ?P (\<lambda>z. if Elem z ?P then ?b (Fst z,Snd z) else undefined) = Lambda ?P ?c"
  proof (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
    fix z
    assume member: "Elem z ?P"
    obtain i F where shape: "z = Opair i F"
      by (rule paper_ZF_pair_codeE[OF member]; rule that; assumption)
    have pair: "Elem (Opair i F) ?P" using member by (simp only: shape)
    have body: "?b (i,F) = ?c (Opair i F)"
      using paper_ZF_R_quantifier_body_value[OF bounded fregean functional rt object pair]
      by (simp only: Fst Snd)
    show "(if Elem z ?P then ?b (Fst z,Snd z) else undefined) = ?c z"
      by (simp only: shape if_P[OF pair] Fst Snd body)
  qed
  show ?thesis
    by (simp only: left_graph graphs; cases universal; simp only: if_True if_False
      paper_ZF_logical_value.simps paper_ZF_pair_lambda_def)
qed

theorem paper_ZF_R_quantifier_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type \<sigma>" and object: "M \<in> objects"
    and typed: "named_env_typed (paper_bbk_domain M) stock g"
  shows "paper_ZF_rep_encode (type_representation (Arr (Arr \<sigma> Prop) Prop)) M
      (paper_bbk_denote M g (NLogical (if universal then SAll \<sigma> else SEx \<sigma>))) =
    paper_ZF_logical_value (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) M
      (if universal then SAll \<sigma> else SEx \<sigma>)"
proof -
  interpret Model: paper_R_bbk_model signature stock "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF R_category object]])
  have qr: "paper_R_type (paper_logical_type (if universal then SAll \<sigma> else SEx \<sigma>))"
    using rt by (cases universal; simp)
  show ?thesis by (simp only: Model.paper_R_logical_denote_empty[OF qr typed];
    rule paper_ZF_R_quantifier_empty_correspondence[OF bounded fregean functional rt object])
qed

corollary paper_ZF_R_eval_quantifier:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type \<sigma>" and arrow: "h \<in> Encoding.coded_arrows"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
  shows "paper_ZF_R_constructed_eval Root (NLogical (if universal then SAll \<sigma> else SEx \<sigma>)) h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation (Arr (Arr \<sigma> Prop) Prop)) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g (NLogical (if universal then SAll \<sigma> else SEx \<sigma>))))"
  by (simp only: paper_ZF_action_eval.simps
    paper_ZF_R_quantifier_correspondence[OF bounded fregean functional rt paper_ZF_R_eval_target_object[OF arrow] typed])

end

end
