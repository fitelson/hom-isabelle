theory Bacon_Source_ZF_R_Negation_Correspondence
  imports Bacon_Source_ZF_R_Negation_Profile_Code Bacon_Source_ZF_R_Eval_Basic_Correspondence
    Bacon_Source_ZF_Logical_Value_Evaluation
begin

section \<open>Logical values transport to the original target logical values\<close>

context paper_ZF_R_type_encoding
begin

lemma paper_ZF_R_logical_transport_empty:
  assumes arrow: "i \<in> Encoding.coded_arrows" and source: "Encoding.coded_source i = M"
    and rt: "paper_R_type (paper_logical_type l)"
  shows "paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (paper_logical_type l)) i
      (paper_bbk_denote M Map.empty (NLogical l)) =
    paper_bbk_denote (Encoding.coded_target i) Map.empty (NLogical l)"
proof -
  have original: "Encoding.decode_arrow i \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF arrow])
  have origin: "paper_arrow_source (Encoding.decode_arrow i) = M"
    using source by (simp only: paper_ZF_recode_source_def)
  have morphism: "paper_R_bbk_model_morphism signature stock
    (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
    (paper_bbk_domain (Encoding.coded_target i)) (paper_bbk_denote (Encoding.coded_target i))
    (paper_bbk_valuation (Encoding.coded_target i)) (paper_arrow_map (Encoding.decode_arrow i))"
    using paper_R_bbk_arrows_morphism[OF paper_R_bbk_subcategory_arrow[OF R_category original]]
    by (simp only: paper_R_bbk_data_morphism_def paper_ZF_recode_target_def origin)
  show ?thesis
    by (simp only: paper_ZF_recode_transport_def; rule paper_R_logical_morphism_empty[OF morphism rt])
qed

section \<open>Every admissible negation pair yields the literal complement\<close>

lemma paper_ZF_R_negation_body_value:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and object: "M \<in> objects"
    and pair: "Elem (Opair i p) (paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target (paper_ZF_rep_domain (type_representation Prop)) M)"
  shows "paper_ZF_R_arrow_body signature stock ArrowBound encode arrows Prop Prop
      (type_representation Prop) (type_representation Prop) M
      (paper_bbk_denote M Map.empty (NLogical SNot)) (i,p) =
    Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source (Encoding.coded_target i))
      (\<lambda>j. \<not> Elem j p)"
proof -
  let ?N = "Encoding.coded_target i"
  let ?X = "type_representation Prop"
  let ?a = "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N Prop) ?X ?N p"
  have arrow: "i \<in> Encoding.coded_arrows" and source: "Encoding.coded_source i = M"
    and pm: "p \<in> explode (paper_ZF_rep_domain ?X ?N)"
    using pair by (auto simp only: paper_ZF_pair_code_member)
  have no: "?N \<in> objects" by (rule paper_ZF_R_eval_target_object[OF arrow])
  have pr: "paper_R_type Prop" and nr: "paper_R_type (paper_logical_type SNot)" by simp_all
  have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound Prop ?X"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional pr])
  have am: "?a \<in> paper_bbk_domain ?N Prop"
    by (rule paper_ZF_R_type_invariant_decode_type[OF invariant no pm])
  have encoded: "paper_ZF_rep_encode ?X ?N ?a = p"
    by (rule paper_ZF_R_type_invariant_encode_decode[OF invariant no pm])
  have argument_code: "proposition_code ?N ?a = p" using encoded by (simp only: paper_ZF_R_Prop_fields(3))
  have moved: "paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr Prop Prop)) i
      (paper_bbk_denote M Map.empty (NLogical SNot)) =
    paper_bbk_denote ?N Map.empty (NLogical SNot)"
    using paper_ZF_R_logical_transport_empty[OF arrow source nr] by simp
  have complement: "paper_ZF_rep_encode ?X ?N
      (paper_R_application signature stock (paper_bbk_domain ?N) (paper_bbk_denote ?N)
        Prop Prop (paper_bbk_denote ?N Map.empty (NLogical SNot)) ?a) =
    Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source ?N)
      (\<lambda>j. \<not> Elem j p)"
    using paper_ZF_R_negation_profile_code[OF no am]
    by (simp only: paper_ZF_R_Prop_fields(3) argument_code)
  show ?thesis by (simp only: paper_ZF_R_arrow_body_on[OF pair] moved complement)
qed

section \<open>The encoded source negation is exactly the independent logical graph\<close>

text \<open>
  Both sides are Lambda graphs on the FULL actual outgoing-arrow/
  represented-proposition pair domain. Their equality is proved at
  each member of that domain. The represented proposition argument
  is decoded by the proved child inverse, then re-encoded exactly.
  Source: Definition 3.19, p.56, and Proposition 3.22, p.72.

  Neither membership of the literal negation graph in the selected
  stock nor its evaluator correspondence is assumed. The logical
  graph is the independently defined complement graph, not an
  old-denotation definition. Other logical families remain separate.
\<close>

theorem paper_ZF_R_Not_empty_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and object: "M \<in> objects"
  shows "paper_ZF_rep_encode (type_representation (Arr Prop Prop)) M
      (paper_bbk_denote M Map.empty (NLogical SNot)) =
    paper_ZF_logical_value (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) M SNot"
proof -
  let ?X = "type_representation Prop"
  let ?d = "paper_bbk_denote M Map.empty (NLogical SNot)"
  let ?P = "paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode arrows)
    Encoding.coded_source Encoding.coded_target (paper_ZF_rep_domain ?X) M"
  let ?b = "paper_ZF_R_arrow_body signature stock ArrowBound encode arrows Prop Prop ?X ?X M ?d"
  let ?c = "\<lambda>z. Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows)
    Encoding.coded_source (Encoding.coded_target (Fst z))) (\<lambda>j. \<not> Elem j (Snd z))"
  have rt: "paper_R_type (Arr Prop Prop)" by simp
  have left_graph: "paper_ZF_rep_encode (type_representation (Arr Prop Prop)) M ?d =
    Lambda ?P (\<lambda>z. if Elem z ?P then ?b (Fst z,Snd z) else undefined)"
    by (simp only: paper_ZF_R_type_representation_arrow[OF rt] paper_ZF_R_arrow_representation_def
      paper_ZF_type_representation.select_convs paper_ZF_R_arrow_encode_def paper_ZF_encode_exponential_graph)
  have graphs: "Lambda ?P (\<lambda>z. if Elem z ?P then ?b (Fst z,Snd z) else undefined) = Lambda ?P ?c"
  proof (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
    fix z
    assume member: "Elem z ?P"
    obtain i p where shape: "z = Opair i p"
      by (rule paper_ZF_pair_codeE[OF member]; rule that; assumption)
    have pair: "Elem (Opair i p) ?P" using member by (simp only: shape)
    have body: "?b (i,p) = Sep (paper_ZF_outgoing_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source (Encoding.coded_target i)) (\<lambda>j. \<not> Elem j p)"
      by (rule paper_ZF_R_negation_body_value[OF bounded fregean functional object pair])
    show "(if Elem z ?P then ?b (Fst z,Snd z) else undefined) = ?c z"
      by (simp only: shape if_P[OF pair] Fst Snd body)
  qed
  show ?thesis by (simp only: left_graph paper_ZF_logical_value.simps paper_ZF_pair_lambda_def; rule graphs)
qed

theorem paper_ZF_R_Not_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and object: "M \<in> objects" and typed: "named_env_typed (paper_bbk_domain M) stock g"
  shows "paper_ZF_rep_encode (type_representation (Arr Prop Prop)) M (paper_bbk_denote M g (NLogical SNot)) =
    paper_ZF_logical_value (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
      (\<lambda>\<rho>. paper_ZF_rep_domain (type_representation \<rho>))
      (\<lambda>\<rho>. paper_ZF_rep_transport (type_representation \<rho>)) M SNot"
proof -
  interpret Model: paper_R_bbk_model signature stock "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF R_category object]])
  have nr: "paper_R_type (paper_logical_type SNot)" by simp
  show ?thesis by (simp only: Model.paper_R_logical_denote_empty[OF nr typed];
    rule paper_ZF_R_Not_empty_correspondence[OF bounded fregean functional object])
qed

corollary paper_ZF_R_eval_Not:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and arrow: "h \<in> Encoding.coded_arrows"
    and typed: "named_env_typed (paper_bbk_domain (Encoding.coded_target h)) stock g"
  shows "paper_ZF_R_constructed_eval Root (NLogical SNot) h
      (paper_ZF_R_encode_assignment stock type_representation (Encoding.coded_target h) g) =
    Some (paper_ZF_rep_encode (type_representation (Arr Prop Prop)) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) g (NLogical SNot)))"
  by (simp only: paper_ZF_action_eval.simps
    paper_ZF_R_Not_correspondence[OF bounded fregean functional paper_ZF_R_eval_target_object[OF arrow] typed])

end

end
