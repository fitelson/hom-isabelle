theory Bacon_Source_ZF_R_Binary_Logical_Graphs
  imports Bacon_Source_ZF_R_Coded_Application Bacon_Source_ZF_R_Negation_Correspondence
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Binary_Logical_Application
begin

section \<open>Compare actual encoded graphs on their full pair domains\<close>

context paper_ZF_R_type_encoding
begin

lemma paper_ZF_R_type_encode_eq_pair_lambda:
  assumes rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and points: "\<And>i z. Elem (Opair i z) (paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target (paper_ZF_rep_domain (type_representation \<sigma>)) M) \<Longrightarrow>
      app (paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) M d) (Opair i z) = b i z"
  shows "paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) M d =
    paper_ZF_pair_lambda (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source Encoding.coded_target
      (paper_ZF_rep_domain (type_representation \<sigma>)) M b"
proof -
  let ?P = "paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source Encoding.coded_target
    (paper_ZF_rep_domain (type_representation \<sigma>)) M"
  let ?body = "paper_ZF_R_arrow_body signature stock ArrowBound encode arrows \<sigma> \<tau>
    (type_representation \<sigma>) (type_representation \<tau>) M d"
  have graph: "paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) M d =
    Lambda ?P (\<lambda>z. if Elem z ?P then ?body (Fst z,Snd z) else undefined)"
    by (simp only: paper_ZF_R_type_representation_arrow[OF rt] paper_ZF_R_arrow_representation_def
      paper_ZF_type_representation.select_convs paper_ZF_R_arrow_encode_def paper_ZF_encode_exponential_graph)
  have equal: "Lambda ?P (\<lambda>z. if Elem z ?P then ?body (Fst z,Snd z) else undefined) =
    Lambda ?P (\<lambda>z. b (Fst z) (Snd z))"
  proof (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI)
    fix z
    assume member: "Elem z ?P"
    obtain i p where shape: "z = Opair i p" by (rule paper_ZF_pair_codeE[OF member]; rule that; assumption)
    have pair: "Elem (Opair i p) ?P" using member by (simp only: shape)
    have point: "app (paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) M d) (Opair i p) = b i p"
      by (rule points[OF pair])
    have body: "(if Elem (Opair i p) ?P then ?body (i,p) else undefined) = b i p"
      using point by (simp only: graph Lambda_app[OF pair] Fst Snd)
    show "(if Elem z ?P then ?body (Fst z,Snd z) else undefined) = b (Fst z) (Snd z)"
      using body by (simp only: shape Fst Snd)
  qed
  show ?thesis by (simp only: graph paper_ZF_pair_lambda_def; rule equal)
qed

text \<open>
  For l:σ→σ→t, the encoded partial value l(a) is the inner
  graph (j,q)↦resulttarget(j)(jσ(fσ(a)),q), once the actual
  coded truth-profile equation for l at TWO old values has been proved.
  Source: Definition 3.19, p.56, and Proposition 3.22, p.72.
  The callback below is a theorem premise to be discharged by the
  particular primitive clause; it is not an added model field.
\<close>

theorem paper_ZF_R_binary_partial_graph:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and sr: "paper_R_type \<sigma>" and symbol: "paper_logical_type l = Arr \<sigma> (Arr \<sigma> Prop)"
    and object: "M \<in> objects" and am: "a \<in> paper_bbk_domain M \<sigma>"
    and result_clause: "\<And>N x y. N \<in> objects \<Longrightarrow> x \<in> paper_bbk_domain N \<sigma> \<Longrightarrow>
      y \<in> paper_bbk_domain N \<sigma> \<Longrightarrow>
      proposition_code N (paper_R_binary_logical_application signature stock (paper_bbk_domain N) (paper_bbk_denote N) \<sigma> l x y) =
      result N (paper_ZF_rep_encode (type_representation \<sigma>) N x) (paper_ZF_rep_encode (type_representation \<sigma>) N y)"
  shows "paper_ZF_rep_encode (type_representation (Arr \<sigma> Prop)) M
      (paper_R_application signature stock (paper_bbk_domain M) (paper_bbk_denote M)
        \<sigma> (Arr \<sigma> Prop) (paper_bbk_denote M Map.empty (NLogical l)) a) =
    paper_ZF_pair_lambda (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source Encoding.coded_target
      (paper_ZF_rep_domain (type_representation \<sigma>)) M
      (\<lambda>i q. result (Encoding.coded_target i)
        (paper_ZF_rep_transport (type_representation \<sigma>) i (paper_ZF_rep_encode (type_representation \<sigma>) M a)) q)"
proof -
  have rt: "paper_R_type (Arr \<sigma> Prop)" and outer_rt: "paper_R_type (Arr \<sigma> (Arr \<sigma> Prop))"
    and lr: "paper_R_type (paper_logical_type l)" by (simp_all add: sr symbol)
  have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<sigma> (type_representation \<sigma>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional sr])
  interpret Model: paper_R_bbk_model signature stock "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF R_category object]])
  have logical_type: "paper_bbk_denote M Map.empty (NLogical l) \<in> paper_bbk_domain M (Arr \<sigma> (Arr \<sigma> Prop))"
    using Model.paper_R_logical_denote_type[OF lr] by (simp only: symbol)
  show ?thesis
  proof (rule paper_ZF_R_type_encode_eq_pair_lambda[OF rt])
    fix i q
    assume pair: "Elem (Opair i q) (paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target (paper_ZF_rep_domain (type_representation \<sigma>)) M)"
    let ?N = "Encoding.coded_target i"
    let ?b = "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<sigma>) (type_representation \<sigma>) ?N q"
    let ?a = "paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) i a"
    let ?v = "paper_R_application signature stock (paper_bbk_domain M) (paper_bbk_denote M)
      \<sigma> (Arr \<sigma> Prop) (paper_bbk_denote M Map.empty (NLogical l)) a"
    have ia: "i \<in> Encoding.coded_arrows" and source: "Encoding.coded_source i = M"
      and qm: "q \<in> explode (paper_ZF_rep_domain (type_representation \<sigma>) ?N)"
      using pair by (auto simp only: paper_ZF_pair_code_member)
    have no: "?N \<in> objects" by (rule paper_ZF_R_eval_target_object[OF ia])
    have source_a: "a \<in> paper_bbk_domain (Encoding.coded_source i) \<sigma>" by (simp only: source; rule am)
    have source_l: "paper_bbk_denote M Map.empty (NLogical l) \<in>
      paper_bbk_domain (Encoding.coded_source i) (Arr \<sigma> (Arr \<sigma> Prop))"
      by (simp only: source; rule logical_type)
    have original_arrow: "Encoding.decode_arrow i \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF ia])
    have typed_arrow: "Encoding.decode_arrow i \<in> paper_typed_arrows objects paper_bbk_domain"
      by (rule paper_R_bbk_arrows_typed[OF paper_R_bbk_subcategory_arrow[OF R_category original_arrow]])
    have original_a: "a \<in> paper_bbk_domain (paper_arrow_source (Encoding.decode_arrow i)) \<sigma>"
      using source_a by (simp only: paper_ZF_recode_source_def)
    have moved_a: "?a \<in> paper_bbk_domain ?N \<sigma>"
      by (simp only: paper_ZF_recode_transport_def paper_ZF_recode_target_def;
        rule paper_typed_arrows_map[OF typed_arrow original_a])
    have old_b: "?b \<in> paper_bbk_domain ?N \<sigma>"
      by (rule paper_ZF_R_type_invariant_decode_type[OF invariant no qm])
    have code_b: "paper_ZF_rep_encode (type_representation \<sigma>) ?N ?b = q"
      by (rule paper_ZF_R_type_invariant_encode_decode[OF invariant no qm])
    have code_a: "paper_ZF_rep_encode (type_representation \<sigma>) ?N ?a =
      paper_ZF_rep_transport (type_representation \<sigma>) i (paper_ZF_rep_encode (type_representation \<sigma>) M a)"
      using paper_action_map_equivariant[OF paper_ZF_R_type_invariant_forward[OF invariant] ia source_a]
      by (simp only: source)
    have moved_l: "paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> (Arr \<sigma> Prop))) i
        (paper_bbk_denote M Map.empty (NLogical l)) = paper_bbk_denote ?N Map.empty (NLogical l)"
      using paper_ZF_R_logical_transport_empty[OF ia source lr] by (simp only: symbol)
    have moved_partial: "paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> Prop)) i ?v =
      paper_R_application signature stock (paper_bbk_domain ?N) (paper_bbk_denote ?N)
        \<sigma> (Arr \<sigma> Prop) (paper_bbk_denote ?N Map.empty (NLogical l)) ?a"
      using paper_ZF_R_coded_application_transport[where i=i and \<sigma>=\<sigma> and \<tau>="Arr \<sigma> Prop",
        OF ia outer_rt source_l source_a]
      by (simp only: source moved_l)
    have result_value: "paper_ZF_rep_encode (type_representation Prop) ?N
        (paper_R_application signature stock (paper_bbk_domain ?N) (paper_bbk_denote ?N) \<sigma> Prop
          (paper_R_application signature stock (paper_bbk_domain ?N) (paper_bbk_denote ?N)
            \<sigma> (Arr \<sigma> Prop) (paper_bbk_denote ?N Map.empty (NLogical l)) ?a) ?b) =
      result ?N (paper_ZF_rep_transport (type_representation \<sigma>) i
        (paper_ZF_rep_encode (type_representation \<sigma>) M a)) q"
      using result_clause[OF no moved_a old_b]
      by (simp only: paper_ZF_R_Prop_fields(3) paper_R_binary_logical_application_def code_a code_b)
    show "app (paper_ZF_rep_encode (type_representation (Arr \<sigma> Prop)) M ?v) (Opair i q) =
      result ?N (paper_ZF_rep_transport (type_representation \<sigma>) i
        (paper_ZF_rep_encode (type_representation \<sigma>) M a)) q"
      by (simp only: paper_ZF_R_type_encode_pair_value[OF rt pair] moved_partial result_value)
  qed
qed

theorem paper_ZF_R_binary_logical_graph:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and sr: "paper_R_type \<sigma>" and symbol: "paper_logical_type l = Arr \<sigma> (Arr \<sigma> Prop)"
    and object: "M \<in> objects"
    and result_clause: "\<And>N x y. N \<in> objects \<Longrightarrow> x \<in> paper_bbk_domain N \<sigma> \<Longrightarrow>
      y \<in> paper_bbk_domain N \<sigma> \<Longrightarrow>
      proposition_code N (paper_R_binary_logical_application signature stock (paper_bbk_domain N) (paper_bbk_denote N) \<sigma> l x y) =
      result N (paper_ZF_rep_encode (type_representation \<sigma>) N x) (paper_ZF_rep_encode (type_representation \<sigma>) N y)"
  shows "paper_ZF_rep_encode (type_representation (Arr \<sigma> (Arr \<sigma> Prop))) M
      (paper_bbk_denote M Map.empty (NLogical l)) =
    paper_ZF_pair_lambda (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source Encoding.coded_target
      (paper_ZF_rep_domain (type_representation \<sigma>)) M
      (\<lambda>i p. paper_ZF_pair_lambda (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source Encoding.coded_target
        (paper_ZF_rep_domain (type_representation \<sigma>)) (Encoding.coded_target i)
        (\<lambda>j q. result (Encoding.coded_target j) (paper_ZF_rep_transport (type_representation \<sigma>) j p) q))"
proof -
  have rt: "paper_R_type (Arr \<sigma> (Arr \<sigma> Prop))" and lr: "paper_R_type (paper_logical_type l)"
    by (simp_all add: sr symbol)
  have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<sigma> (type_representation \<sigma>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional sr])
  show ?thesis
  proof (rule paper_ZF_R_type_encode_eq_pair_lambda[OF rt])
    fix i p
    assume pair: "Elem (Opair i p) (paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target (paper_ZF_rep_domain (type_representation \<sigma>)) M)"
    let ?N = "Encoding.coded_target i"
    let ?a = "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<sigma>) (type_representation \<sigma>) ?N p"
    have ia: "i \<in> Encoding.coded_arrows" and source: "Encoding.coded_source i = M"
      and pm: "p \<in> explode (paper_ZF_rep_domain (type_representation \<sigma>) ?N)"
      using pair by (auto simp only: paper_ZF_pair_code_member)
    have no: "?N \<in> objects" by (rule paper_ZF_R_eval_target_object[OF ia])
    have am: "?a \<in> paper_bbk_domain ?N \<sigma>" by (rule paper_ZF_R_type_invariant_decode_type[OF invariant no pm])
    have child_cancel: "paper_ZF_rep_encode (type_representation \<sigma>) ?N ?a = p"
      by (rule paper_ZF_R_type_invariant_encode_decode[OF invariant no pm])
    have moved_l: "paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> (Arr \<sigma> Prop))) i
      (paper_bbk_denote M Map.empty (NLogical l)) = paper_bbk_denote ?N Map.empty (NLogical l)"
      using paper_ZF_R_logical_transport_empty[OF ia source lr] by (simp only: symbol)
    show "app (paper_ZF_rep_encode (type_representation (Arr \<sigma> (Arr \<sigma> Prop))) M
        (paper_bbk_denote M Map.empty (NLogical l))) (Opair i p) =
      paper_ZF_pair_lambda (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source Encoding.coded_target
        (paper_ZF_rep_domain (type_representation \<sigma>)) ?N
        (\<lambda>j q. result (Encoding.coded_target j) (paper_ZF_rep_transport (type_representation \<sigma>) j p) q)"
      by (simp only: paper_ZF_R_type_encode_pair_value[OF rt pair] moved_l
        paper_ZF_R_binary_partial_graph[where result=result, OF bounded fregean functional sr symbol no am result_clause] child_cancel)
  qed
qed

end

end
