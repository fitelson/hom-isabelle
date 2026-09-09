theory Bacon_Source_ZF_R_Quantifier_Tests
  imports Bacon_Source_ZF_R_All_Type_Representation
    Bacon_Source_ZF_R_Proposition_Identity_Truth
begin

section \<open>Every target value is tested by the encoded predicate\<close>

context paper_ZF_R_type_encoding
begin

lemma paper_ZF_R_predicate_source_test:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type \<sigma>" and object: "M \<in> objects"
    and predicate: "d \<in> paper_bbk_domain M (Arr \<sigma> Prop)"
    and arrow: "j \<in> Encoding.coded_arrows" and source: "Encoding.coded_source j = M"
    and argument: "a \<in> paper_bbk_domain (Encoding.coded_target j) \<sigma>"
  shows "Elem (Encoding.coded_identity (Encoding.coded_target j))
      (app (paper_ZF_rep_encode (type_representation (Arr \<sigma> Prop)) M d)
        (Opair j (paper_ZF_rep_encode (type_representation \<sigma>) (Encoding.coded_target j) a))) =
    paper_bbk_valuation (Encoding.coded_target j)
      (paper_R_application signature stock (paper_bbk_domain (Encoding.coded_target j))
        (paper_bbk_denote (Encoding.coded_target j)) \<sigma> Prop
        (paper_arrow_map (Encoding.decode_arrow j) (Arr \<sigma> Prop) d) a)"
proof -
  let ?h = "Encoding.decode_arrow j"
  let ?N = "Encoding.coded_target j"
  let ?X = "type_representation \<sigma>"
  let ?Y = "type_representation Prop"
  have original: "?h \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF arrow])
  have origin: "paper_arrow_source ?h = M" using source by (simp only: paper_ZF_recode_source_def)
  have target: "paper_arrow_target ?h = ?N" by (simp only: paper_ZF_recode_target_def)
  have no: "?N \<in> objects" using Encoding.target_object[OF original] by (simp only: target)
  have ar: "paper_R_type (Arr \<sigma> Prop)" using rt by simp
  have inv: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<sigma> ?X"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
  have encoding: "paper_ZF_R_profile_encoding signature stock objects arrows encode ArrowBound" by unfold_locales
  have typed: "paper_ZF_rep_encode ?X N b \<in> explode (paper_ZF_rep_domain ?X N)"
    if "N \<in> objects" "b \<in> paper_bbk_domain N \<sigma>" for N b
    by (rule paper_ZF_R_type_invariant_encode_type[OF inv that])
  have inverse: "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<sigma>) ?X N (paper_ZF_rep_encode ?X N b) = b"
    if "N \<in> objects" "b \<in> paper_bbk_domain N \<sigma>" for N b
    by (rule paper_ZF_R_type_invariant_decode_encode[OF inv that])
  have at: "a \<in> paper_bbk_domain (paper_arrow_target ?h) \<sigma>" by (simp only: target; rule argument)
  have tested: "app (paper_ZF_R_arrow_encode signature stock ArrowBound encode arrows \<sigma> Prop ?X ?Y M d)
      (Opair (encode ?h) (paper_ZF_rep_encode ?X (paper_arrow_target ?h) a)) =
    paper_ZF_rep_encode ?Y (paper_arrow_target ?h)
      (paper_R_application signature stock (paper_bbk_domain (paper_arrow_target ?h))
        (paper_bbk_denote (paper_arrow_target ?h)) \<sigma> Prop (paper_arrow_map ?h (Arr \<sigma> Prop) d) a)"
    by (rule paper_ZF_R_arrow_encode_source_argument[OF encoding typed inverse original origin at])
  have encoder: "paper_ZF_rep_encode (type_representation (Arr \<sigma> Prop)) =
      paper_ZF_R_arrow_encode signature stock ArrowBound encode arrows \<sigma> Prop ?X ?Y"
    by (simp only: paper_ZF_R_type_representation_arrow[OF ar] paper_ZF_R_arrow_representation_def
      paper_ZF_type_representation.select_convs)
  have morphism: "paper_R_bbk_model_morphism signature stock
      (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M)
      (paper_bbk_domain ?N) (paper_bbk_denote ?N) (paper_bbk_valuation ?N) (paper_arrow_map ?h)"
    using paper_R_bbk_arrows_morphism[OF paper_R_bbk_subcategory_arrow[OF R_category original]]
    by (simp only: paper_R_bbk_data_morphism_def origin target)
  interpret Target: paper_R_bbk_model signature stock "paper_bbk_domain ?N" "paper_bbk_denote ?N" "paper_bbk_valuation ?N"
    by (rule paper_R_bbk_model_morphism_target[OF morphism])
  have mapped: "paper_arrow_map ?h (Arr \<sigma> Prop) d \<in> paper_bbk_domain ?N (Arr \<sigma> Prop)"
    by (rule paper_R_bbk_homomorphism_domain[OF paper_R_bbk_model_morphism_raw[OF morphism] predicate])
  have result: "paper_R_application signature stock (paper_bbk_domain ?N) (paper_bbk_denote ?N)
      \<sigma> Prop (paper_arrow_map ?h (Arr \<sigma> Prop) d) a \<in> paper_bbk_domain ?N Prop"
    by (rule Target.paper_R_application_type[OF ar mapped argument])
  have graph: "app (paper_ZF_rep_encode (type_representation (Arr \<sigma> Prop)) M d)
      (Opair j (paper_ZF_rep_encode ?X ?N a)) =
    proposition_code ?N (paper_R_application signature stock (paper_bbk_domain ?N) (paper_bbk_denote ?N)
      \<sigma> Prop (paper_arrow_map ?h (Arr \<sigma> Prop) d) a)"
    using tested by (simp only: encoder target Encoding.paper_ZF_encode_decode_arrow[OF arrow] paper_ZF_R_Prop_fields(3))
  show ?thesis by (simp only: graph; rule paper_ZF_R_proposition_identity_truth[OF no result])
qed

text \<open>
  The range equality at target(j) replaces all represented arguments by
  all original arguments. It is the child σ bijection, not surjectivity
  of jσ, that justifies both the universal and existential directions.
  In particular, tests are not restricted to values transported from M.
\<close>

lemma paper_ZF_R_quantifier_tests:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type \<sigma>" and object: "M \<in> objects"
    and predicate: "d \<in> paper_bbk_domain M (Arr \<sigma> Prop)"
    and arrow: "j \<in> Encoding.coded_arrows" and source: "Encoding.coded_source j = M"
  shows "(if universal then \<forall>z\<in>explode (paper_ZF_rep_domain (type_representation \<sigma>) (Encoding.coded_target j)).
        Elem (Encoding.coded_identity (Encoding.coded_target j))
          (app (paper_ZF_rep_encode (type_representation (Arr \<sigma> Prop)) M d) (Opair j z))
      else \<exists>z\<in>explode (paper_ZF_rep_domain (type_representation \<sigma>) (Encoding.coded_target j)).
        Elem (Encoding.coded_identity (Encoding.coded_target j))
          (app (paper_ZF_rep_encode (type_representation (Arr \<sigma> Prop)) M d) (Opair j z))) =
    (if universal then \<forall>a\<in>paper_bbk_domain (Encoding.coded_target j) \<sigma>.
        paper_bbk_valuation (Encoding.coded_target j) (paper_R_application signature stock
          (paper_bbk_domain (Encoding.coded_target j)) (paper_bbk_denote (Encoding.coded_target j))
          \<sigma> Prop (paper_arrow_map (Encoding.decode_arrow j) (Arr \<sigma> Prop) d) a)
      else \<exists>a\<in>paper_bbk_domain (Encoding.coded_target j) \<sigma>.
        paper_bbk_valuation (Encoding.coded_target j) (paper_R_application signature stock
          (paper_bbk_domain (Encoding.coded_target j)) (paper_bbk_denote (Encoding.coded_target j))
          \<sigma> Prop (paper_arrow_map (Encoding.decode_arrow j) (Arr \<sigma> Prop) d) a))"
proof -
  have original: "Encoding.decode_arrow j \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF arrow])
  have no: "Encoding.coded_target j \<in> objects"
    using Encoding.target_object[OF original] by (simp only: paper_ZF_recode_target_def)
  have inv: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<sigma> (type_representation \<sigma>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
  have image: "explode (paper_ZF_rep_domain (type_representation \<sigma>) (Encoding.coded_target j)) =
      image (paper_ZF_rep_encode (type_representation \<sigma>) (Encoding.coded_target j))
        (paper_bbk_domain (Encoding.coded_target j) \<sigma>)"
    by (rule sym[OF paper_ZF_R_type_invariant_image[OF inv no]])
  have tests: "Elem (Encoding.coded_identity (Encoding.coded_target j))
      (app (paper_ZF_rep_encode (type_representation (Arr \<sigma> Prop)) M d)
        (Opair j (paper_ZF_rep_encode (type_representation \<sigma>) (Encoding.coded_target j) a))) =
    paper_bbk_valuation (Encoding.coded_target j)
      (paper_R_application signature stock (paper_bbk_domain (Encoding.coded_target j))
        (paper_bbk_denote (Encoding.coded_target j)) \<sigma> Prop
        (paper_arrow_map (Encoding.decode_arrow j) (Arr \<sigma> Prop) d) a)"
    if "a \<in> paper_bbk_domain (Encoding.coded_target j) \<sigma>" for a
    by (rule paper_ZF_R_predicate_source_test[OF bounded fregean functional rt object predicate arrow source that])
  show ?thesis using tests by (cases universal; simp only: if_True if_False image; blast)
qed

end

end
