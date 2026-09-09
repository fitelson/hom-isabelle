theory Bacon_Source_ZF_R_Coded_Application
  imports Bacon_Source_ZF_R_Individual_Base
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Application_Morphism
begin

section \<open>Application transport and evaluation at arbitrary coded pairs\<close>

text \<open>
  Along a coded arrow i:M→N, old application commutes with its
  decoded homomorphism. The actual arrow encoder, tested at a legitimate
  pair ⟨i,z⟩, applies the old transported head to the child inverse of z.
  Source: §3.3, p.49, Definition 3.19, p.56, and Proposition 3.22,
  p.72. These helpers assume no evaluator or logical-stock closure.
\<close>

context paper_ZF_R_profile_encoding
begin

lemma paper_ZF_R_coded_application_transport:
  assumes arrow: "i \<in> Encoding.coded_arrows" and rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and head: "d \<in> paper_bbk_domain (Encoding.coded_source i) (Arr \<sigma> \<tau>)"
    and argument: "a \<in> paper_bbk_domain (Encoding.coded_source i) \<sigma>"
  shows "paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<tau>) i
      (paper_R_application signature stock (paper_bbk_domain (Encoding.coded_source i))
        (paper_bbk_denote (Encoding.coded_source i)) \<sigma> \<tau> d a) =
    paper_R_application signature stock (paper_bbk_domain (Encoding.coded_target i))
      (paper_bbk_denote (Encoding.coded_target i)) \<sigma> \<tau>
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>)) i d)
      (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h \<sigma>) i a)"
proof -
  have original: "Encoding.decode_arrow i \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF arrow])
  have data: "paper_R_bbk_data_morphism signature stock (paper_arrow_source (Encoding.decode_arrow i))
      (paper_arrow_target (Encoding.decode_arrow i)) (paper_arrow_map (Encoding.decode_arrow i))"
    by (rule paper_R_bbk_arrows_morphism[OF paper_R_bbk_subcategory_arrow[OF R_category original]])
  have morphism: "paper_R_bbk_model_morphism signature stock
      (paper_bbk_domain (Encoding.coded_source i)) (paper_bbk_denote (Encoding.coded_source i)) (paper_bbk_valuation (Encoding.coded_source i))
      (paper_bbk_domain (Encoding.coded_target i)) (paper_bbk_denote (Encoding.coded_target i)) (paper_bbk_valuation (Encoding.coded_target i))
      (paper_arrow_map (Encoding.decode_arrow i))"
    using data by (simp only: paper_R_bbk_data_morphism_def paper_ZF_recode_source_def paper_ZF_recode_target_def)
  show ?thesis by (simp only: paper_ZF_recode_transport_def;
    rule paper_R_application_morphism[OF morphism rt head argument])
qed

end

context paper_ZF_R_type_encoding
begin

lemma paper_ZF_R_type_encode_pair_value:
  assumes rt: "paper_R_type (Arr \<sigma> \<tau>)"
    and pair: "Elem (Opair i z) (paper_ZF_pair_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target (paper_ZF_rep_domain (type_representation \<sigma>)) M)"
  shows "app (paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) M d) (Opair i z) =
    paper_ZF_rep_encode (type_representation \<tau>) (Encoding.coded_target i)
      (paper_R_application signature stock (paper_bbk_domain (Encoding.coded_target i))
        (paper_bbk_denote (Encoding.coded_target i)) \<sigma> \<tau>
        (paper_ZF_recode_transport arrows encode (\<lambda>h. paper_arrow_map h (Arr \<sigma> \<tau>)) i d)
        (paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<sigma>) (type_representation \<sigma>) (Encoding.coded_target i) z))"
  by (simp only: paper_ZF_R_type_representation_arrow[OF rt] paper_ZF_R_arrow_representation_def
    paper_ZF_type_representation.select_convs paper_ZF_R_arrow_encode_value[OF pair] paper_ZF_R_arrow_body_on[OF pair])

end

end
