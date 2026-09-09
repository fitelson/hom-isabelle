theory Bacon_Source_ZF_R_Canonical_Application
  imports Bacon_Source_ZF_R_All_Type_Representation
begin

section \<open>Application at the identity arrow\<close>

text \<open>
  Application in an action interpretation is F⟨1M,a⟩.
  Source: Definition 3.19, p.56. On encoded original values this
  equals fτM(appᴹσ,τ(d,a)); the test arrow is the original identity.
  The child σ inverse is justified by its already proved invariant.

  Status: actual application correspondence and closure of all coded
  domains, as required by footnote 78(i). No premodel, model-totality,
  application-closure, or higher-type decoder premise is introduced.
\<close>

definition paper_ZF_action_apply :: "('o \<Rightarrow> ZF) \<Rightarrow> 'o \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF" where
  "paper_ZF_action_apply identity M F a = app F (Opair (identity M) a)"

context paper_ZF_R_type_encoding
begin

theorem paper_ZF_R_application_correspondence:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type (Arr \<sigma> \<tau>)" and object: "M \<in> objects"
    and head: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)" and argument: "a \<in> paper_bbk_domain M \<sigma>"
  shows "paper_ZF_action_apply Encoding.coded_identity M
      (paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) M d)
      (paper_ZF_rep_encode (type_representation \<sigma>) M a) =
    paper_ZF_rep_encode (type_representation \<tau>) M
      (paper_R_application signature stock (paper_bbk_domain M) (paper_bbk_denote M) \<sigma> \<tau> d a)"
proof -
  let ?X = "type_representation \<sigma>"
  let ?Y = "type_representation \<tau>"
  let ?i = "paper_typed_identity paper_bbk_domain M"
  have sr: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF rt])
  have sigma_invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<sigma> ?X"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional sr])
  have encoding: "paper_ZF_R_profile_encoding signature stock objects arrows encode ArrowBound" by unfold_locales
  have input_typed: "paper_ZF_rep_encode ?X N b \<in> explode (paper_ZF_rep_domain ?X N)"
    if "N \<in> objects" "b \<in> paper_bbk_domain N \<sigma>" for N b
    by (rule paper_ZF_R_type_invariant_encode_type[OF sigma_invariant that])
  have input_inverse: "paper_ZF_rep_inverse (\<lambda>N. paper_bbk_domain N \<sigma>) ?X N (paper_ZF_rep_encode ?X N b) = b"
    if "N \<in> objects" "b \<in> paper_bbk_domain N \<sigma>" for N b
    by (rule paper_ZF_R_type_invariant_decode_encode[OF sigma_invariant that])
  have arrow: "?i \<in> arrows" by (rule Encoding.identity_arrow[OF object])
  have source: "paper_arrow_source ?i = M" by (rule paper_typed_identity_endpoints)
  have target: "paper_arrow_target ?i = M" by (rule paper_typed_identity_endpoints)
  have argument_target: "a \<in> paper_bbk_domain (paper_arrow_target ?i) \<sigma>"
    by (simp only: target; rule argument)
  have identity_head: "paper_arrow_map ?i (Arr \<sigma> \<tau>) d = d"
    by (rule paper_typed_identity_map_on[where D=paper_bbk_domain and A=M and \<sigma>="Arr \<sigma> \<tau>", OF head])
  have tested: "app (paper_ZF_R_arrow_encode signature stock ArrowBound encode arrows \<sigma> \<tau> ?X ?Y M d)
      (Opair (encode ?i) (paper_ZF_rep_encode ?X (paper_arrow_target ?i) a)) =
      paper_ZF_rep_encode ?Y (paper_arrow_target ?i)
        (paper_R_application signature stock (paper_bbk_domain (paper_arrow_target ?i))
          (paper_bbk_denote (paper_arrow_target ?i)) \<sigma> \<tau> (paper_arrow_map ?i (Arr \<sigma> \<tau>) d) a)"
    by (rule paper_ZF_R_arrow_encode_source_argument[OF encoding input_typed input_inverse arrow source argument_target])
  have arrow_encoder: "paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) =
      paper_ZF_R_arrow_encode signature stock ArrowBound encode arrows \<sigma> \<tau> ?X ?Y"
    by (simp only: paper_ZF_R_type_representation_arrow[OF rt] paper_ZF_R_arrow_representation_def
      paper_ZF_type_representation.select_convs)
  show ?thesis using tested
    by (simp only: paper_ZF_action_apply_def paper_ZF_recode_identity_def arrow_encoder target identity_head)
qed

theorem paper_ZF_R_application_closed:
  assumes bounded: "\<And>N. N \<in> objects \<Longrightarrow> paper_bbk_domain N Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type (Arr \<sigma> \<tau>)" and object: "M \<in> objects"
    and head: "F \<in> explode (paper_ZF_rep_domain (type_representation (Arr \<sigma> \<tau>)) M)"
    and argument: "z \<in> explode (paper_ZF_rep_domain (type_representation \<sigma>) M)"
  shows "paper_ZF_action_apply Encoding.coded_identity M F z \<in>
    explode (paper_ZF_rep_domain (type_representation \<tau>) M)"
proof -
  have sr: "paper_R_type \<sigma>" and tr: "paper_R_type \<tau>" using rt by simp_all
  have sigma_invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<sigma> (type_representation \<sigma>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional sr])
  have tau_invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<tau> (type_representation \<tau>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional tr])
  have arrow_invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound (Arr \<sigma> \<tau>)
      (type_representation (Arr \<sigma> \<tau>))"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
  have head_image: "F \<in> image (paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) M)
      (paper_bbk_domain M (Arr \<sigma> \<tau>))"
    using head by (simp only: paper_ZF_R_type_invariant_image[OF arrow_invariant object])
  obtain d where dm: "d \<in> paper_bbk_domain M (Arr \<sigma> \<tau>)"
    and dshape: "F = paper_ZF_rep_encode (type_representation (Arr \<sigma> \<tau>)) M d"
    using head_image by blast
  have argument_image: "z \<in> image (paper_ZF_rep_encode (type_representation \<sigma>) M) (paper_bbk_domain M \<sigma>)"
    using argument by (simp only: paper_ZF_R_type_invariant_image[OF sigma_invariant object])
  obtain a where am: "a \<in> paper_bbk_domain M \<sigma>" and ashape: "z = paper_ZF_rep_encode (type_representation \<sigma>) M a"
    using argument_image by blast
  interpret Model: paper_R_bbk_model signature stock "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF R_category object]])
  have original_result: "paper_R_application signature stock (paper_bbk_domain M) (paper_bbk_denote M) \<sigma> \<tau> d a
      \<in> paper_bbk_domain M \<tau>"
    by (rule Model.paper_R_application_type[OF rt dm am])
  have coded_result: "paper_ZF_rep_encode (type_representation \<tau>) M
      (paper_R_application signature stock (paper_bbk_domain M) (paper_bbk_denote M) \<sigma> \<tau> d a)
      \<in> explode (paper_ZF_rep_domain (type_representation \<tau>) M)"
    by (rule paper_ZF_R_type_invariant_encode_type[OF tau_invariant object original_result])
  show ?thesis by (simp only: dshape ashape
    paper_ZF_R_application_correspondence[OF bounded fregean functional rt object dm am]; rule coded_result)
qed

end

end
