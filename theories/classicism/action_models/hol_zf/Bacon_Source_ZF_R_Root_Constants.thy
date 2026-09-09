theory Bacon_Source_ZF_R_Root_Constants
  imports Bacon_Source_ZF_R_All_Type_Representation
begin

section \<open>Constants interpreted in the root fiber\<close>

text \<open>
  Put Iσ(c)=fσRoot(⟦c⟧Root) for each declared c:σ. This is
  the constant data for Definition 3.18(4), p.55, in the construction
  of Proposition 3.22, p.72. The original constant is evaluated at
  the empty partial assignment, which is typed and adequate for c.
  Locality shows that any other typed assignment gives the same value.

  For EVERY coded h:Root→M, forward naturality and the original
  homomorphism equation give hσ(Iσ(c))=fσM(⟦c⟧M). No root arrow
  is selected or assumed unique. Root reachability is separate and
  unnecessary for this equation at each supplied arrow. Neither a
  new interpretation function nor action-model totality is assumed.
\<close>

lemma paper_ZF_R_empty_assignment_typed:
  "named_env_typed D G (Map.empty :: ZF named_assignment)"
  by (simp add: named_env_typed_def)

lemma paper_ZF_R_constant_adequate:
  "named_adequate g (NConst c \<sigma>)"
  by (simp add: named_adequate_def)

lemma paper_ZF_R_hom_empty_assignment:
  "paper_hom_assignment G h Map.empty = Map.empty"
  by (rule ext, simp add: paper_hom_assignment_def)

context paper_ZF_R_type_encoding
begin

definition paper_ZF_R_root_constant :: "('c,ZF) paper_bbk_model_data \<Rightarrow> otype \<Rightarrow> 'c \<Rightarrow> ZF" where
  "paper_ZF_R_root_constant Root \<sigma> c = paper_ZF_rep_encode (type_representation \<sigma>) Root
    (paper_bbk_denote Root Map.empty (NConst c \<sigma>))"

lemma paper_ZF_R_declared_constant_language:
  assumes declared: "c \<in> signature \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_R_in_language signature stock (NConst c \<sigma>) \<sigma>"
  unfolding paper_R_in_language_def
  by (simp only: named_in_signature.simps; rule conjI[OF paper_R_has_type.Const[OF rt] declared])

lemma paper_ZF_R_original_constant_type:
  assumes object: "M \<in> objects" and declared: "c \<in> signature \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_bbk_denote M Map.empty (NConst c \<sigma>) \<in> paper_bbk_domain M \<sigma>"
  by (rule paper_R_bbk_data_denote_type[
    OF paper_R_bbk_subcategory_models[OF R_category object]
      paper_ZF_R_declared_constant_language[OF declared rt]
      paper_ZF_R_empty_assignment_typed paper_ZF_R_constant_adequate])

lemma paper_ZF_R_original_constant_denote_empty:
  assumes object: "M \<in> objects" and declared: "c \<in> signature \<sigma>" and rt: "paper_R_type \<sigma>"
    and typed: "named_env_typed (paper_bbk_domain M) stock g"
  shows "paper_bbk_denote M g (NConst c \<sigma>) = paper_bbk_denote M Map.empty (NConst c \<sigma>)"
proof -
  interpret Model: paper_R_bbk_model signature stock "paper_bbk_domain M" "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF paper_R_bbk_subcategory_models[OF R_category object]])
  show ?thesis
  proof (rule Model.denote_locality[OF paper_ZF_R_declared_constant_language[OF declared rt]
      typed paper_ZF_R_empty_assignment_typed paper_ZF_R_constant_adequate paper_ZF_R_constant_adequate])
    fix n
    assume "n \<in> named_fv (NConst c \<sigma>)"
    then show "g n = Map.empty n" by simp
  qed
qed

lemma paper_ZF_R_original_constant_transport:
  assumes arrow: "h \<in> arrows" and declared: "c \<in> signature \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_arrow_map h \<sigma> (paper_bbk_denote (paper_arrow_source h) Map.empty (NConst c \<sigma>)) =
    paper_bbk_denote (paper_arrow_target h) Map.empty (NConst c \<sigma>)"
proof -
  have morphism: "paper_R_bbk_data_morphism signature stock (paper_arrow_source h) (paper_arrow_target h) (paper_arrow_map h)"
    by (rule paper_R_bbk_arrows_morphism[OF paper_R_bbk_subcategory_arrow[OF R_category arrow]])
  have hom: "paper_R_bbk_homomorphism signature stock
      (paper_bbk_domain (paper_arrow_source h)) (paper_bbk_denote (paper_arrow_source h))
      (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h)) (paper_arrow_map h)"
    by (rule paper_R_bbk_data_morphism_raw[OF morphism])
  have equation: "paper_arrow_map h \<sigma> (paper_bbk_denote (paper_arrow_source h) Map.empty (NConst c \<sigma>)) =
      paper_bbk_denote (paper_arrow_target h) (paper_hom_assignment stock (paper_arrow_map h) Map.empty) (NConst c \<sigma>)"
    by (rule paper_R_bbk_homomorphism_denote[OF hom paper_ZF_R_declared_constant_language[OF declared rt]
      paper_ZF_R_empty_assignment_typed paper_ZF_R_constant_adequate])
  show ?thesis using equation by (simp only: paper_ZF_R_hom_empty_assignment)
qed

theorem paper_ZF_R_root_constant_type:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and root: "Root \<in> objects" and declared: "c \<in> signature \<sigma>" and rt: "paper_R_type \<sigma>"
  shows "paper_ZF_R_root_constant Root \<sigma> c \<in> explode (paper_ZF_rep_domain (type_representation \<sigma>) Root)"
  unfolding paper_ZF_R_root_constant_def
  by (rule paper_ZF_R_type_invariant_encode_type[
    OF paper_ZF_R_all_type_invariant[OF bounded fregean functional rt] root
      paper_ZF_R_original_constant_type[OF root declared rt]])

theorem paper_ZF_R_root_constant_transport:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and root: "Root \<in> objects" and declared: "c \<in> signature \<sigma>" and rt: "paper_R_type \<sigma>"
    and arrow: "h \<in> Encoding.coded_arrows" and source: "Encoding.coded_source h = Root"
  shows "paper_ZF_rep_transport (type_representation \<sigma>) h (paper_ZF_R_root_constant Root \<sigma> c) =
    paper_ZF_rep_encode (type_representation \<sigma>) (Encoding.coded_target h)
      (paper_bbk_denote (Encoding.coded_target h) Map.empty (NConst c \<sigma>))"
proof -
  let ?d = "paper_bbk_denote Root Map.empty (NConst c \<sigma>)"
  have invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<sigma> (type_representation \<sigma>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
  have member: "?d \<in> paper_bbk_domain Root \<sigma>" by (rule paper_ZF_R_original_constant_type[OF root declared rt])
  have source_member: "?d \<in> paper_bbk_domain (Encoding.coded_source h) \<sigma>"
    by (simp only: source; rule member)
  have natural: "paper_ZF_rep_encode (type_representation \<sigma>) (Encoding.coded_target h)
      (paper_ZF_recode_transport arrows encode (\<lambda>f. paper_arrow_map f \<sigma>) h ?d) =
    paper_ZF_rep_transport (type_representation \<sigma>) h
      (paper_ZF_rep_encode (type_representation \<sigma>) (Encoding.coded_source h) ?d)"
    by (rule paper_action_map_equivariant[OF paper_ZF_R_type_invariant_forward[OF invariant] arrow source_member])
  have original_arrow: "Encoding.decode_arrow h \<in> arrows" by (rule Encoding.paper_ZF_decode_arrow_type[OF arrow])
  have origin: "paper_arrow_source (Encoding.decode_arrow h) = Root"
    using source by (simp only: paper_ZF_recode_source_def)
  have transported_constant: "paper_ZF_recode_transport arrows encode (\<lambda>f. paper_arrow_map f \<sigma>) h ?d =
      paper_bbk_denote (Encoding.coded_target h) Map.empty (NConst c \<sigma>)"
    using paper_ZF_R_original_constant_transport[OF original_arrow declared rt]
    by (simp only: paper_ZF_recode_transport_def paper_ZF_recode_target_def origin)
  show ?thesis using natural
    by (simp only: paper_ZF_R_root_constant_def source transported_constant; rule sym)
qed

corollary paper_ZF_R_root_constant_parallel:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and root: "Root \<in> objects" and declared: "c \<in> signature \<sigma>" and rt: "paper_R_type \<sigma>"
    and first: "h \<in> Encoding.coded_arrows" and hs: "Encoding.coded_source h = Root"
    and second: "i \<in> Encoding.coded_arrows" and isource: "Encoding.coded_source i = Root"
    and same_target: "Encoding.coded_target h = Encoding.coded_target i"
  shows "paper_ZF_rep_transport (type_representation \<sigma>) h (paper_ZF_R_root_constant Root \<sigma> c) =
    paper_ZF_rep_transport (type_representation \<sigma>) i (paper_ZF_R_root_constant Root \<sigma> c)"
  by (simp only: paper_ZF_R_root_constant_transport[OF bounded fregean functional root declared rt first hs]
    paper_ZF_R_root_constant_transport[OF bounded fregean functional root declared rt second isource] same_target)

text \<open>
  Parallel root arrows therefore agree on the constructed constant data.
  This proves the nonlogical harmony noted on p.73 for this construction;
  it is not a restriction added to general action premodels. In particular,
  agreement on these constants does not identify the arrows themselves.
\<close>

end

end
