theory Bacon_Source_ZF_R_Premodel_Domains
  imports Bacon_Source_ZF_R_All_Type_Representation
begin

section \<open>The actual recursive domains satisfy the required subaction clauses\<close>

text \<open>
  The proposition action is a subaction of the coded outgoing powerset.
  For σ→τ∈R, the selected arrow action is a subaction of the coded
  exponential of the ACTUAL selected σ and τ actions.
  Source: Definition 3.18(i.2–3), p.55, and Proposition 3.22,
  p.72. No child decoder or higher-type representation is assumed:
  the child and arrow action laws come from the proved all-type invariant.

  Range separation gives fiber inclusion, while the recursive transport
  is literally the ambient exponential transport. This proves the domain
  clauses only. A rooted category, root constant assignments, partial
  interpretation, and totality remain separate construction components.
\<close>

context paper_ZF_R_type_encoding
begin

theorem paper_ZF_R_premodel_Prop_subaction:
  "paper_subaction objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity
    (\<lambda>M. explode (paper_ZF_rep_domain (type_representation Prop) M)) (paper_ZF_rep_transport (type_representation Prop))
    (\<lambda>M. explode (paper_ZF_powerset_code (paper_ZF_image_code ArrowBound encode arrows) Encoding.coded_source M))
    (paper_ZF_powerset_transport_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose)"
  using paper_ZF_R_Prop_subaction by (simp only: paper_ZF_R_Prop_fields(1))

lemma paper_ZF_R_premodel_arrow_domain_subset:
  assumes rt: "paper_R_type (Arr \<sigma> \<tau>)"
  shows "explode (paper_ZF_rep_domain (type_representation (Arr \<sigma> \<tau>)) M) \<subseteq>
    explode (paper_ZF_exponential_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose
      (paper_ZF_rep_domain (type_representation \<sigma>)) (paper_ZF_rep_transport (type_representation \<sigma>))
      (paper_ZF_rep_domain (type_representation \<tau>)) (paper_ZF_rep_transport (type_representation \<tau>)) M)"
  by (simp only: paper_ZF_R_type_representation_arrow[OF rt] paper_ZF_R_arrow_representation_def
    paper_ZF_type_representation.select_convs paper_ZF_R_arrow_bound_def;
    rule paper_ZF_range_code_subset)

lemma paper_ZF_R_premodel_arrow_transport:
  assumes rt: "paper_R_type (Arr \<sigma> \<tau>)"
  shows "paper_ZF_rep_transport (type_representation (Arr \<sigma> \<tau>)) =
    paper_ZF_exponential_transport_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose (paper_ZF_rep_domain (type_representation \<sigma>))"
  by (simp only: paper_ZF_R_type_representation_arrow[OF rt] paper_ZF_R_arrow_representation_def
    paper_ZF_type_representation.select_convs)

theorem paper_ZF_R_premodel_arrow_subaction:
  assumes bounded: "\<And>M. M \<in> objects \<Longrightarrow> paper_bbk_domain M Ind \<subseteq> explode IndividualBound"
    and fregean: "paper_bbk_quasi_fregean_on objects arrows"
    and functional: "paper_R_quasi_functional_on signature stock objects arrows"
    and rt: "paper_R_type (Arr \<sigma> \<tau>)"
  shows "paper_subaction objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
    Encoding.coded_compose Encoding.coded_identity
    (\<lambda>M. explode (paper_ZF_rep_domain (type_representation (Arr \<sigma> \<tau>)) M))
    (paper_ZF_rep_transport (type_representation (Arr \<sigma> \<tau>)))
    (\<lambda>M. explode (paper_ZF_exponential_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose
      (paper_ZF_rep_domain (type_representation \<sigma>)) (paper_ZF_rep_transport (type_representation \<sigma>))
      (paper_ZF_rep_domain (type_representation \<tau>)) (paper_ZF_rep_transport (type_representation \<tau>)) M))
    (paper_ZF_exponential_transport_code (paper_ZF_image_code ArrowBound encode arrows)
      Encoding.coded_source Encoding.coded_target Encoding.coded_compose (paper_ZF_rep_domain (type_representation \<sigma>)))"
proof -
  have sr: "paper_R_type \<sigma>" and tr: "paper_R_type \<tau>" using rt by simp_all
  have sigma_invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<sigma> (type_representation \<sigma>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional sr])
  have tau_invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound \<tau> (type_representation \<tau>)"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional tr])
  have arrow_invariant: "paper_ZF_R_type_invariant objects arrows encode ArrowBound (Arr \<sigma> \<tau>)
      (type_representation (Arr \<sigma> \<tau>))"
    by (rule paper_ZF_R_all_type_invariant[OF bounded fregean functional rt])
  have sigma_action: "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
      Encoding.coded_compose Encoding.coded_identity
      (\<lambda>M. explode (paper_ZF_rep_domain (type_representation \<sigma>) M)) (paper_ZF_rep_transport (type_representation \<sigma>))"
    by (rule paper_ZF_R_type_invariant_action[OF sigma_invariant])
  have tau_action: "paper_action objects Encoding.coded_arrows Encoding.coded_source Encoding.coded_target
      Encoding.coded_compose Encoding.coded_identity
      (\<lambda>M. explode (paper_ZF_rep_domain (type_representation \<tau>) M)) (paper_ZF_rep_transport (type_representation \<tau>))"
    by (rule paper_ZF_R_type_invariant_action[OF tau_invariant])
  interpret Pair: paper_ZF_action_pair objects "paper_ZF_image_code ArrowBound encode arrows"
    Encoding.coded_source Encoding.coded_target Encoding.coded_compose Encoding.coded_identity
    "paper_ZF_rep_domain (type_representation \<sigma>)" "paper_ZF_rep_transport (type_representation \<sigma>)"
    "paper_ZF_rep_domain (type_representation \<tau>)" "paper_ZF_rep_transport (type_representation \<tau>)"
    by (unfold_locales; use sigma_action tau_action in
      \<open>auto simp: paper_action_def paper_action_axioms_def paper_category_def\<close>)
  show ?thesis
  proof (rule paper_subactionI[OF paper_ZF_R_type_invariant_action[OF arrow_invariant] Pair.paper_ZF_exponential_action])
    fix M
    assume "M \<in> objects"
    show "explode (paper_ZF_rep_domain (type_representation (Arr \<sigma> \<tau>)) M) \<subseteq>
        explode (paper_ZF_exponential_code (paper_ZF_image_code ArrowBound encode arrows)
          Encoding.coded_source Encoding.coded_target Encoding.coded_compose
          (paper_ZF_rep_domain (type_representation \<sigma>)) (paper_ZF_rep_transport (type_representation \<sigma>))
          (paper_ZF_rep_domain (type_representation \<tau>)) (paper_ZF_rep_transport (type_representation \<tau>)) M)"
      by (rule paper_ZF_R_premodel_arrow_domain_subset[OF rt])
  next
    fix h z
    assume "h \<in> Encoding.coded_arrows"
      and "z \<in> explode (paper_ZF_rep_domain (type_representation (Arr \<sigma> \<tau>)) (Encoding.coded_source h))"
    show "paper_ZF_rep_transport (type_representation (Arr \<sigma> \<tau>)) h z =
        paper_ZF_exponential_transport_code (paper_ZF_image_code ArrowBound encode arrows)
          Encoding.coded_source Encoding.coded_target Encoding.coded_compose
          (paper_ZF_rep_domain (type_representation \<sigma>)) h z"
      by (simp only: paper_ZF_R_premodel_arrow_transport[OF rt])
  qed
qed

end

end
