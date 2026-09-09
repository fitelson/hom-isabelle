theory Bacon_Source_Relational_Quasi_Fregean_Denotation
  imports Bacon_Source_Relational_Subcategory Bacon_Source_BBK_Selected_Truth_Profile
begin

section \<open>Common truth equivalence implies common denotation equality\<close>

text \<open>
  Suppose 𝒞 is a quasi-Fregean R BBK category and P,Q:t agree
  in truth at every object under every typed partial assignment
  adequate for both formulas. Then ⟦P⟧Mᵍ=⟦Q⟧Mᵍ at each
  such object and assignment.
  Source: the Propositional Equivalence part of Theorem 3.12,
  Bacon–Dorr pp.51–52, using Definitions 3.10–3.11.

  Fix M,g and transport g along each h:M→N. The common truth
  hypothesis applies at N to h·g. Interpretation preservation gives
  equality of the two truth profiles at M, and quasi-Fregeanness
  separates their denotations. Truth is not assumed preserved by h.
  No total assignment, canonicality, full-arrow collection or C proof
  judgment is needed. This is the semantic closure ingredient, not
  a proof of C soundness or of existence of such a category.
\<close>

theorem paper_R_quasi_fregean_denotation:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and fregean: "paper_bbk_quasi_fregean_on Obj Arrows"
    and pl: "paper_R_in_language \<Sigma> G P Prop"
    and ql: "paper_R_in_language \<Sigma> G Q Prop"
    and common: "\<And>N k. N \<in> Obj \<Longrightarrow>
      named_env_typed (paper_bbk_domain N) G k \<Longrightarrow>
      named_adequate k P \<Longrightarrow> named_adequate k Q \<Longrightarrow>
      paper_bbk_valuation N (paper_bbk_denote N k P) =
        paper_bbk_valuation N (paper_bbk_denote N k Q)"
    and object: "M \<in> Obj"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and pa: "named_adequate g P" and qa: "named_adequate g Q"
  shows "paper_bbk_denote M g P = paper_bbk_denote M g Q"
proof -
  have valid: "paper_R_bbk_data_valid \<Sigma> G M"
    by (rule paper_R_bbk_subcategory_models[OF category object])
  have pm: "paper_bbk_denote M g P \<in> paper_bbk_domain M Prop"
    by (rule paper_R_bbk_data_denote_type[OF valid pl typed pa])
  have qm: "paper_bbk_denote M g Q \<in> paper_bbk_domain M Prop"
    by (rule paper_R_bbk_data_denote_type[OF valid ql typed qa])
  have profiles: "paper_bbk_truth_profile_on Arrows M (paper_bbk_denote M g P) =
    paper_bbk_truth_profile_on Arrows M (paper_bbk_denote M g Q)"
  proof (rule iffD2[OF paper_bbk_truth_profile_on_eq_iff], intro ballI impI)
    fix h
    assume arrow: "h \<in> Arrows" and source: "paper_arrow_source h = M"
    have selected: "h \<in> paper_R_bbk_arrows \<Sigma> G Obj"
      by (rule paper_R_bbk_subcategory_arrow[OF category arrow])
    have target: "paper_arrow_target h \<in> Obj"
      by (rule paper_typed_arrows_target[OF paper_R_bbk_arrows_typed[OF selected]])
    have hom: "paper_R_bbk_homomorphism \<Sigma> G (paper_bbk_domain M) (paper_bbk_denote M)
      (paper_bbk_domain (paper_arrow_target h)) (paper_bbk_denote (paper_arrow_target h))
      (paper_arrow_map h)"
      using paper_R_bbk_data_morphism_raw[OF paper_R_bbk_arrows_morphism[OF selected]]
      by (simp only: source)
    let ?k = "paper_hom_assignment G (paper_arrow_map h) g"
    have kt: "named_env_typed (paper_bbk_domain (paper_arrow_target h)) G ?k"
      by (rule paper_R_bbk_homomorphism_assignment_typed[OF hom typed])
    have kp: "named_adequate ?k P"
      by (rule paper_R_bbk_homomorphism_assignment_adequate[OF pa])
    have kq: "named_adequate ?k Q"
      by (rule paper_R_bbk_homomorphism_assignment_adequate[OF qa])
    have hp: "paper_arrow_map h Prop (paper_bbk_denote M g P) =
      paper_bbk_denote (paper_arrow_target h) ?k P"
      by (rule paper_R_bbk_homomorphism_denote[OF hom pl typed pa])
    have hq: "paper_arrow_map h Prop (paper_bbk_denote M g Q) =
      paper_bbk_denote (paper_arrow_target h) ?k Q"
      by (rule paper_R_bbk_homomorphism_denote[OF hom ql typed qa])
    show "paper_bbk_valuation (paper_arrow_target h)
        (paper_arrow_map h Prop (paper_bbk_denote M g P)) =
      paper_bbk_valuation (paper_arrow_target h)
        (paper_arrow_map h Prop (paper_bbk_denote M g Q))"
      by (simp only: hp hq; rule common[OF target kt kp kq])
  qed
  have injective: "inj_on (paper_bbk_truth_profile_on Arrows M) (paper_bbk_domain M Prop)"
    using fregean object unfolding paper_bbk_quasi_fregean_on_def by blast
  show ?thesis by (rule inj_onD[OF injective profiles pm qm])
qed

end
