theory Bacon_Source_Relational_Quasi_Fregean_Box
  imports Bacon_Source_Relational_Tautology_Profile
begin

section \<open>Necessity in a quasi-Fregean category\<close>

text \<open>
  At M,g, □P holds exactly when every outgoing homomorphism makes
  the image of ⟦P⟧Mᵍ true. The forward identification uses the
  actual identity truth clause for Figure 1's □; the converse uses
  quasi-Fregeanness to recover equality from equal truth profiles.

  The category may have a selected arrow collection and need not
  contain all homomorphisms. Neither C validity nor Modalized
  Functionality is assumed here. Source: Definitions 3.10–3.11 and
  the last paragraph of n.73, p.52.
\<close>

theorem paper_R_quasi_fregean_box_profile:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and quasi: "paper_bbk_quasi_fregean_on Obj Arrows"
    and object: "M \<in> Obj"
    and language: "paper_R_in_language \<Sigma> G P Prop"
    and typed: "named_env_typed (paper_bbk_domain M) G g"
    and adequate: "named_adequate g P"
  shows "paper_bbk_valuation M (paper_bbk_denote M g (paper_R_named_box G P)) \<longleftrightarrow>
    paper_bbk_truth_profile_on Arrows M (paper_bbk_denote M g P) =
      paper_outgoing Arrows paper_arrow_source M"
proof -
  have valid: "paper_R_bbk_data_valid \<Sigma> G M"
    by (rule paper_R_bbk_subcategory_models[OF category object])
  interpret Model: paper_R_bbk_model \<Sigma> G "paper_bbk_domain M"
    "paper_bbk_denote M" "paper_bbk_valuation M"
    by (rule paper_R_bbk_data_model[OF valid])
  let ?A = "named_paper_or P (named_paper_not P)"
  let ?p = "paper_bbk_denote M g P"
  let ?a = "paper_bbk_denote M g ?A"
  have al: "paper_R_in_language \<Sigma> G ?A Prop"
    by (rule paper_R_named_or_language[OF language paper_R_named_not_language[OF language]])
  have aa: "named_adequate g ?A" using adequate
    by (simp add: named_adequate_def named_paper_primitive_fv)
  have pm: "?p \<in> paper_bbk_domain M Prop" by (rule Model.denote_type[OF language typed adequate])
  have am: "?a \<in> paper_bbk_domain M Prop" by (rule Model.denote_type[OF al typed aa])
  have injective: "inj_on (paper_bbk_truth_profile_on Arrows M) (paper_bbk_domain M Prop)"
    using quasi object unfolding paper_bbk_quasi_fregean_on_def by blast
  have comparison: "(?p = ?a) \<longleftrightarrow>
    paper_bbk_truth_profile_on Arrows M ?p = paper_bbk_truth_profile_on Arrows M ?a"
  proof
    assume same: "?p = ?a"
    show "paper_bbk_truth_profile_on Arrows M ?p = paper_bbk_truth_profile_on Arrows M ?a"
      by (simp only: same)
  next
    assume profiles: "paper_bbk_truth_profile_on Arrows M ?p = paper_bbk_truth_profile_on Arrows M ?a"
    show "?p = ?a" by (rule inj_onD[OF injective profiles pm am])
  qed
  show ?thesis by (simp only: Model.paper_R_named_box_truth[OF language typed adequate]
    comparison paper_R_tautology_profile[OF category language typed adequate])
qed

corollary paper_R_quasi_fregean_box_truth:
  assumes category: "paper_R_bbk_subcategory \<Sigma> G Obj Arrows"
    and quasi: "paper_bbk_quasi_fregean_on Obj Arrows" and object: "M \<in> Obj"
    and language: "paper_R_in_language \<Sigma> G P Prop"
    and typed: "named_env_typed (paper_bbk_domain M) G g" and adequate: "named_adequate g P"
  shows "paper_bbk_valuation M (paper_bbk_denote M g (paper_R_named_box G P)) \<longleftrightarrow>
    (\<forall>h\<in>Arrows. paper_arrow_source h = M \<longrightarrow>
      paper_bbk_valuation (paper_arrow_target h) (paper_arrow_map h Prop (paper_bbk_denote M g P)))"
  by (simp only: paper_R_quasi_fregean_box_profile[OF category quasi object language typed adequate]
    set_eq_iff paper_bbk_truth_profile_on_member paper_outgoing_member; blast)

end
