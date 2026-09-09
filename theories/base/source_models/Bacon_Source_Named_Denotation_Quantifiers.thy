theory Bacon_Source_Named_Denotation_Quantifiers
  imports Bacon_Source_Named_Quantifier_Instances
begin

section \<open>Truth of first-class named quantifiers\<close>

text \<open>
  For F:σ → t and fresh x:σ, V⟦∀σ F⟧ᴹᵍ holds exactly when
  V⟦Fx⟧ᴹᵍ[x↦a] holds for every a ∈ Dσ. The existential clause uses
  some a ∈ Dσ instead. Source: Bacon–Dorr Definition 3.1(iii.d–e).

  Representation: SAll and SEx remain first-class named logical constants.
  A shared completion of g supplies the source quantifier field; the
  preceding instance lemma identifies each updated named application.
  Status: proved in the weak source structure with explicit typing,
  adequacy and freshness guards. No named-model predicate or richness
  premise is assumed. Model-class equivalence and Γ erasure are separate.
\<close>

context paper_db_bbk_structure
begin

theorem paper_db_named_forall_truth:
  assumes language: "named_in_language paper_logical_type signature G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed domain G g"
    and adequate: "named_adequate g F"
    and n_type: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "valuation (named_denote G g (NApp (NLogical (SAll \<sigma>)) F)) =
    (\<forall>a \<in> domain \<sigma>. valuation (named_denote G (g(n := Some a)) (NApp F (NVar n))))"
proof -
  let ?h = "SOME h. named_completion domain G g h"
  let ?E = "named_to_source G [] F"
  have completion: "named_completion domain G g ?h"
    by (rule paper_db_named_chosen_completion[OF typed])
  obtain m where f_language:
    "sterm_in_language paper_logical_type signature (source_prefix G m) ?E (Arr \<sigma> Prop)"
    and index: "lookup (source_prefix G m) n = Some \<sigma>"
    by (rule paper_db_named_quantifier_frame[OF language n_type])
  have source_truth:
    "valuation (denote ?h (SApp (SLogical (SAll \<sigma>)) ?E)) =
      (\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a ?h) (SApp (sshift ?E) (SVar 0))))"
    by (rule valuation_forall[OF f_language paper_db_named_chosen_prefix[OF typed]])
  have instances: "\<And>a. a \<in> domain \<sigma> \<Longrightarrow>
    denote (pbbk_extend a ?h) (SApp (sshift ?E) (SVar 0)) =
      named_denote G (g(n := Some a)) (NApp F (NVar n))"
    by (rule paper_db_named_quantifier_instance[OF language f_language index
      n_type fresh typed adequate completion])
  have quantified:
    "(\<forall>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a ?h) (SApp (sshift ?E) (SVar 0)))) =
     (\<forall>a \<in> domain \<sigma>. valuation (named_denote G (g(n := Some a)) (NApp F (NVar n))))"
    by (rule ball_cong[OF refl]) (simp only: instances)
  show ?thesis using trans[OF source_truth quantified]
    by (simp only: named_denote_def named_to_source.simps)
qed

theorem paper_db_named_exists_truth:
  assumes language: "named_in_language paper_logical_type signature G F (Arr \<sigma> Prop)"
    and typed: "named_env_typed domain G g"
    and adequate: "named_adequate g F"
    and n_type: "G n = \<sigma>" and fresh: "n \<notin> named_fv F"
  shows "valuation (named_denote G g (NApp (NLogical (SEx \<sigma>)) F)) =
    (\<exists>a \<in> domain \<sigma>. valuation (named_denote G (g(n := Some a)) (NApp F (NVar n))))"
proof -
  let ?h = "SOME h. named_completion domain G g h"
  let ?E = "named_to_source G [] F"
  have completion: "named_completion domain G g ?h"
    by (rule paper_db_named_chosen_completion[OF typed])
  obtain m where f_language:
    "sterm_in_language paper_logical_type signature (source_prefix G m) ?E (Arr \<sigma> Prop)"
    and index: "lookup (source_prefix G m) n = Some \<sigma>"
    by (rule paper_db_named_quantifier_frame[OF language n_type])
  have source_truth:
    "valuation (denote ?h (SApp (SLogical (SEx \<sigma>)) ?E)) =
      (\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a ?h) (SApp (sshift ?E) (SVar 0))))"
    by (rule valuation_exists[OF f_language paper_db_named_chosen_prefix[OF typed]])
  have instances: "\<And>a. a \<in> domain \<sigma> \<Longrightarrow>
    denote (pbbk_extend a ?h) (SApp (sshift ?E) (SVar 0)) =
      named_denote G (g(n := Some a)) (NApp F (NVar n))"
    by (rule paper_db_named_quantifier_instance[OF language f_language index
      n_type fresh typed adequate completion])
  have quantified:
    "(\<exists>a \<in> domain \<sigma>. valuation (denote (pbbk_extend a ?h) (SApp (sshift ?E) (SVar 0)))) =
     (\<exists>a \<in> domain \<sigma>. valuation (named_denote G (g(n := Some a)) (NApp F (NVar n))))"
    by (rule bex_cong[OF refl]) (simp only: instances)
  show ?thesis using trans[OF source_truth quantified]
    by (simp only: named_denote_def named_to_source.simps)
qed

end

end
