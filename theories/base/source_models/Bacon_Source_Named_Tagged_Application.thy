theory Bacon_Source_Named_Tagged_Application
  imports Bacon_Source_Named_Type_Tags Bacon_Source_Named_Denotation_Basics
begin

section \<open>Heterogeneous application congruence in the tagged construction\<close>

text \<open>
  If ⟦F⟧ᵍ = ⟦H⟧ʰ and ⟦A⟧ᵍ = ⟦B⟧ʰ, then
  ⟦FA⟧ᵍ = ⟦HB⟧ʰ, even when the initially displayed types are
  F:σ → τ and H:υ → ρ. Source: Bacon–Dorr Definition 3.1(ii.b),
  p.44, whose application clause does not require the displayed heads
  to have the same type in advance.

  Isabelle representation. A constructed value is the pair of its
  syntactic type and its old denotation. Equality of the tagged heads
  therefore gives σ → τ = υ → ρ, hence σ = υ and τ = ρ.
  Projecting the value coordinates supplies the two old equalities.
  The existing same-type application lemma then applies to the untagged
  adequate assignments. The output tags agree by the recovered τ = ρ.

  Status. This verifies the heterogeneous clause for the tagged
  construction inside a weak paper_db_bbk_structure. It assumes neither
  disjointness of the original domains nor full function spaces, and it
  does not claim the untagged construction satisfies a heterogeneous
  clause when original domains overlap. No named model is assumed.
\<close>

context paper_db_bbk_structure
begin

theorem paper_db_tagged_named_application_cong:
  assumes f_language: "named_in_language paper_logical_type signature G F (Arr \<sigma> \<tau>)"
    and a_language: "named_in_language paper_logical_type signature G A \<sigma>"
    and h_language: "named_in_language paper_logical_type signature K H (Arr \<upsilon> \<rho>)"
    and b_language: "named_in_language paper_logical_type signature K B \<upsilon>"
    and g_typed: "named_env_typed (named_tag_domain domain) G g"
    and j_typed: "named_env_typed (named_tag_domain domain) K j"
    and g_adequate: "named_adequate g (NApp F A)"
    and j_adequate: "named_adequate j (NApp H B)"
    and heads: "tagged_named_denote G g F = tagged_named_denote K j H"
    and arguments: "tagged_named_denote G g A = tagged_named_denote K j B"
  shows "tagged_named_denote G g (NApp F A) = tagged_named_denote K j (NApp H B)"
proof -
  have ft: "has_ntype paper_logical_type G F (Arr \<sigma> \<tau>)"
    using f_language unfolding named_in_language_def by (rule conjunct1)
  have at: "has_ntype paper_logical_type G A \<sigma>"
    using a_language unfolding named_in_language_def by (rule conjunct1)
  have ht: "has_ntype paper_logical_type K H (Arr \<upsilon> \<rho>)"
    using h_language unfolding named_in_language_def by (rule conjunct1)
  have bt: "has_ntype paper_logical_type K B \<upsilon>"
    using b_language unfolding named_in_language_def by (rule conjunct1)
  have head_tags: "fst (tagged_named_denote G g F) = fst (tagged_named_denote K j H)"
    by (rule arg_cong[where f=fst, OF heads])
  have arrow_types: "Arr \<sigma> \<tau> = Arr \<upsilon> \<rho>"
    using head_tags by (simp only: tagged_named_denote_eq[OF ft]
      tagged_named_denote_eq[OF ht] fst_conv)
  have input_type: "\<sigma> = \<upsilon>" and output_type: "\<tau> = \<rho>"
    using arrow_types by simp_all
  have heads_old: "named_denote G (named_untag_assignment g) F =
    named_denote K (named_untag_assignment j) H"
  proof -
    have projected: "snd (tagged_named_denote G g F) = snd (tagged_named_denote K j H)"
      by (rule arg_cong[where f=snd, OF heads])
    show ?thesis using projected
      by (simp only: tagged_named_denote_eq[OF ft] tagged_named_denote_eq[OF ht] snd_conv)
  qed
  have arguments_old: "named_denote G (named_untag_assignment g) A =
    named_denote K (named_untag_assignment j) B"
  proof -
    have projected: "snd (tagged_named_denote G g A) = snd (tagged_named_denote K j B)"
      by (rule arg_cong[where f=snd, OF arguments])
    show ?thesis using projected
      by (simp only: tagged_named_denote_eq[OF at] tagged_named_denote_eq[OF bt] snd_conv)
  qed
  have old_g_typed: "named_env_typed domain G (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF g_typed])
  have old_j_typed: "named_env_typed domain K (named_untag_assignment j)"
    by (rule named_untag_assignment_typed[OF j_typed])
  have old_g_adequate: "named_adequate (named_untag_assignment g) (NApp F A)"
    by (simp only: named_untag_assignment_adequate; rule g_adequate)
  have old_j_adequate: "named_adequate (named_untag_assignment j) (NApp H B)"
    by (simp only: named_untag_assignment_adequate; rule j_adequate)
  have h_same: "named_in_language paper_logical_type signature K H (Arr \<sigma> \<tau>)"
    using h_language by (simp only: input_type output_type)
  have b_same: "named_in_language paper_logical_type signature K B \<sigma>"
    using b_language by (simp only: input_type)
  have application_old: "named_denote G (named_untag_assignment g) (NApp F A) =
    named_denote K (named_untag_assignment j) (NApp H B)"
    by (rule paper_db_named_application_cong[OF f_language a_language h_same b_same
      old_g_typed old_j_typed old_g_adequate old_j_adequate heads_old arguments_old])
  have fa_type: "has_ntype paper_logical_type G (NApp F A) \<tau>"
    by (rule has_ntype.App[OF ft at])
  have hb_type: "has_ntype paper_logical_type K (NApp H B) \<rho>"
    by (rule has_ntype.App[OF ht bt])
  show ?thesis by (simp only: tagged_named_denote_eq[OF fa_type]
    tagged_named_denote_eq[OF hb_type] output_type application_old)
qed

end

end
