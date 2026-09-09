theory Bacon_Source_Named_Tagged_Locality
  imports Bacon_Source_Named_Type_Tags Bacon_Source_Named_Conversion_Denotation
begin

section \<open>Locality and guarded conversion after type tagging\<close>

text \<open>
  Tagged values are ⟨σ,⟦A⟧ᴹᵍ⟩ for A:σ. Equal partial assignments
  on FV(A) give equal values, and a guarded conversion A ≡βη B preserves
  both the type tag and its denotation. Source: Definition 3.1(ii.c–d).
  Representation: remove assignment tags, apply the proved untagged
  clause, then restore the common syntactic type.
  Status: weak source structures only; no original-domain disjointness,
  named-model premise, or unrestricted-signature conversion is assumed.
\<close>

context paper_db_bbk_structure
begin

theorem paper_db_tagged_named_locality:
  assumes language: "named_in_language paper_logical_type signature G A \<sigma>"
    and first: "named_env_typed (named_tag_domain domain) G g"
    and second: "named_env_typed (named_tag_domain domain) G h"
    and ga: "named_adequate g A" and ha: "named_adequate h A"
    and agree: "\<And>n. n \<in> named_fv A \<Longrightarrow> g n = h n"
  shows "tagged_named_denote G g A = tagged_named_denote G h A"
proof -
  have gt: "named_env_typed domain G (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF first])
  have ht: "named_env_typed domain G (named_untag_assignment h)"
    by (rule named_untag_assignment_typed[OF second])
  have gu: "named_adequate (named_untag_assignment g) A"
    by (rule iffD2[OF named_untag_assignment_adequate ga])
  have hu: "named_adequate (named_untag_assignment h) A"
    by (rule iffD2[OF named_untag_assignment_adequate ha])
  have old: "named_denote G (named_untag_assignment g) A =
    named_denote G (named_untag_assignment h) A"
  proof (rule paper_db_named_denote_locality[OF language gt ht gu hu])
    fix n
    assume member: "n \<in> named_fv A"
    show "named_untag_assignment g n = named_untag_assignment h n"
      by (simp only: named_untag_assignment_def agree[OF member])
  qed
  show ?thesis by (simp only: tagged_named_denote_def old)
qed

theorem paper_db_tagged_named_conversion:
  assumes conversion: "named_beta_eta_in_language paper_logical_type signature G \<sigma> A B"
    and typed: "named_env_typed (named_tag_domain domain) G g"
    and adequate_A: "named_adequate g A" and adequate_B: "named_adequate g B"
  shows "tagged_named_denote G g A = tagged_named_denote G g B"
proof -
  have languages: "named_in_language paper_logical_type signature G A \<sigma> \<and>
    named_in_language paper_logical_type signature G B \<sigma>"
    by (rule named_beta_eta_languages[OF conversion])
  have left: "named_in_language paper_logical_type signature G A \<sigma>"
    by (rule conjunct1[OF languages])
  have right: "named_in_language paper_logical_type signature G B \<sigma>"
    by (rule conjunct2[OF languages])
  have old_typed: "named_env_typed domain G (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF typed])
  have old_A: "named_adequate (named_untag_assignment g) A"
    by (rule iffD2[OF named_untag_assignment_adequate adequate_A])
  have old_B: "named_adequate (named_untag_assignment g) B"
    by (rule iffD2[OF named_untag_assignment_adequate adequate_B])
  have old: "named_denote G (named_untag_assignment g) A =
    named_denote G (named_untag_assignment g) B"
    by (rule paper_db_named_conversion_denote[OF conversion old_typed old_A old_B])
  show ?thesis by (simp only: tagged_named_denote_language_eq[OF left]
    tagged_named_denote_language_eq[OF right] old)
qed

end

end
