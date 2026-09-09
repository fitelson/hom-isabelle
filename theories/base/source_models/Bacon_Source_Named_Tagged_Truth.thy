theory Bacon_Source_Named_Tagged_Truth
  imports Bacon_Source_Named_Tagged_Application Bacon_Source_Named_Tagged_Locality
begin

section \<open>Primitive truth clauses on the tagged carrier\<close>

text \<open>
  Define V′⟨σ,a⟩ = V(a). The tagged interpretation retains the truth
  conditions of ¬, ∧, ∨ and =σ. For identity, both operands have tag σ,
  so equality of tagged denotations is exactly equality of their values.
  Source: Bacon–Dorr Definition 3.1(iii.a–c,f), pp.43–44.
  Representation: V′ is the displayed function λv. valuation (snd v).
  Status: constructed clauses in the weak source structure, not an assumed
  named model; the original domains need not be disjoint. There is no
  primitive implication clause or claim identifying implication operators.
\<close>

context paper_db_bbk_structure
begin

theorem paper_db_tagged_named_neg_truth:
  assumes language: "named_in_language paper_logical_type signature G A Prop"
    and typed: "named_env_typed (named_tag_domain domain) G g"
    and adequate: "named_adequate g A"
  shows "valuation (snd (tagged_named_denote G g (NApp (NLogical SNot) A))) =
    (\<not> valuation (snd (tagged_named_denote G g A)))"
proof -
  have old_typed: "named_env_typed domain G (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF typed])
  have old_adequate: "named_adequate (named_untag_assignment g) A"
    by (rule iffD2[OF named_untag_assignment_adequate adequate])
  have old: "valuation (named_denote G (named_untag_assignment g) (NApp (NLogical SNot) A)) =
    (\<not> valuation (named_denote G (named_untag_assignment g) A))"
    by (rule paper_db_named_neg_truth[OF language old_typed old_adequate])
  show ?thesis using old by (simp only: tagged_named_denote_def snd_conv)
qed

theorem paper_db_tagged_named_conj_truth:
  assumes left: "named_in_language paper_logical_type signature G A Prop"
    and right: "named_in_language paper_logical_type signature G B Prop"
    and typed: "named_env_typed (named_tag_domain domain) G g"
    and adequate: "named_adequate g (NApp (NApp (NLogical SAnd) A) B)"
  shows "valuation (snd (tagged_named_denote G g (NApp (NApp (NLogical SAnd) A) B))) =
    (valuation (snd (tagged_named_denote G g A)) \<and>
     valuation (snd (tagged_named_denote G g B)))"
proof -
  have old_typed: "named_env_typed domain G (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF typed])
  have old_adequate: "named_adequate (named_untag_assignment g) (NApp (NApp (NLogical SAnd) A) B)"
    by (rule iffD2[OF named_untag_assignment_adequate adequate])
  have old: "valuation (named_denote G (named_untag_assignment g) (NApp (NApp (NLogical SAnd) A) B)) =
    (valuation (named_denote G (named_untag_assignment g) A) \<and>
     valuation (named_denote G (named_untag_assignment g) B))"
    by (rule paper_db_named_conj_truth[OF left right old_typed old_adequate])
  show ?thesis using old by (simp only: tagged_named_denote_def snd_conv)
qed

theorem paper_db_tagged_named_disj_truth:
  assumes left: "named_in_language paper_logical_type signature G A Prop"
    and right: "named_in_language paper_logical_type signature G B Prop"
    and typed: "named_env_typed (named_tag_domain domain) G g"
    and adequate: "named_adequate g (NApp (NApp (NLogical SOr) A) B)"
  shows "valuation (snd (tagged_named_denote G g (NApp (NApp (NLogical SOr) A) B))) =
    (valuation (snd (tagged_named_denote G g A)) \<or>
     valuation (snd (tagged_named_denote G g B)))"
proof -
  have old_typed: "named_env_typed domain G (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF typed])
  have old_adequate: "named_adequate (named_untag_assignment g) (NApp (NApp (NLogical SOr) A) B)"
    by (rule iffD2[OF named_untag_assignment_adequate adequate])
  have old: "valuation (named_denote G (named_untag_assignment g) (NApp (NApp (NLogical SOr) A) B)) =
    (valuation (named_denote G (named_untag_assignment g) A) \<or>
     valuation (named_denote G (named_untag_assignment g) B))"
    by (rule paper_db_named_disj_truth[OF left right old_typed old_adequate])
  show ?thesis using old by (simp only: tagged_named_denote_def snd_conv)
qed

theorem paper_db_tagged_named_identity_truth:
  assumes left: "named_in_language paper_logical_type signature G A \<sigma>"
    and right: "named_in_language paper_logical_type signature G B \<sigma>"
    and typed: "named_env_typed (named_tag_domain domain) G g"
    and adequate: "named_adequate g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)"
  shows "valuation (snd (tagged_named_denote G g (NApp (NApp (NLogical (SEq \<sigma>)) A) B))) =
    (tagged_named_denote G g A = tagged_named_denote G g B)"
proof -
  have old_typed: "named_env_typed domain G (named_untag_assignment g)"
    by (rule named_untag_assignment_typed[OF typed])
  have old_adequate: "named_adequate (named_untag_assignment g) (NApp (NApp (NLogical (SEq \<sigma>)) A) B)"
    by (rule iffD2[OF named_untag_assignment_adequate adequate])
  have old: "valuation (named_denote G (named_untag_assignment g) (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) =
    (named_denote G (named_untag_assignment g) A = named_denote G (named_untag_assignment g) B)"
    by (rule paper_db_named_identity_truth[OF left right old_typed old_adequate])
  have tagged_equality:
    "(tagged_named_denote G g A = tagged_named_denote G g B) =
     (named_denote G (named_untag_assignment g) A = named_denote G (named_untag_assignment g) B)"
    by (simp add: tagged_named_denote_language_eq[OF left]
      tagged_named_denote_language_eq[OF right])
  show ?thesis by (subst tagged_equality)
    (simp only: tagged_named_denote_def snd_conv old)
qed

end

end
