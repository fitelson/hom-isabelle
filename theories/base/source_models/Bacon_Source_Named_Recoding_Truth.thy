theory Bacon_Source_Named_Recoding_Truth
  imports Bacon_Source_Named_Recoding_Structure
begin

section \<open>Truth is preserved by an injective change of semantic carrier\<close>

text \<open>
  Replace Dσ by f[Dσ], where f is injective. Interpret A under g by
  f(⟦A⟧ᵐᵃᵖ⁽ᶠ⁻¹⁾ᵍ), and value v by V(f⁻¹(v)). The composite
  valuation therefore recovers the old truth value. Source role:
  carrier transport for Bacon–Dorr Definition 3.1, pp.43–44.

  Representation: inv f is used only with its proved inverse equations.
  Surjectivity onto the new ambient carrier is not assumed; typed
  assignments take values in the image domains. Status: primitive
  Boolean and actual-identity clauses only, not a model assembly.
\<close>

context paper_named_bbk_model
begin

theorem named_recode_neg_truth:
  assumes injective: "inj f"
    and language: "named_in_language paper_logical_type signature stock A Prop"
    and typed: "named_env_typed (named_image_domain f domain) stock g"
    and adequate: "named_adequate g A"
  shows "named_recode_valuation f (named_recode_denote f g (NApp (NLogical SNot) A)) =
    (\<not> named_recode_valuation f (named_recode_denote f g A))"
proof -
  have old_typed: "named_env_typed domain stock (named_map_assignment (inv f) g)"
    by (rule named_map_assignment_inv_typed[OF injective typed])
  have old_adequate: "named_adequate (named_map_assignment (inv f) g) A"
    by (rule iffD2[OF named_map_assignment_adequate adequate])
  show ?thesis by (simp only: named_recode_truth[OF injective];
    rule valuation_neg[OF language old_typed old_adequate])
qed

theorem named_recode_conj_truth:
  assumes injective: "inj f"
    and left: "named_in_language paper_logical_type signature stock A Prop"
    and right: "named_in_language paper_logical_type signature stock B Prop"
    and typed: "named_env_typed (named_image_domain f domain) stock g"
    and adequate_A: "named_adequate g A" and adequate_B: "named_adequate g B"
  shows "named_recode_valuation f (named_recode_denote f g (NApp (NApp (NLogical SAnd) A) B)) =
    (named_recode_valuation f (named_recode_denote f g A) \<and>
     named_recode_valuation f (named_recode_denote f g B))"
proof -
  have old_typed: "named_env_typed domain stock (named_map_assignment (inv f) g)"
    by (rule named_map_assignment_inv_typed[OF injective typed])
  have old_A: "named_adequate (named_map_assignment (inv f) g) A"
    by (rule iffD2[OF named_map_assignment_adequate adequate_A])
  have old_B: "named_adequate (named_map_assignment (inv f) g) B"
    by (rule iffD2[OF named_map_assignment_adequate adequate_B])
  show ?thesis by (simp only: named_recode_truth[OF injective];
    rule valuation_conj[OF left right old_typed old_A old_B])
qed

theorem named_recode_disj_truth:
  assumes injective: "inj f"
    and left: "named_in_language paper_logical_type signature stock A Prop"
    and right: "named_in_language paper_logical_type signature stock B Prop"
    and typed: "named_env_typed (named_image_domain f domain) stock g"
    and adequate_A: "named_adequate g A" and adequate_B: "named_adequate g B"
  shows "named_recode_valuation f (named_recode_denote f g (NApp (NApp (NLogical SOr) A) B)) =
    (named_recode_valuation f (named_recode_denote f g A) \<or>
     named_recode_valuation f (named_recode_denote f g B))"
proof -
  have old_typed: "named_env_typed domain stock (named_map_assignment (inv f) g)"
    by (rule named_map_assignment_inv_typed[OF injective typed])
  have old_A: "named_adequate (named_map_assignment (inv f) g) A"
    by (rule iffD2[OF named_map_assignment_adequate adequate_A])
  have old_B: "named_adequate (named_map_assignment (inv f) g) B"
    by (rule iffD2[OF named_map_assignment_adequate adequate_B])
  show ?thesis by (simp only: named_recode_truth[OF injective];
    rule valuation_disj[OF left right old_typed old_A old_B])
qed

theorem named_recode_identity_truth:
  assumes injective: "inj f"
    and left: "named_in_language paper_logical_type signature stock A \<sigma>"
    and right: "named_in_language paper_logical_type signature stock B \<sigma>"
    and typed: "named_env_typed (named_image_domain f domain) stock g"
    and adequate_A: "named_adequate g A" and adequate_B: "named_adequate g B"
  shows "named_recode_valuation f (named_recode_denote f g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) =
    (named_recode_denote f g A = named_recode_denote f g B)"
proof -
  have old_typed: "named_env_typed domain stock (named_map_assignment (inv f) g)"
    by (rule named_map_assignment_inv_typed[OF injective typed])
  have old_A: "named_adequate (named_map_assignment (inv f) g) A"
    by (rule iffD2[OF named_map_assignment_adequate adequate_A])
  have old_B: "named_adequate (named_map_assignment (inv f) g) B"
    by (rule iffD2[OF named_map_assignment_adequate adequate_B])
  have equality:
    "(named_recode_denote f g A = named_recode_denote f g B) =
     (denote (named_map_assignment (inv f) g) A = denote (named_map_assignment (inv f) g) B)"
    by (simp only: named_recode_denote_def inj_eq[OF injective])
  show ?thesis by (simp only: named_recode_truth[OF injective] equality;
    rule valuation_identity[OF left right old_typed old_A old_B])
qed

end

end
