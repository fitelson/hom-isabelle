theory Bacon_Source_Named_Denotation_Basics
  imports Bacon_Source_Named_Completion_Denotation
begin

section \<open>Application and primitive truth for adequate named assignments\<close>

text \<open>
  If ⟦F⟧ᴹᵍ = ⟦H⟧ᴹʰ and ⟦A⟧ᴹᵍ = ⟦B⟧ᴹʰ, application
  congruence gives ⟦FA⟧ᴹᵍ = ⟦HB⟧ᴹʰ. The primitive ¬, ∧, ∨,
  and =σ then have the truth conditions of Bacon–Dorr Definition 3.1.
  Identity is actual equality of denotations, not Leibniz equivalence.

  Representation: named_denote selects a completion using G and g only,
  independently of the term. Thus each parent and its subterms use the
  same completion. Finite support supplies the common source frames.
  We retain adequacy guards matching the intended partial interpretation;
  the deterministic totalization permits these particular calculations
  even without those guards, but that is not a new source convention.

  Status: derived solely in paper_db_bbk_structure. No independent named
  model is assumed. Quantifiers, model assembly, and Γ erasure are not
  proved here; there is no primitive or defined implication field.
\<close>

context paper_db_bbk_structure
begin

lemma paper_db_named_language_prefix:
  assumes language: "named_in_language paper_logical_type signature G A \<sigma>"
    and bound: "source_free_bound (named_to_source G [] A) \<le> m"
  shows "sterm_in_language paper_logical_type signature (source_prefix G m)
    (named_to_source G [] A) \<sigma>"
proof -
  have global_language:
    "sgterm_in_language paper_logical_type signature G (named_to_source G [] A) \<sigma>"
    using named_to_source_global_language[where ns="[]", OF language]
    by (simp only: named_stack_stock.simps)
  show ?thesis by (rule source_language_in_prefix[OF global_language bound])
qed

lemma paper_db_named_pair_prefix:
  assumes left: "named_in_language paper_logical_type signature G A \<sigma>"
    and right: "named_in_language paper_logical_type signature G B \<tau>"
  obtains m where
    "sterm_in_language paper_logical_type signature (source_prefix G m)
      (named_to_source G [] A) \<sigma>"
    "sterm_in_language paper_logical_type signature (source_prefix G m)
      (named_to_source G [] B) \<tau>"
proof -
  let ?m = "max (source_free_bound (named_to_source G [] A))
    (source_free_bound (named_to_source G [] B))"
  have first: "sterm_in_language paper_logical_type signature (source_prefix G ?m)
    (named_to_source G [] A) \<sigma>"
    by (rule paper_db_named_language_prefix[OF left]) simp
  have second: "sterm_in_language paper_logical_type signature (source_prefix G ?m)
    (named_to_source G [] B) \<tau>"
    by (rule paper_db_named_language_prefix[OF right]) simp
  show thesis by (rule that[OF first second])
qed

lemma paper_db_named_chosen_prefix:
  assumes typed: "named_env_typed domain G g"
  shows "pbbk_env_typed domain (source_prefix G m)
    (SOME h. named_completion domain G g h)"
  by (rule paper_global_env_prefix[OF
    named_completion_typed[OF paper_db_named_chosen_completion[OF typed]]])

theorem paper_db_named_application_cong:
  assumes f_language: "named_in_language paper_logical_type signature G F (Arr \<sigma> \<tau>)"
    and a_language: "named_in_language paper_logical_type signature G A \<sigma>"
    and h_language: "named_in_language paper_logical_type signature K H (Arr \<sigma> \<tau>)"
    and b_language: "named_in_language paper_logical_type signature K B \<sigma>"
    and g_typed: "named_env_typed domain G g"
    and j_typed: "named_env_typed domain K j"
    and g_adequate: "named_adequate g (NApp F A)"
    and j_adequate: "named_adequate j (NApp H B)"
    and heads: "named_denote G g F = named_denote K j H"
    and arguments: "named_denote G g A = named_denote K j B"
  shows "named_denote G g (NApp F A) = named_denote K j (NApp H B)"
proof -
  obtain m where f_type: "sterm_in_language paper_logical_type signature (source_prefix G m)
    (named_to_source G [] F) (Arr \<sigma> \<tau>)"
    and a_type: "sterm_in_language paper_logical_type signature (source_prefix G m)
    (named_to_source G [] A) \<sigma>"
    by (rule paper_db_named_pair_prefix[OF f_language a_language])
  obtain n where h_type: "sterm_in_language paper_logical_type signature (source_prefix K n)
    (named_to_source K [] H) (Arr \<sigma> \<tau>)"
    and b_type: "sterm_in_language paper_logical_type signature (source_prefix K n)
    (named_to_source K [] B) \<sigma>"
    by (rule paper_db_named_pair_prefix[OF h_language b_language])
  have eq_heads:
    "denote (SOME h. named_completion domain G g h) (named_to_source G [] F) =
     denote (SOME h. named_completion domain K j h) (named_to_source K [] H)"
    using heads unfolding named_denote_def .
  have eq_arguments:
    "denote (SOME h. named_completion domain G g h) (named_to_source G [] A) =
     denote (SOME h. named_completion domain K j h) (named_to_source K [] B)"
    using arguments unfolding named_denote_def .
  have result:
    "denote (SOME h. named_completion domain G g h)
       (SApp (named_to_source G [] F) (named_to_source G [] A)) =
     denote (SOME h. named_completion domain K j h)
       (SApp (named_to_source K [] H) (named_to_source K [] B))"
    by (rule denote_application_cong[OF f_type a_type h_type b_type
      paper_db_named_chosen_prefix[OF g_typed] paper_db_named_chosen_prefix[OF j_typed]
      eq_heads eq_arguments])
  show ?thesis using result by (simp only: named_denote_def named_to_source.simps)
qed

theorem paper_db_named_neg_truth:
  assumes language: "named_in_language paper_logical_type signature G A Prop"
    and typed: "named_env_typed domain G g"
    and adequate: "named_adequate g A"
  shows "valuation (named_denote G g (NApp (NLogical SNot) A)) =
    (\<not> valuation (named_denote G g A))"
proof -
  let ?m = "source_free_bound (named_to_source G [] A)"
  have a_type: "sterm_in_language paper_logical_type signature (source_prefix G ?m)
    (named_to_source G [] A) Prop"
    by (rule paper_db_named_language_prefix[OF language]) (rule order_refl)
  have result:
    "valuation (denote (SOME h. named_completion domain G g h)
       (paper_not (named_to_source G [] A))) =
     (\<not> valuation (denote (SOME h. named_completion domain G g h)
       (named_to_source G [] A)))"
    by (rule valuation_neg[OF a_type paper_db_named_chosen_prefix[OF typed]])
  show ?thesis using result
    by (simp only: named_denote_def named_to_source.simps paper_not_def)
qed

theorem paper_db_named_conj_truth:
  assumes left: "named_in_language paper_logical_type signature G A Prop"
    and right: "named_in_language paper_logical_type signature G B Prop"
    and typed: "named_env_typed domain G g"
    and adequate: "named_adequate g (NApp (NApp (NLogical SAnd) A) B)"
  shows "valuation (named_denote G g (NApp (NApp (NLogical SAnd) A) B)) =
    (valuation (named_denote G g A) \<and> valuation (named_denote G g B))"
proof -
  obtain m where a_type: "sterm_in_language paper_logical_type signature (source_prefix G m)
    (named_to_source G [] A) Prop"
    and b_type: "sterm_in_language paper_logical_type signature (source_prefix G m)
    (named_to_source G [] B) Prop"
    by (rule paper_db_named_pair_prefix[OF left right])
  have result:
    "valuation (denote (SOME h. named_completion domain G g h)
       (paper_and (named_to_source G [] A) (named_to_source G [] B))) =
     (valuation (denote (SOME h. named_completion domain G g h) (named_to_source G [] A)) \<and>
      valuation (denote (SOME h. named_completion domain G g h) (named_to_source G [] B)))"
    by (rule valuation_conj[OF a_type b_type paper_db_named_chosen_prefix[OF typed]])
  show ?thesis using result
    by (simp only: named_denote_def named_to_source.simps paper_and_def)
qed

theorem paper_db_named_disj_truth:
  assumes left: "named_in_language paper_logical_type signature G A Prop"
    and right: "named_in_language paper_logical_type signature G B Prop"
    and typed: "named_env_typed domain G g"
    and adequate: "named_adequate g (NApp (NApp (NLogical SOr) A) B)"
  shows "valuation (named_denote G g (NApp (NApp (NLogical SOr) A) B)) =
    (valuation (named_denote G g A) \<or> valuation (named_denote G g B))"
proof -
  obtain m where a_type: "sterm_in_language paper_logical_type signature (source_prefix G m)
    (named_to_source G [] A) Prop"
    and b_type: "sterm_in_language paper_logical_type signature (source_prefix G m)
    (named_to_source G [] B) Prop"
    by (rule paper_db_named_pair_prefix[OF left right])
  have result:
    "valuation (denote (SOME h. named_completion domain G g h)
       (paper_or (named_to_source G [] A) (named_to_source G [] B))) =
     (valuation (denote (SOME h. named_completion domain G g h) (named_to_source G [] A)) \<or>
      valuation (denote (SOME h. named_completion domain G g h) (named_to_source G [] B)))"
    by (rule valuation_disj[OF a_type b_type paper_db_named_chosen_prefix[OF typed]])
  show ?thesis using result
    by (simp only: named_denote_def named_to_source.simps paper_or_def)
qed

theorem paper_db_named_identity_truth:
  assumes left: "named_in_language paper_logical_type signature G A \<sigma>"
    and right: "named_in_language paper_logical_type signature G B \<sigma>"
    and typed: "named_env_typed domain G g"
    and adequate: "named_adequate g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)"
  shows "valuation (named_denote G g (NApp (NApp (NLogical (SEq \<sigma>)) A) B)) =
    (named_denote G g A = named_denote G g B)"
proof -
  obtain m where a_type: "sterm_in_language paper_logical_type signature (source_prefix G m)
    (named_to_source G [] A) \<sigma>"
    and b_type: "sterm_in_language paper_logical_type signature (source_prefix G m)
    (named_to_source G [] B) \<sigma>"
    by (rule paper_db_named_pair_prefix[OF left right])
  have result:
    "valuation (denote (SOME h. named_completion domain G g h)
       (SApp (SApp (SLogical (SEq \<sigma>)) (named_to_source G [] A))
         (named_to_source G [] B))) =
     (denote (SOME h. named_completion domain G g h) (named_to_source G [] A) =
      denote (SOME h. named_completion domain G g h) (named_to_source G [] B))"
    by (rule valuation_identity[OF a_type b_type paper_db_named_chosen_prefix[OF typed]])
  show ?thesis using result by (simp only: named_denote_def named_to_source.simps)
qed

end

end
