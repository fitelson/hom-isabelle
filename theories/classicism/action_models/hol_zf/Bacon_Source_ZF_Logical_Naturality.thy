theory Bacon_Source_ZF_Logical_Naturality
  imports Bacon_Source_ZF_Logical_Values Bacon_Source_ZF_Exponential_Transport
begin

section \<open>Target-dependent graph bodies commute with precomposition\<close>

text \<open>
  A pair graph whose body at ⟨h,x⟩ is B(target h)(x) is
  unchanged by replacing h by h∘i, apart from its pair domain.
  Composition preserves that target. Source: Example 3.16(ii),
  p.54, and the logical-constant step of Proposition C.1, p.70.

  This is an equality of actual Lambda graphs on their complete
  pair domains. It requires a category and a legitimate arrow only,
  not selected-domain membership, an action, or a logical model.
\<close>

theorem paper_ZF_pair_lambda_target_naturality:
  assumes category: "paper_category Obj (explode A) source target compose identity"
    and arrow: "i \<in> explode A"
  shows "paper_ZF_exponential_transport_code A source target compose X i
      (paper_ZF_pair_lambda A source target X (source i) (\<lambda>h x. B (target h) x)) =
    paper_ZF_pair_lambda A source target X (target i) (\<lambda>h x. B (target h) x)"
proof -
  interpret C: paper_category Obj "explode A" source target compose identity by (rule category)
  let ?P = "paper_ZF_pair_code A source target X (target i)"
  let ?F = "paper_ZF_pair_lambda A source target X (source i) (\<lambda>h x. B (target h) x)"
  have bodies: "app ?F (Opair (compose (Fst z) i) (Snd z)) = B (target (Fst z)) (Snd z)"
    if member: "Elem z ?P" for z
  proof -
    have ha: "Fst z \<in> explode A" and hs: "source (Fst z) = target i"
      using paper_ZF_pair_code_projections[OF member] by blast+
    have meeting: "target i = source (Fst z)" by (rule hs[symmetric])
    have precomposed: "Elem (Opair (compose (Fst z) i) (Snd z))
        (paper_ZF_pair_code A source target X (source i))"
      by (rule paper_ZF_pair_precompose_code[OF category arrow member])
    have applied: "app ?F (Opair (compose (Fst z) i) (Snd z)) =
        B (target (compose (Fst z) i)) (Snd z)"
      by (rule paper_ZF_pair_lambda_apply[OF precomposed])
    show ?thesis by (simp only: applied C.compose_target[OF arrow ha meeting])
  qed
  show ?thesis
    unfolding paper_ZF_exponential_transport_code_def paper_ZF_pair_lambda_def
    by (rule iffD2[OF Lambda_ext], rule conjI[OF refl], intro allI impI,
      rule bodies[unfolded paper_ZF_pair_lambda_def], assumption)
qed

section \<open>All six literal logical families\<close>

theorem paper_ZF_logical_value_precompose:
  assumes category: "paper_category Obj (explode A) source target compose identity"
    and arrow: "i \<in> explode A"
    and symbol: "paper_logical_type l = Arr \<sigma> \<tau>"
  shows "paper_ZF_exponential_transport_code A source target compose (D \<sigma>) i
      (paper_ZF_logical_value A source target compose identity D T (source i) l) =
    paper_ZF_logical_value A source target compose identity D T (target i) l"
  using symbol
  by (cases l; auto simp: paper_logical_type.simps paper_ZF_logical_value.simps
    intro!: paper_ZF_pair_lambda_target_naturality[OF category arrow])

text \<open>
  The nested bodies for ∧, ∨ and =σ retain the entire inner
  pair domain. Quantifiers retain their full target-domain tests.
  No injectivity, surjectivity, or selected logical-stock closure is
  used. To identify canonical precomposition with a premodel's own
  transport, selected-fiber membership must be supplied separately.
\<close>

end

