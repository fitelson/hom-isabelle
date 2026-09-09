theory Bacon_Source_Named_Representation_Reflection
  imports Bacon_Source_Named_Prefix_Roundtrip Bacon_Source_Vector_Syntax
begin

section \<open>Typed source terms have named representatives\<close>

text \<open>
  Every source term M:τ in the fixed global stock G has a named
  representative N:τ with enc(N) = M. Decode M in an identity chart
  long enough to contain all its free slots. The chart's nth map is
  the identity on that support, so re-encoding removes the chart renaming.
  Source role: the named-variable representation of Bacon–Dorr §1.1, p.5.

  Representation: the initial term M need not already be a named encoding.
  Typing, signature membership and rich G are explicit. Neither raw
  untyped surjectivity nor reverse H proof preservation is asserted.
\<close>

theorem source_prefix_decoder_encoding:
  assumes language: "sgterm_in_language L \<Sigma> G M \<tau>"
    and bound: "source_free_bound M \<le> m" and rich: "sg_rich G"
  shows "named_to_source G [] (source_to_named G [0..<m] M) = M"
proof -
  have prefix: "sterm_in_language L \<Sigma> (source_prefix G m) M \<tau>"
    by (rule source_language_in_prefix[OF language bound])
  have typed: "has_stype L (source_prefix G m) M \<tau>"
    using prefix unfolding sterm_in_language_def by (rule conjunct1)
  have decoded: "named_to_source G [] (source_to_named G [0..<m] M) =
    srename (\<lambda>i. [0..<m] ! i) M"
    by (rule source_to_named_empty_encoding[OF typed named_identity_prefix_chart rich])
  have agreement: "srename (\<lambda>i. [0..<m] ! i) M = srename id M"
  proof (rule srename_fv_agreement)
    fix i
    assume free: "i \<in> sfv M"
    have free_bound: "i < source_free_bound M"
      by (rule source_free_bound_covers[OF free])
    have index: "i < m" by (rule less_le_trans[OF free_bound bound])
    show "[0..<m] ! i = id i" using index by simp
  qed
  show ?thesis by (rule trans[OF decoded trans[OF agreement srename_identity]])
qed

theorem source_named_representation_exists:
  assumes language: "sgterm_in_language L \<Sigma> G M \<tau>" and rich: "sg_rich G"
  shows "\<exists>N. named_in_language L \<Sigma> G N \<tau> \<and> named_to_source G [] N = M"
proof -
  let ?m = "source_free_bound M"
  let ?N = "source_to_named G [0..< ?m] M"
  have bound: "source_free_bound M \<le> ?m" by (rule order_refl)
  have prefix: "sterm_in_language L \<Sigma> (source_prefix G ?m) M \<tau>"
    by (rule source_language_in_prefix[OF language bound])
  have named_language: "named_in_language L \<Sigma> G ?N \<tau>"
    by (rule source_to_named_language[OF prefix named_identity_prefix_chart rich])
  have encoded: "named_to_source G [] ?N = M"
    by (rule source_prefix_decoder_encoding[OF language bound rich])
  show ?thesis by (rule exI[where x="?N"], rule conjI[OF named_language encoded])
qed

section \<open>Language reflection through equality of encodings\<close>

text \<open>
  If enc(A):τ belongs to ℒ(Σ), construct a well-typed named N with
  the same encoding. The proved α characterization gives N ≡α A,
  and α preserves typing and signature membership. Thus A:τ is itself
  in ℒ(Σ). Status: this reflection argument uses no H or model judgment.
\<close>

theorem named_representation_language_reflection:
  assumes encoded: "sgterm_in_language L \<Sigma> G (named_to_source G [] A) \<tau>"
    and rich: "sg_rich G"
  shows "named_in_language L \<Sigma> G A \<tau>"
proof -
  obtain N where language: "named_in_language L \<Sigma> G N \<tau>"
    and same: "named_to_source G [] N = named_to_source G [] A"
    using source_named_representation_exists[OF encoded rich] by (elim exE conjE)
  have alpha: "named_alpha G N A" by (rule named_encoding_implies_alpha[OF rich same])
  show ?thesis by (rule iffD1[OF named_alpha_language_iff[OF alpha] language])
qed

corollary named_representation_language_iff:
  assumes rich: "sg_rich G"
  shows "named_in_language L \<Sigma> G A \<tau> \<longleftrightarrow>
    sgterm_in_language L \<Sigma> G (named_to_source G [] A) \<tau>"
proof
  assume language: "named_in_language L \<Sigma> G A \<tau>"
  show "sgterm_in_language L \<Sigma> G (named_to_source G [] A) \<tau>"
    using named_to_source_global_language[where ns="[]", OF language]
    by (simp only: named_stack_stock.simps)
next
  assume encoded: "sgterm_in_language L \<Sigma> G (named_to_source G [] A) \<tau>"
  show "named_in_language L \<Sigma> G A \<tau>"
    by (rule named_representation_language_reflection[OF encoded rich])
qed

end
