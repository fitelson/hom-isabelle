theory Bacon_Source_Minimal_Frame
  imports Bacon_Source_Finite_Typing Bacon_Source_Variable_Embedding
begin

section \<open>A source term needs only its supported initial frame\<close>

text \<open>
  Γ ⊢ M:τ implies Γ↾b(M) ⊢ M:τ, where b(M) is one beyond
  the greatest free slot, or zero when there are no free slots.
  Source role: finite support of the variable typing convention in
  Bacon–Dorr §1.1, p.5.

  Isabelle representation. We reuse the existing finite-to-global and
  global-to-finite typing proofs. Those proofs extend both contexts beneath
  λ and retain slot zero for its bound variable. The intermediate total
  stock i ↦ Γᵢ is consulted only at supported slots when returning to a
  finite frame; its unspecified out-of-range nth values play no role.

  Status. A syntax typing restriction, not proof-context restriction or
  denotation erasure. No rich stock, signature inhabitants, semantic
  domain inhabitants, or model premise is needed.
\<close>

lemma source_finite_context_agreement:
  assumes typed: "has_stype L \<Gamma> M \<tau>"
    and agrees: "\<And>i. i \<in> sfv M \<Longrightarrow> lookup \<Delta> i = lookup \<Gamma> i"
  shows "has_stype L \<Delta> M \<tau>"
proof -
  let ?G = "\<lambda>i. \<Gamma> ! i"
  have global_type: "has_sgtype L ?G M \<tau>"
  proof (rule source_finite_to_global_typing[where G="?G", OF typed])
    fix i \<sigma>
    assume index: "lookup \<Gamma> i = Some \<sigma>"
    show "?G i = \<sigma>" using index by (auto simp: lookup_def split: if_splits)
  qed
  show ?thesis
  proof (rule source_global_to_finite_typing[OF global_type])
    fix i
    assume free: "i \<in> sfv M"
    have bound: "i < length \<Gamma>"
      using subsetD[OF source_typed_fv_bound[OF typed] free] by simp
    have index: "lookup \<Gamma> i = Some (?G i)"
      by (simp only: lookup_def bound if_True)
    show "lookup \<Delta> i = Some (?G i)" by (rule trans[OF agrees[OF free] index])
  qed
qed

lemma source_typing_take_support:
  assumes typed: "has_stype L \<Gamma> M \<tau>"
    and covered: "\<And>i. i \<in> sfv M \<Longrightarrow> i < k"
  shows "has_stype L (take k \<Gamma>) M \<tau>"
proof (rule source_finite_context_agreement[OF typed])
  fix i
  assume free: "i \<in> sfv M"
  have before_k: "i < k" by (rule covered[OF free])
  have before_end: "i < length \<Gamma>"
    using subsetD[OF source_typed_fv_bound[OF typed] free] by simp
  have before_prefix: "i < length (take k \<Gamma>)" using before_k before_end by simp
  show "lookup (take k \<Gamma>) i = lookup \<Gamma> i"
    by (simp only: lookup_def before_prefix before_end if_True nth_take[OF before_k])
qed

lemma source_free_bound_le_context:
  assumes typed: "has_stype L \<Gamma> M \<tau>"
  shows "source_free_bound M \<le> length \<Gamma>"
  using typed
proof (induction rule: has_stype.induct)
  case (Var \<Gamma> n \<tau>)
  have bound: "n < length \<Gamma>"
    using Var.hyps by (auto simp: lookup_def split: if_splits)
  show ?case using bound by simp
next
  case Const
  show ?case by simp
next
  case Logical
  show ?case by simp
next
  case (App \<Gamma> F \<sigma> \<tau> A)
  show ?case using App.IH by simp
next
  case (Lam \<sigma> \<Gamma> M \<tau>)
  have body: "source_free_bound M \<le> Suc (length \<Gamma>)"
    using Lam.IH by simp
  have subtracted: "source_free_bound M - 1 \<le> Suc (length \<Gamma>) - 1"
    by (rule diff_le_mono[OF body])
  show ?case using subtracted by simp
qed

theorem source_typing_minimal_frame:
  assumes typed: "has_stype L \<Gamma> M \<tau>"
  shows "has_stype L (take (source_free_bound M) \<Gamma>) M \<tau>"
  by (rule source_typing_take_support[OF typed]; rule source_free_bound_covers; assumption)

corollary source_language_minimal_frame:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> M \<tau>"
  shows "sterm_in_language L \<Sigma> (take (source_free_bound M) \<Gamma>) M \<tau>"
proof -
  have typed: "has_stype L \<Gamma> M \<tau>" and sig: "sterm_in_signature \<Sigma> M"
    using language unfolding sterm_in_language_def by blast+
  show ?thesis unfolding sterm_in_language_def
    by (rule conjI[OF source_typing_minimal_frame[OF typed] sig])
qed

end
