theory Bacon_Source_Variable_Embedding
  imports Bacon_Source_Finite_Typing Bacon_Source_Closing_Structure Bacon_Source_Rich_Stock
begin

section \<open>Presenting finite-frame variables in a total typed stock\<close>

text \<open>
  A finite list Γ can be represented by variables from the source stock G
  when each declared slot k is sent to a variable of its declared type
  (Bacon–Dorr §1.1 and Figure 2).

  Isabelle representation: r maps finite-frame slots to total-stock slots.
  First type A in the total stock k ↦ G(r(k)); then use the proved global
  renaming theorem. No injectivity is needed for this typing implication.
  Signature membership concerns nonlogical constants and is unchanged.

  Status: typing and language preservation only. This map is not asserted
  to be injective on terms, to reflect typing, or to transport H proofs.
\<close>

lemma source_variable_embedding_type:
  assumes typed: "has_stype L \<Gamma> A \<tau>"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "has_sgtype L G (srename r A) \<tau>"
proof -
  have intermediate: "has_sgtype L (\<lambda>n. G (r n)) A \<tau>"
    by (rule source_finite_to_global_typing[where G="\<lambda>n. G (r n)", OF typed map])
  show ?thesis
  proof (rule srename_preserves_global_typing[where H=G and r=r, OF intermediate])
    fix n
    show "G (r n) = G (r n)" by (rule refl)
  qed
qed

lemma source_variable_embedding_signature:
  "sterm_in_signature \<Sigma> (srename r A) \<longleftrightarrow> sterm_in_signature \<Sigma> A"
  by (rule srename_signature)

lemma source_variable_embedding_language:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>"
    and map: "\<And>n \<rho>. lookup \<Gamma> n = Some \<rho> \<Longrightarrow> G (r n) = \<rho>"
  shows "sgterm_in_language L \<Sigma> G (srename r A) \<tau>"
proof -
  note parts = language[unfolded sterm_in_language_def]
  have typed: "has_sgtype L G (srename r A) \<tau>"
    by (rule source_variable_embedding_type[where G=G and r=r, OF conjunct1[OF parts] map])
  have names: "sterm_in_signature \<Sigma> (srename r A)"
    by (rule iffD2[OF source_variable_embedding_signature conjunct2[OF parts]])
  show ?thesis unfolding sgterm_in_language_def by (rule conjI[OF typed names])
qed

section \<open>Finite typing bounds the free-variable support\<close>

text \<open>
  FV(A) is contained in the variables declared by Γ.
  Under λx:σ.A, free slot k corresponds to slot k + 1 in the body.
  Source role: the finite freshness choices required by Figure 2's
  Gen and Inst side conditions.

  Isabelle representation: the bound is {0,…,|Γ|−1}. It may contain
  unused slots, which must not be confused with an assumption that
  every source proof uses only the conclusion's free variables.
  Status: finite support for a term, not yet for a proof transformation.
\<close>

lemma source_typed_fv_bound:
  assumes "has_stype L \<Gamma> A \<tau>"
  shows "sfv A \<subseteq> {..<length \<Gamma>}"
  using assms
proof (induction rule: has_stype.induct)
  case (Var \<Gamma> n \<tau>)
  have bound: "n < length \<Gamma>" using Var.hyps by (auto simp: lookup_def split: if_splits)
  show ?case using bound by simp
next
  case Const
  show ?case by simp
next
  case Logical
  show ?case by simp
next
  case App
  show ?case unfolding sfv.simps by (rule Un_least[OF App.IH])
next
  case (Lam \<sigma> \<Gamma> A \<tau>)
  show ?case
  proof (rule subsetI)
    fix n
    assume "n \<in> sfv (SLam \<sigma> A)"
    then have member: "Suc n \<in> sfv A" by (simp only: sfv.simps mem_Collect_eq)
    have bound: "Suc n \<in> {..<length (\<sigma> # \<Gamma>)}" by (rule subsetD[OF Lam.IH member])
    show "n \<in> {..<length \<Gamma>}" using bound by simp
  qed
qed

corollary source_typed_fv_finite:
  assumes "has_stype L \<Gamma> A \<tau>"
  shows "finite (sfv A)"
  by (rule finite_subset[OF source_typed_fv_bound[OF assms]]) simp

section \<open>A fresh typed source variable outside the finite image\<close>

text \<open>
  For every σ, choose a variable of type σ outside the image of Γ.
  Source: the infinite typed stock of §1.1, used for Gen/Inst in Figure 2.

  Isabelle representation: image r {..<length Γ} is finite even when r is
  not injective. Richness supplies a σ-variable outside that image.
  Status: a syntactic freshness witness, not an object-language existence
  axiom or a theorem-reflection result.
\<close>

lemma source_embedding_fresh_variable:
  fixes \<Gamma> :: ctx and r :: "nat \<Rightarrow> nat"
  assumes rich: "sg_rich G"
  obtains n where "G n = \<sigma>" and "n \<notin> image r {..<length \<Gamma>}"
proof -
  have finite_image: "finite (image r {..<length \<Gamma>})" by simp
  obtain n where typed: "G n = \<sigma>" and fresh: "n \<notin> image r {..<length \<Gamma>}"
    using sg_rich_fresh[where \<sigma>=\<sigma>, OF rich finite_image] by (elim exE conjE)
  show thesis by (rule that[OF typed fresh])
qed

end
