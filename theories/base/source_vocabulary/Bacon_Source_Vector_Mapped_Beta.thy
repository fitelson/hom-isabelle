theory Bacon_Source_Vector_Mapped_Beta
  imports Bacon_Source_Vector_Beta
begin

section \<open>Applying one closed source abstraction to renamed variables\<close>

text \<open>
  Let K := λvₙ₋₁.…λv₀.A close every slot of Γ.  Then K applied
  to the original variables converts to A, and K applied to their
  type-respecting r-images converts to srename r A.  Source role: the
  syntactic ingredient for deriving, rather than assuming, assignment
  renaming coherence from Definition 3.1(ii.a–d), pp.43–44.

  Isabelle representation.  First transport a signature-indexed source
  conversion along a typed variable map, preserving every intermediate
  type and signature guard.  Then rename the checked vector β equation;
  closedness leaves K unchanged.  No injectivity of r, closed signature
  inhabitants, semantic model, or object-language inference is used.
\<close>

lemma sbeta_eta_rename:
  assumes conversion: "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> \<tau> A B"
    and ren: "\<And>i \<sigma>. lookup \<Gamma> i = Some \<sigma> \<Longrightarrow> lookup \<Pi> (r i) = Some \<sigma>"
  shows "sbeta_eta_equiv_in_signature L \<Sigma> \<Pi> \<tau> (srename r A) (srename r B)"
  using conversion ren
proof (induction arbitrary: \<Pi> r rule: sbeta_eta_equiv_in_signature.induct)
  case (Refl \<Gamma> A \<tau>)
  have typed: "has_stype L \<Pi> (srename r A) \<tau>"
    by (rule srename_preserves_typing[where \<Delta>=\<Pi> and r=r, OF Refl.hyps(1) Refl.prems])
  have sig: "sterm_in_signature \<Sigma> (srename r A)" using Refl.hyps(2) by (simp only: srename_signature)
  show ?case by (rule sbeta_eta_equiv_in_signature.Refl[OF typed sig])
next
  case (Beta \<Gamma> A \<tau> B)
  have at: "has_stype L \<Pi> (srename r A) \<tau>"
    by (rule srename_preserves_typing[where \<Delta>=\<Pi> and r=r, OF Beta.hyps(1) Beta.prems])
  have bt: "has_stype L \<Pi> (srename r B) \<tau>"
    by (rule srename_preserves_typing[where \<Delta>=\<Pi> and r=r, OF Beta.hyps(2) Beta.prems])
  have asig: "sterm_in_signature \<Sigma> (srename r A)" using Beta.hyps(3) by (simp only: srename_signature)
  have bsig: "sterm_in_signature \<Sigma> (srename r B)" using Beta.hyps(4) by (simp only: srename_signature)
  have step: "scompatible_step sbeta_contract (srename r A) (srename r B)"
    by (rule srename_beta_step[where r=r, OF Beta.hyps(5)])
  show ?case by (rule sbeta_eta_equiv_in_signature.Beta[OF at bt asig bsig step])
next
  case (Eta \<Gamma> A \<tau> B)
  have at: "has_stype L \<Pi> (srename r A) \<tau>"
    by (rule srename_preserves_typing[where \<Delta>=\<Pi> and r=r, OF Eta.hyps(1) Eta.prems])
  have bt: "has_stype L \<Pi> (srename r B) \<tau>"
    by (rule srename_preserves_typing[where \<Delta>=\<Pi> and r=r, OF Eta.hyps(2) Eta.prems])
  have asig: "sterm_in_signature \<Sigma> (srename r A)" using Eta.hyps(3) by (simp only: srename_signature)
  have bsig: "sterm_in_signature \<Sigma> (srename r B)" using Eta.hyps(4) by (simp only: srename_signature)
  have step: "scompatible_step seta_contract (srename r A) (srename r B)"
    by (rule srename_eta_step[where r=r, OF Eta.hyps(5)])
  show ?case by (rule sbeta_eta_equiv_in_signature.Eta[OF at bt asig bsig step])
next
  case (Sym \<Gamma> \<tau> A B)
  show ?case by (rule sbeta_eta_equiv_in_signature.Sym[OF Sym.IH[where \<Pi>=\<Pi> and r=r, OF Sym.prems]])
next
  case (Trans \<Gamma> \<tau> A B C)
  show ?case by (rule sbeta_eta_equiv_in_signature.Trans[
    OF Trans.IH(1)[where \<Pi>=\<Pi> and r=r, OF Trans.prems]
      Trans.IH(2)[where \<Pi>=\<Pi> and r=r, OF Trans.prems]])
qed

lemma srenamed_fresh_vars_type:
  assumes ren: "\<And>i \<sigma>. lookup \<Gamma> i = Some \<sigma> \<Longrightarrow> lookup \<Pi> (r i) = Some \<sigma>"
  shows "list_all2 (\<lambda>A \<sigma>. has_stype L \<Pi> A \<sigma>)
    (map (srename r) (rev (sfresh_vars (length \<Gamma>)))) (rev \<Gamma>)"
proof -
  have original: "list_all2 (\<lambda>A \<sigma>. has_stype L \<Gamma> A \<sigma>)
    (rev (sfresh_vars (length \<Gamma>))) (rev \<Gamma>)"
    using sreverse_fresh_vars_type[where L=L and \<Delta>=\<Gamma> and \<Gamma>="[]"] by simp
  show ?thesis unfolding list_all2_map1
  proof (rule list_all2_mono[OF original])
    fix A \<sigma>
    assume typed: "has_stype L \<Gamma> A \<sigma>"
    show "has_stype L \<Pi> (srename r A) \<sigma>" by (rule srename_preserves_typing[OF typed ren])
  qed
qed

lemma srenamed_fresh_vars_signature:
  assumes member: "A \<in> set (map (srename r) (rev (sfresh_vars n)))"
  shows "sterm_in_signature \<Sigma> A"
proof -
  obtain B where original: "B \<in> set (rev (sfresh_vars n))" and eq: "A = srename r B"
    using member by auto
  have sig: "sterm_in_signature \<Sigma> B" by (rule sfresh_vars_signature[OF original])
  show ?thesis by (simp only: eq srename_signature sig)
qed

theorem sabstract_all_application_beta:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>"
  shows "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> \<tau>
    (sapp_vec (sabstract_prefix \<Gamma> A) (rev (sfresh_vars (length \<Gamma>)))) A"
proof -
  have with_empty: "sterm_in_language L \<Sigma> (\<Gamma> @ []) A \<tau>" using language by simp
  have raw: "sbeta_eta_equiv_in_signature L \<Sigma> (\<Gamma> @ []) \<tau>
    (sapp_vec (sraise (length \<Gamma>) (sabstract_prefix \<Gamma> A)) (rev (sfresh_vars (length \<Gamma>)))) A"
    by (rule sdeabstract_beta[OF with_empty])
  have typed: "has_stype L \<Gamma> A \<tau>" using language unfolding sterm_in_language_def by (rule conjunct1)
  have closed: "sfv (sabstract_prefix \<Gamma> A) = {}" by (rule sabstract_all_closed[OF typed])
  show ?thesis using raw by (simp only: append_Nil2 sraise_closed[OF closed])
qed

theorem sabstract_all_mapped_beta:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>"
    and ren: "\<And>i \<sigma>. lookup \<Gamma> i = Some \<sigma> \<Longrightarrow> lookup \<Pi> (r i) = Some \<sigma>"
  shows "sbeta_eta_equiv_in_signature L \<Sigma> \<Pi> \<tau>
    (sapp_vec (sabstract_prefix \<Gamma> A) (map (srename r) (rev (sfresh_vars (length \<Gamma>)))))
    (srename r A)"
proof -
  have original: "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> \<tau>
    (sapp_vec (sabstract_prefix \<Gamma> A) (rev (sfresh_vars (length \<Gamma>)))) A"
    by (rule sabstract_all_application_beta[OF language])
  have mapped: "sbeta_eta_equiv_in_signature L \<Sigma> \<Pi> \<tau>
    (srename r (sapp_vec (sabstract_prefix \<Gamma> A) (rev (sfresh_vars (length \<Gamma>))))) (srename r A)"
    by (rule sbeta_eta_rename[where \<Pi>=\<Pi> and r=r, OF original ren])
  have typed: "has_stype L \<Gamma> A \<tau>" using language unfolding sterm_in_language_def by (rule conjunct1)
  have closed: "sfv (sabstract_prefix \<Gamma> A) = {}" by (rule sabstract_all_closed[OF typed])
  show ?thesis using mapped by (simp only: srename_sapp_vec srename_closed[OF closed])
qed

lemma sabstract_all_language:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>"
  shows "sterm_in_language L \<Sigma> \<Pi> (sabstract_prefix \<Gamma> A) (sarrow_type (rev \<Gamma>) \<tau>)"
proof -
  have typed: "has_stype L \<Gamma> A \<tau>" and sig: "sterm_in_signature \<Sigma> A"
    using language unfolding sterm_in_language_def by blast+
  have abstract_type: "has_stype L [] (sabstract_prefix \<Gamma> A) (sarrow_type (rev \<Gamma>) \<tau>)"
    by (rule sabstract_all_type[OF typed])
  have closed: "sfv (sabstract_prefix \<Gamma> A) = {}" by (rule sabstract_all_closed[OF typed])
  have moved: "has_stype L \<Pi> (sabstract_prefix \<Gamma> A) (sarrow_type (rev \<Gamma>) \<tau>)"
    using sraise_type[where \<Delta>=\<Pi> and \<Gamma>="[]", OF abstract_type]
    by (simp only: append_Nil2 sraise_closed[OF closed])
  have names: "sterm_in_signature \<Sigma> (sabstract_prefix \<Gamma> A)"
    by (simp only: sabstract_prefix_signature sig)
  show ?thesis unfolding sterm_in_language_def by (rule conjI[OF moved names])
qed

end
