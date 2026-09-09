theory Bacon_Source_Binder_Conversion
  imports Bacon_Source_Quantifier_Axioms
begin

section \<open>A quantifier applied to a displayed abstraction\<close>

text \<open>
  ∀σ(λx:σ.A) and ∃σ(λx:σ.A) are the first-class source forms
  of ∀x:σ.A and ∃x:σ.A (Bacon–Dorr §1.1 and Figure 2).

  Isabelle representation: after the logical wrapper contracts, a second
  β step removes the application of the shifted abstraction to slot zero.
  That step is lifted under the target quantifier, with all endpoints
  typed and in the declared signature.

  Status: syntax conversion only. No model assumption or material
  replacement inside an intensional context is used.
\<close>

lemma source_target_binder_restore:
  "psubst0 (PVar 0) (prename (lift_ren Suc) A) = A"
  unfolding psubst0_def
  by (rule psubst_prename_inverse) (case_tac n; simp)

lemma source_target_binder_application:
  fixes A :: "'c pterm"
  assumes body: "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) A \<tau>"
  shows "pbeta_eta_equiv_in_signature \<Sigma> (\<sigma> # \<Gamma>) \<tau>
    (PApp (pshift (PLam \<sigma> A)) (PVar 0)) A"
proof -
  note bd = body[unfolded pterm_in_language_def]
  have lambda: "has_ptype \<Gamma> (PLam \<sigma> A) (Arr \<sigma> \<tau>)"
    by (rule has_ptype.PLam[OF conjunct1[OF bd]])
  have shifted: "has_ptype (\<sigma> # \<Gamma>) (pshift (PLam \<sigma> A)) (Arr \<sigma> \<tau>)"
    by (rule pshift_preserves_typing[OF lambda])
  have variable: "has_ptype (\<sigma> # \<Gamma>) (PVar 0) \<sigma>"
    by (rule has_ptype.PVar[OF lookup_Cons_0])
  have typed: "has_ptype (\<sigma> # \<Gamma>) (PApp (pshift (PLam \<sigma> A)) (PVar 0)) \<tau>"
    by (rule has_ptype.PApp[OF shifted variable])
  have names: "pterm_in_signature \<Sigma> (PApp (pshift (PLam \<sigma> A)) (PVar 0))"
    using conjunct2[OF bd] by (simp add: pshift_def)
  have root: "pbeta_contract
    (PApp (PLam \<sigma> (prename (lift_ren Suc) A)) (PVar 0))
    (psubst0 (PVar 0) (prename (lift_ren Suc) A))" by (rule pbeta_contract.beta)
  have reduced: "pbeta_contract (PApp (pshift (PLam \<sigma> A)) (PVar 0)) A"
    using root by (simp only: pshift_def prename.simps source_target_binder_restore)
  have step: "pcompatible_step pbeta_contract (PApp (pshift (PLam \<sigma> A)) (PVar 0)) A"
    by (rule pcompatible_step.root[where R=pbeta_contract and
      M="PApp (pshift (PLam \<sigma> A)) (PVar 0)" and N=A, OF reduced])
  show ?thesis by (rule pbeta_eta_equiv_in_signature.Beta[
    OF typed conjunct1[OF bd] names conjunct2[OF bd] step])
qed

lemma source_conversion_Forall:
  fixes M N :: "'c pterm"
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> (\<sigma> # \<Gamma>) Prop M N"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (PForall \<sigma> M) (PForall \<sigma> N)"
proof (rule source_conversion_map[where C="PForall \<sigma>", OF conv])
  show "\<And>X. has_ptype (\<sigma> # \<Gamma>) X Prop \<Longrightarrow> has_ptype \<Gamma> (PForall \<sigma> X) Prop"
    by (erule has_ptype.PForall)
  show "\<And>X. pterm_in_signature \<Sigma> X \<Longrightarrow> pterm_in_signature \<Sigma> (PForall \<sigma> X)" by simp
  show "\<And>X Y. pcompatible_step pbeta_contract X Y \<Longrightarrow>
    pcompatible_step pbeta_contract (PForall \<sigma> X) (PForall \<sigma> Y)"
    by (erule pcompatible_step.Forall_body)
  show "\<And>X Y. pcompatible_step peta_contract X Y \<Longrightarrow>
    pcompatible_step peta_contract (PForall \<sigma> X) (PForall \<sigma> Y)"
    by (erule pcompatible_step.Forall_body)
qed

lemma source_conversion_Exists:
  fixes M N :: "'c pterm"
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> (\<sigma> # \<Gamma>) Prop M N"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (PExists \<sigma> M) (PExists \<sigma> N)"
proof (rule source_conversion_map[where C="PExists \<sigma>", OF conv])
  show "\<And>X. has_ptype (\<sigma> # \<Gamma>) X Prop \<Longrightarrow> has_ptype \<Gamma> (PExists \<sigma> X) Prop"
    by (erule has_ptype.PExists)
  show "\<And>X. pterm_in_signature \<Sigma> X \<Longrightarrow> pterm_in_signature \<Sigma> (PExists \<sigma> X)" by simp
  show "\<And>X Y. pcompatible_step pbeta_contract X Y \<Longrightarrow>
    pcompatible_step pbeta_contract (PExists \<sigma> X) (PExists \<sigma> Y)"
    by (erule pcompatible_step.Exists_body)
  show "\<And>X Y. pcompatible_step peta_contract X Y \<Longrightarrow>
    pcompatible_step peta_contract (PExists \<sigma> X) (PExists \<sigma> Y)"
    by (erule pcompatible_step.Exists_body)
qed

lemma paper_binder_abstraction_language:
  assumes body: "sterm_in_language paper_logical_type \<Sigma> (\<sigma> # \<Gamma>) A \<tau>"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SLam \<sigma> A) (Arr \<sigma> \<tau>)"
proof -
  note bd = body[unfolded sterm_in_language_def]
  have typed: "has_stype paper_logical_type \<Gamma> (SLam \<sigma> A) (Arr \<sigma> \<tau>)"
    by (rule has_stype.Lam[OF conjunct1[OF bd]])
  show ?thesis unfolding sterm_in_language_def
    by (rule conjI[OF typed]) (simp add: conjunct2[OF bd])
qed

theorem paper_all_binder_conversion:
  assumes body: "sterm_in_language paper_logical_type \<Sigma> (\<sigma> # \<Gamma>) A Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (SApp (SLogical (SAll \<sigma>)) (SLam \<sigma> A)))
    (PForall \<sigma> (paper_to_pterm A))"
proof -
  note abstraction = paper_binder_abstraction_language[OF body]
  note outer = paper_all_application[OF abstraction]
  note inner = source_target_binder_application[OF iffD2[OF paper_to_pterm_language_iff body]]
  have lifted: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (PForall \<sigma> (PApp (pshift (paper_to_pterm (SLam \<sigma> A))) (PVar 0)))
    (PForall \<sigma> (paper_to_pterm A))"
    using source_conversion_Forall[OF inner] by (simp only: sterm_translation.simps)
  show ?thesis by (rule pbeta_eta_equiv_in_signature.Trans[OF outer lifted])
qed

theorem paper_ex_binder_conversion:
  assumes body: "sterm_in_language paper_logical_type \<Sigma> (\<sigma> # \<Gamma>) A Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (SApp (SLogical (SEx \<sigma>)) (SLam \<sigma> A)))
    (PExists \<sigma> (paper_to_pterm A))"
proof -
  note abstraction = paper_binder_abstraction_language[OF body]
  note outer = paper_ex_application[OF abstraction]
  note inner = source_target_binder_application[OF iffD2[OF paper_to_pterm_language_iff body]]
  have lifted: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (PExists \<sigma> (PApp (pshift (paper_to_pterm (SLam \<sigma> A))) (PVar 0)))
    (PExists \<sigma> (paper_to_pterm A))"
    using source_conversion_Exists[OF inner] by (simp only: sterm_translation.simps)
  show ?thesis by (rule pbeta_eta_equiv_in_signature.Trans[OF outer lifted])
qed

end
