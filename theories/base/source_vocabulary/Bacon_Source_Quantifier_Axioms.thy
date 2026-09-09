theory Bacon_Source_Quantifier_Axioms
  imports Bacon_Source_Proof_Connectives
begin

section \<open>Conversion inside the target proof-level implication\<close>

text \<open>
  Contextual βη conversion permits replacement within a formula
  (Bacon–Dorr Figure 2).  The target proof rules use primitive PImp.

  Isabelle representation: these two lemmas lift genuine, signature-indexed
  βη conversion under PImp.  The unchanged argument must be a formula in Σ.

  Status: syntactic conversion only.  This does not identify PImp with the
  paper's defined implication or lift mere material equivalence.
\<close>

lemma source_conversion_Imp_left:
  fixes M N B :: "'c pterm"
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop M N"
    and arg: "pterm_in_language \<Sigma> \<Gamma> B Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (PImp M B) (PImp N B)"
proof (rule source_conversion_map[where C="\<lambda>X. PImp X B", OF conv])
  show "\<And>X. has_ptype \<Gamma> X Prop \<Longrightarrow> has_ptype \<Gamma> (PImp X B) Prop"
  proof -
    fix X :: "'c pterm"
    assume xt: "has_ptype \<Gamma> X Prop"
    have bt: "has_ptype \<Gamma> B Prop" using arg unfolding pterm_in_language_def by (rule conjunct1)
    show "has_ptype \<Gamma> (PImp X B) Prop" by (rule has_ptype.PImp[OF xt bt])
  qed
  show "\<And>X. pterm_in_signature \<Sigma> X \<Longrightarrow> pterm_in_signature \<Sigma> (PImp X B)"
    using arg unfolding pterm_in_language_def by simp
  show "\<And>X Y. pcompatible_step pbeta_contract X Y \<Longrightarrow>
    pcompatible_step pbeta_contract (PImp X B) (PImp Y B)"
    by (erule pcompatible_step.Imp_left)
  show "\<And>X Y. pcompatible_step peta_contract X Y \<Longrightarrow>
    pcompatible_step peta_contract (PImp X B) (PImp Y B)"
    by (erule pcompatible_step.Imp_left)
qed

lemma source_conversion_Imp_right:
  fixes M N A :: "'c pterm"
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop M N"
    and arg: "pterm_in_language \<Sigma> \<Gamma> A Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (PImp A M) (PImp A N)"
proof (rule source_conversion_map[where C="PImp A", OF conv])
  show "\<And>X. has_ptype \<Gamma> X Prop \<Longrightarrow> has_ptype \<Gamma> (PImp A X) Prop"
  proof -
    fix X :: "'c pterm"
    assume xt: "has_ptype \<Gamma> X Prop"
    have at: "has_ptype \<Gamma> A Prop" using arg unfolding pterm_in_language_def by (rule conjunct1)
    show "has_ptype \<Gamma> (PImp A X) Prop" by (rule has_ptype.PImp[OF at xt])
  qed
  show "\<And>X. pterm_in_signature \<Sigma> X \<Longrightarrow> pterm_in_signature \<Sigma> (PImp A X)"
    using arg unfolding pterm_in_language_def by simp
  show "\<And>X Y. pcompatible_step pbeta_contract X Y \<Longrightarrow>
    pcompatible_step pbeta_contract (PImp A X) (PImp A Y)"
    by (erule pcompatible_step.Imp_right)
  show "\<And>X Y. pcompatible_step peta_contract X Y \<Longrightarrow>
    pcompatible_step peta_contract (PImp A X) (PImp A Y)"
    by (erule pcompatible_step.Imp_right)
qed

section \<open>Arbitrary predicates as binder bodies\<close>

text \<open>
  UI is ∀σF → FA, and EG is FA → ∃σF, for F:σ → t and A:σ
  (Bacon–Dorr Figure 2).  F is not required to be an abstraction.

  Isabelle representation: the binder body is PApp (pshift F) (PVar 0).
  Substituting A for its new slot gives PApp F A exactly.  The following
  helper theorems use target UI/EG before the literal source wrappers are
  restored.

  Status: typed and signature-guarded axiom transport, not Gen/Inst
  preservation or a global-to-finite proof transformation.
\<close>

lemma paper_source_logical_language:
  "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SLogical l) (paper_logical_type l)"
proof (rule iffD1[OF paper_to_pterm_language_iff])
  show "pterm_in_language \<Sigma> \<Gamma> (paper_to_pterm (SLogical l)) (paper_logical_type l)"
    unfolding sterm_translation.simps by (rule paper_logical_translation_language)
qed

lemma paper_source_app_language:
  assumes F: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> \<tau>)"
    and A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp F A) \<tau>"
proof (rule iffD1[OF paper_to_pterm_language_iff])
  show "pterm_in_language \<Sigma> \<Gamma> (paper_to_pterm (SApp F A)) \<tau>"
    unfolding sterm_translation.simps
    by (rule source_target_app_language[OF iffD2[OF paper_to_pterm_language_iff F]
      iffD2[OF paper_to_pterm_language_iff A]])
qed

lemma source_predicate_body_language:
  assumes F: "pterm_in_language \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
  shows "pterm_in_language \<Sigma> (\<sigma> # \<Gamma>) (PApp (pshift F) (PVar 0)) Prop"
proof -
  have ft: "has_ptype \<Gamma> F (Arr \<sigma> Prop)" using F unfolding pterm_in_language_def by (rule conjunct1)
  have fs: "pterm_in_signature \<Sigma> F" using F unfolding pterm_in_language_def by (rule conjunct2)
  have body: "has_ptype (\<sigma> # \<Gamma>) (PApp (pshift F) (PVar 0)) Prop"
    by (rule has_ptype.PApp[OF pshift_preserves_typing[OF ft] has_ptype.PVar[OF lookup_Cons_0]])
  show ?thesis unfolding pterm_in_language_def
    by (rule conjI[OF body]) (simp add: pshift_def fs)
qed

lemma source_predicate_subst0:
  "psubst0 A (PApp (pshift F) (PVar 0)) = PApp F A"
  by (simp add: psubst0_def pshift_def source_target_subst_shift)

lemma source_target_UI_predicate:
  assumes F: "pterm_in_language \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
    and A: "pterm_in_language \<Sigma> \<Gamma> A \<sigma>"
  shows "pH_proves \<Sigma> \<Gamma> (PImp (PForall \<sigma> (PApp (pshift F) (PVar 0))) (PApp F A))"
proof -
  note body = source_predicate_body_language[OF F, unfolded pterm_in_language_def]
  note arg = A[unfolded pterm_in_language_def]
  note ui_axiom = pH_proves.UI[OF conjunct1[OF body] conjunct1[OF arg]
    conjunct2[OF body] conjunct2[OF arg]]
  show ?thesis using ui_axiom by (simp only: source_predicate_subst0)
qed

lemma source_target_EG_predicate:
  assumes F: "pterm_in_language \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
    and A: "pterm_in_language \<Sigma> \<Gamma> A \<sigma>"
  shows "pH_proves \<Sigma> \<Gamma> (PImp (PApp F A) (PExists \<sigma> (PApp (pshift F) (PVar 0))))"
proof -
  note body = source_predicate_body_language[OF F, unfolded pterm_in_language_def]
  note arg = A[unfolded pterm_in_language_def]
  note eg_axiom = pH_proves.EG[OF conjunct1[OF body] conjunct1[OF arg]
    conjunct2[OF body] conjunct2[OF arg]]
  show ?thesis using eg_axiom by (simp only: source_predicate_subst0)
qed

subsection \<open>Literal source UI and EG in a finite presentation\<close>

text \<open>
  ⊢H ⟦∀σF → FA⟧ and ⊢H ⟦FA → ∃σF⟧.
  The source arrows here are exactly Figure 1's λ-defined implication.

  Isabelle representation: normalize the quantifier application inside a
  target PImp, transport the target axiom backwards through that conversion,
  and then use the outermost implication-theoremhood equivalence.

  Status: finite-frame translation of these two source axiom families.
  No operator identity or assumption that F is a λ-term is used.
\<close>

theorem paper_UI_translation:
  assumes F: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
    and A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
  shows "pH_proves \<Sigma> \<Gamma>
    (paper_to_pterm (paper_imp (SApp (SLogical (SAll \<sigma>)) F) (SApp F A)))"
proof -
  note ft = iffD2[OF paper_to_pterm_language_iff F]
  note at = iffD2[OF paper_to_pterm_language_iff A]
  have quantifier: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (SLogical (SAll \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_source_logical_language[where l="SAll \<sigma>"] by simp
  note all_l = paper_source_app_language[OF quantifier F]
  note fa_l = paper_source_app_language[OF F A]
  note fa_t = iffD2[OF paper_to_pterm_language_iff fa_l]
  note conversion = source_conversion_Imp_left[OF paper_all_application[OF F] fa_t]
  have normalized: "pH_proves \<Sigma> \<Gamma>
    (PImp (PForall \<sigma> (PApp (pshift (paper_to_pterm F)) (PVar 0))) (paper_to_pterm (SApp F A)))"
    using source_target_UI_predicate[OF ft at] by (simp only: sterm_translation.simps)
  have primitive: "pH_proves \<Sigma> \<Gamma>
    (PImp (paper_to_pterm (SApp (SLogical (SAll \<sigma>)) F)) (paper_to_pterm (SApp F A)))"
    by (rule source_pH_conversion_backward[OF conversion normalized])
  show ?thesis by (rule iffD2[OF paper_imp_translation_proves_iff[OF all_l fa_l] primitive])
qed

theorem paper_EG_translation:
  assumes F: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
    and A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
  shows "pH_proves \<Sigma> \<Gamma>
    (paper_to_pterm (paper_imp (SApp F A) (SApp (SLogical (SEx \<sigma>)) F)))"
proof -
  note ft = iffD2[OF paper_to_pterm_language_iff F]
  note at = iffD2[OF paper_to_pterm_language_iff A]
  have quantifier: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (SLogical (SEx \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_source_logical_language[where l="SEx \<sigma>"] by simp
  note ex_l = paper_source_app_language[OF quantifier F]
  note fa_l = paper_source_app_language[OF F A]
  note fa_t = iffD2[OF paper_to_pterm_language_iff fa_l]
  note conversion = source_conversion_Imp_right[OF paper_ex_application[OF F] fa_t]
  have normalized: "pH_proves \<Sigma> \<Gamma>
    (PImp (paper_to_pterm (SApp F A)) (PExists \<sigma> (PApp (pshift (paper_to_pterm F)) (PVar 0))))"
    using source_target_EG_predicate[OF ft at] by (simp only: sterm_translation.simps)
  have primitive: "pH_proves \<Sigma> \<Gamma>
    (PImp (paper_to_pterm (SApp F A)) (paper_to_pterm (SApp (SLogical (SEx \<sigma>)) F)))"
    by (rule source_pH_conversion_backward[OF conversion normalized])
  show ?thesis by (rule iffD2[OF paper_imp_translation_proves_iff[OF fa_l ex_l] primitive])
qed

end
