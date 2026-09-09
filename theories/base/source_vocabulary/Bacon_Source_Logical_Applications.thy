theory Bacon_Source_Logical_Applications
  imports Bacon_Source_Typing_Reflection
begin

section \<open>Guarded β computations for first-class logical constants\<close>

text \<open>
  (λv.A)B ≡β A[B/v].  Saturating the source logical constants gives
  ¬A, A ∧ B, A ∨ B, A =σ B, ∀σF, and ∃σF
  (Bacon–Dorr pp. 5–6 and Figure 2).  For example, ⟦∀σF⟧ converts to
  ∀x:σ.⟦F⟧x, with the free variables of F shifted beneath the binder.

  Isabelle representation: the helpers below perform one or two target β
  contractions.  Every conversion endpoint and intermediate term is typed
  and in Σ.  Source arguments carry explicit language-membership guards.

  Status: syntax conversions for later UI, EG, and LL transport, not H
  theoremhood.  Paper-defined → is not replaced by primitive PImp.
\<close>

lemma source_target_app_language:
  assumes F: "pterm_in_language \<Sigma> \<Gamma> F (Arr \<sigma> \<tau>)"
    and A: "pterm_in_language \<Sigma> \<Gamma> A \<sigma>"
  shows "pterm_in_language \<Sigma> \<Gamma> (PApp F A) \<tau>"
proof -
  have ft: "has_ptype \<Gamma> F (Arr \<sigma> \<tau>)"
    using F unfolding pterm_in_language_def by (rule conjunct1)
  have at: "has_ptype \<Gamma> A \<sigma>"
    using A unfolding pterm_in_language_def by (rule conjunct1)
  have fs: "pterm_in_signature \<Sigma> F"
    using F unfolding pterm_in_language_def by (rule conjunct2)
  have asig: "pterm_in_signature \<Sigma> A"
    using A unfolding pterm_in_language_def by (rule conjunct2)
  show ?thesis unfolding pterm_in_language_def
    by (rule conjI[OF has_ptype.PApp[OF ft at]]) (simp add: fs asig)
qed

lemma source_target_subst0_signature:
  assumes body: "pterm_in_signature \<Sigma> B" and arg: "pterm_in_signature \<Sigma> A"
  shows "pterm_in_signature \<Sigma> (psubst0 A B)"
  unfolding psubst0_def
proof (rule psubst_signature[OF body])
  fix n
  show "pterm_in_signature \<Sigma> (case_nat A PVar n)" by (cases n) (simp_all add: arg)
qed

lemma source_target_beta_step:
  assumes start: "pterm_in_language \<Sigma> \<Gamma> M \<tau>"
    and finish: "pterm_in_signature \<Sigma> N"
    and step: "pcompatible_step pbeta_contract M N"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M N"
proof -
  have mt: "has_ptype \<Gamma> M \<tau>" using start unfolding pterm_in_language_def by (rule conjunct1)
  have ms: "pterm_in_signature \<Sigma> M"
    using start unfolding pterm_in_language_def by (rule conjunct2)
  have nt: "has_ptype \<Gamma> N \<tau>"
    by (rule pcompatible_preserves_typing[OF step pbeta_preserves_typing mt])
  show ?thesis by (rule pbeta_eta_equiv_in_signature.Beta[OF mt nt ms finish step])
qed

lemma source_target_unary_beta:
  assumes head: "pterm_in_language \<Sigma> \<Gamma> (PLam \<sigma> B) (Arr \<sigma> \<tau>)"
    and arg: "pterm_in_language \<Sigma> \<Gamma> A \<sigma>"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau>
    (PApp (PLam \<sigma> B) A) (psubst0 A B)"
proof -
  have start: "pterm_in_language \<Sigma> \<Gamma> (PApp (PLam \<sigma> B) A) \<tau>"
    by (rule source_target_app_language[OF head arg])
  have bs: "pterm_in_signature \<Sigma> B"
    using conjunct2[OF head[unfolded pterm_in_language_def]]
    by (simp only: pterm_in_signature.simps)
  have asig: "pterm_in_signature \<Sigma> A"
    using arg unfolding pterm_in_language_def by (rule conjunct2)
  have finish: "pterm_in_signature \<Sigma> (psubst0 A B)"
    by (rule source_target_subst0_signature[OF bs asig])
  have step: "pcompatible_step pbeta_contract (PApp (PLam \<sigma> B) A) (psubst0 A B)"
    by (rule pcompatible_step.root[where R=pbeta_contract and
      M="PApp (PLam \<sigma> B) A" and N="psubst0 A B", OF pbeta_contract.beta])
  show ?thesis by (rule source_target_beta_step[OF start finish step])
qed

lemma source_target_binary_beta:
  assumes head: "pterm_in_language \<Sigma> \<Gamma> (PLam \<sigma> (PLam \<rho> B)) (Arr \<sigma> (Arr \<rho> \<tau>))"
    and arg1: "pterm_in_language \<Sigma> \<Gamma> A \<sigma>"
    and arg2: "pterm_in_language \<Sigma> \<Gamma> C \<rho>"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau>
    (PApp (PApp (PLam \<sigma> (PLam \<rho> B)) A) C)
    (psubst0 C (psubst (plift_subst (case_nat A PVar)) B))"
proof -
  let ?H = "psubst (plift_subst (case_nat A PVar)) B"
  let ?M = "PApp (PApp (PLam \<sigma> (PLam \<rho> B)) A) C"
  let ?I = "PApp (PLam \<rho> ?H) C"
  have start: "pterm_in_language \<Sigma> \<Gamma> ?M \<tau>"
    by (rule source_target_app_language[OF source_target_app_language[OF head arg1] arg2])
  have bs: "pterm_in_signature \<Sigma> (PLam \<rho> B)"
    using conjunct2[OF head[unfolded pterm_in_language_def]]
    by (simp only: pterm_in_signature.simps)
  have asig: "pterm_in_signature \<Sigma> A"
    using arg1 unfolding pterm_in_language_def by (rule conjunct2)
  have cs: "pterm_in_signature \<Sigma> C"
    using arg2 unfolding pterm_in_language_def by (rule conjunct2)
  have hs: "pterm_in_signature \<Sigma> ?H"
    using source_target_subst0_signature[OF bs asig]
    by (simp only: psubst0_def psubst.simps pterm_in_signature.simps)
  have isig: "pterm_in_signature \<Sigma> ?I" by (simp add: hs cs)
  have root: "pbeta_contract (PApp (PLam \<sigma> (PLam \<rho> B)) A) (PLam \<rho> ?H)"
    using pbeta_contract.beta[where \<sigma>=\<sigma> and M="PLam \<rho> B" and N=A]
    by (simp only: psubst0_def psubst.simps)
  have first_step: "pcompatible_step pbeta_contract ?M ?I"
    by (rule pcompatible_step.App_left[OF pcompatible_step.root[where R=pbeta_contract
      and M="PApp (PLam \<sigma> (PLam \<rho> B)) A" and N="PLam \<rho> ?H", OF root]])
  have first: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> ?M ?I"
    by (rule source_target_beta_step[OF start isig first_step])
  have it: "has_ptype \<Gamma> ?I \<tau>"
    by (rule conjunct1[OF conjunct2[OF pbeta_eta_equiv_in_signature_data[OF first]]])
  have il: "pterm_in_language \<Sigma> \<Gamma> ?I \<tau>"
    unfolding pterm_in_language_def by (rule conjI[OF it isig])
  have final_names: "pterm_in_signature \<Sigma> (psubst0 C ?H)"
    by (rule source_target_subst0_signature[OF hs cs])
  have second_step: "pcompatible_step pbeta_contract ?I (psubst0 C ?H)"
    by (rule pcompatible_step.root[where R=pbeta_contract and
      M="?I" and N="psubst0 C ?H", OF pbeta_contract.beta])
  have second: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> ?I (psubst0 C ?H)"
    by (rule source_target_beta_step[OF il final_names second_step])
  show ?thesis by (rule pbeta_eta_equiv_in_signature.Trans[OF first second])
qed

lemma source_target_subst_shift:
  "psubst (case_nat T PVar) (prename Suc M) = M"
  using psubst0_pshift[where T=T and M=M] by (simp only: psubst0_def pshift_def)

lemma paper_logical_translation_language:
  "pterm_in_language \<Sigma> \<Gamma> (paper_logical_translation l) (paper_logical_type l)"
  unfolding pterm_in_language_def
  by (rule conjI[OF paper_logical_translation_type paper_logical_translation_signature])

lemma book_minimal_logical_translation_language:
  "pterm_in_language \<Sigma> \<Gamma> (book_minimal_logical_translation l) (book_minimal_logical_type l)"
  unfolding pterm_in_language_def
  by (rule conjI[OF book_minimal_logical_translation_type book_minimal_logical_translation_signature])

subsection \<open>The paper's saturated propositional and identity operations\<close>

text \<open>
  ⟦¬A⟧ ≡β ¬⟦A⟧, ⟦A ∧ B⟧ ≡β ⟦A⟧ ∧ ⟦B⟧, and similarly
  for ∨ and =σ (Bacon–Dorr pp. 5–6).  The left sides below retain ordinary
  SApp applications of first-class SLogical constants.

  Isabelle representation: the right sides use expanded target constructors.
  Status: signature-guarded β conversions, not general extensionality.
\<close>

lemma paper_not_application:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (SApp (SLogical SNot) A)) (PNeg (paper_to_pterm A))"
proof -
  have head: "pterm_in_language \<Sigma> \<Gamma> (PLam Prop (PNeg (PVar 0))) (Arr Prop Prop)"
    using paper_logical_translation_language[where l=SNot] by simp
  note conv = source_target_unary_beta[OF head iffD2[OF paper_to_pterm_language_iff A]]
  show ?thesis using conv by (simp add: psubst0_def)
qed

lemma paper_and_application:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (SApp (SApp (SLogical SAnd) A) B)) (PConj (paper_to_pterm A) (paper_to_pterm B))"
proof -
  have head: "pterm_in_language \<Sigma> \<Gamma> (PLam Prop (PLam Prop (PConj (PVar 1) (PVar 0))))
    (Arr Prop (Arr Prop Prop))"
    using paper_logical_translation_language[where l=SAnd] by simp
  note conv = source_target_binary_beta[OF head iffD2[OF paper_to_pterm_language_iff A]
    iffD2[OF paper_to_pterm_language_iff B]]
  show ?thesis using conv by (simp add: psubst0_def source_target_subst_shift)
qed

lemma paper_or_application:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (SApp (SApp (SLogical SOr) A) B)) (PDisj (paper_to_pterm A) (paper_to_pterm B))"
proof -
  have head: "pterm_in_language \<Sigma> \<Gamma> (PLam Prop (PLam Prop (PDisj (PVar 1) (PVar 0))))
    (Arr Prop (Arr Prop Prop))"
    using paper_logical_translation_language[where l=SOr] by simp
  note conv = source_target_binary_beta[OF head iffD2[OF paper_to_pterm_language_iff A]
    iffD2[OF paper_to_pterm_language_iff B]]
  show ?thesis using conv by (simp add: psubst0_def source_target_subst_shift)
qed

lemma paper_eq_application:
  assumes A: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
    and B: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B \<sigma>"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (SApp (SApp (SLogical (SEq \<sigma>)) A) B)) (PEq \<sigma> (paper_to_pterm A) (paper_to_pterm B))"
proof -
  have head: "pterm_in_language \<Sigma> \<Gamma> (PLam \<sigma> (PLam \<sigma> (PEq \<sigma> (PVar 1) (PVar 0))))
    (Arr \<sigma> (Arr \<sigma> Prop))"
    using paper_logical_translation_language[where l="SEq \<sigma>"] by simp
  note conv = source_target_binary_beta[OF head iffD2[OF paper_to_pterm_language_iff A]
    iffD2[OF paper_to_pterm_language_iff B]]
  show ?thesis using conv by (simp add: psubst0_def source_target_subst_shift)
qed

subsection \<open>Quantifiers applied to predicates and the book basis\<close>

text \<open>
  ∀σF and ∃σF apply a quantifier constant to a predicate F:σ → t
  (Bacon–Dorr Figure 2).  Their translations become binder formulas
  ∀x:σ.⟦F⟧x and ∃x:σ.⟦F⟧x.  The final two lemmas use the book's
  distinct primitive → and ∀σ (Bacon Chapters 4–5).

  Isabelle representation: pshift moves the old free slots past x; PVar 0
  is x.  Status: exact guarded conversions in each basis, with no claim
  that book-defined Leibniz identity has BBK actual-equality semantics.
\<close>

lemma paper_all_application:
  assumes F: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (SApp (SLogical (SAll \<sigma>)) F))
    (PForall \<sigma> (PApp (pshift (paper_to_pterm F)) (PVar 0)))"
proof -
  have head: "pterm_in_language \<Sigma> \<Gamma>
    (PLam (Arr \<sigma> Prop) (PForall \<sigma> (PApp (PVar 1) (PVar 0)))) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_logical_translation_language[where l="SAll \<sigma>"] by simp
  note conv = source_target_unary_beta[OF head iffD2[OF paper_to_pterm_language_iff F]]
  show ?thesis using conv by (simp add: psubst0_def pshift_def)
qed

lemma paper_ex_application:
  assumes F: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (paper_to_pterm (SApp (SLogical (SEx \<sigma>)) F))
    (PExists \<sigma> (PApp (pshift (paper_to_pterm F)) (PVar 0)))"
proof -
  have head: "pterm_in_language \<Sigma> \<Gamma>
    (PLam (Arr \<sigma> Prop) (PExists \<sigma> (PApp (PVar 1) (PVar 0)))) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_logical_translation_language[where l="SEx \<sigma>"] by simp
  note conv = source_target_unary_beta[OF head iffD2[OF paper_to_pterm_language_iff F]]
  show ?thesis using conv by (simp add: psubst0_def pshift_def)
qed

lemma book_imp_application:
  assumes A: "sterm_in_language book_minimal_logical_type \<Sigma> \<Gamma> A Prop"
    and B: "sterm_in_language book_minimal_logical_type \<Sigma> \<Gamma> B Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (book_minimal_to_pterm (SApp (SApp (SLogical SImp) A) B))
    (PImp (book_minimal_to_pterm A) (book_minimal_to_pterm B))"
proof -
  have head: "pterm_in_language \<Sigma> \<Gamma> (PLam Prop (PLam Prop (PImp (PVar 1) (PVar 0))))
    (Arr Prop (Arr Prop Prop))"
    using book_minimal_logical_translation_language[where l=SImp] by simp
  note conv = source_target_binary_beta[OF head iffD2[OF book_minimal_to_pterm_language_iff A]
    iffD2[OF book_minimal_to_pterm_language_iff B]]
  show ?thesis using conv by (simp add: psubst0_def source_target_subst_shift)
qed

lemma book_all_application:
  assumes F: "sterm_in_language book_minimal_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop
    (book_minimal_to_pterm (SApp (SLogical (SBAll \<sigma>)) F))
    (PForall \<sigma> (PApp (pshift (book_minimal_to_pterm F)) (PVar 0)))"
proof -
  have head: "pterm_in_language \<Sigma> \<Gamma>
    (PLam (Arr \<sigma> Prop) (PForall \<sigma> (PApp (PVar 1) (PVar 0)))) (Arr (Arr \<sigma> Prop) Prop)"
    using book_minimal_logical_translation_language[where l="SBAll \<sigma>"] by simp
  note conv = source_target_unary_beta[OF head iffD2[OF book_minimal_to_pterm_language_iff F]]
  show ?thesis using conv by (simp add: psubst0_def pshift_def)
qed

end
