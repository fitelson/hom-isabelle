theory Bacon_Source_Conversion
  imports Bacon_Source_Substitution
    Bacon_Parametric_Signature_Development.Bacon_Parametric_BBK_Semantics
begin

section \<open>Free variables are preserved by the source translation\<close>

text \<open>
  FV(A) records free variables, as used in Bacon–Dorr Figure 2, p. 8,
  and Bacon Chapter 5.  Logical and nonlogical constants have no free
  variables; FV(λv.A) removes the variable bound by λ.

  Isabelle representation: sfv records free de Bruijn slots.  Leaving a
  binder removes slot zero and lowers the remaining slots.  The target
  function pbbk_fv uses the same convention, including inside the closed
  logical wrappers.

  Status: exact free-slot correspondence for both primitive bases.
  This is not yet a correspondence with a separate named-variable syntax.
\<close>

fun sfv :: "('c, 'l) sterm \<Rightarrow> nat set" where
  "sfv (SVar n) = {n}"
| "sfv (SConst c \<sigma>) = {}"
| "sfv (SLogical l) = {}"
| "sfv (SApp M N) = sfv M \<union> sfv N"
| "sfv (SLam \<sigma> M) = {n. Suc n \<in> sfv M}"

lemma paper_logical_translation_fv:
  "pbbk_fv (paper_logical_translation l) = {}"
  by (cases l) (simp_all add: One_nat_def)

lemma book_minimal_logical_translation_fv:
  "pbbk_fv (book_minimal_logical_translation l) = {}"
  by (cases l) (simp_all add: One_nat_def)

lemma sterm_translation_fv:
  assumes wrappers: "\<And>l. pbbk_fv (W l) = {}"
  shows "pbbk_fv (sterm_translation W A) = sfv A"
  by (induction A)
    (simp_all only: sterm_translation.simps pbbk_fv.simps sfv.simps wrappers)

lemma paper_to_pterm_fv:
  "pbbk_fv (paper_to_pterm A) = sfv A"
  by (rule sterm_translation_fv[OF paper_logical_translation_fv])

lemma book_minimal_to_pterm_fv:
  "pbbk_fv (book_minimal_to_pterm A) = sfv A"
  by (rule sterm_translation_fv[OF book_minimal_logical_translation_fv])

section \<open>Root contractions and replacement inside a term\<close>

text \<open>
  (λv.A)B →β A[B/v], and λv.Fv →η F when v is not free in F.
  A contraction may occur inside Φ[−], including beneath a binder
  (Bacon–Dorr Figure 2, pp. 7–8; Bacon Chapter 5).

  Isabelle representation: the η pattern uses sshift F beneath a fresh
  binder.  scompatible_step closes a root pattern under application and
  abstraction, the only compound constructors of the source grammar.

  Status: these root/context relations are raw pattern infrastructure.
  They are not unrestricted conversion theorems.  The equivalence relation
  below guards every step and every transitivity node by typing and Σ.
\<close>

inductive sbeta_contract :: "('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm \<Rightarrow> bool" where
  beta: "sbeta_contract (SApp (SLam \<sigma> M) N) (ssubst0 N M)"

inductive seta_contract :: "('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm \<Rightarrow> bool" where
  eta: "seta_contract (SLam \<sigma> (SApp (sshift F) (SVar 0))) F"

inductive scompatible_step ::
  "(('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm \<Rightarrow> bool) \<Rightarrow>
    ('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm \<Rightarrow> bool"
  for R :: "('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm \<Rightarrow> bool" where
  root: "R M N \<Longrightarrow> scompatible_step R M N"
| App_left: "scompatible_step R M M' \<Longrightarrow>
    scompatible_step R (SApp M N) (SApp M' N)"
| App_right: "scompatible_step R N N' \<Longrightarrow>
    scompatible_step R (SApp M N) (SApp M N')"
| Lam_body: "scompatible_step R M M' \<Longrightarrow>
    scompatible_step R (SLam \<sigma> M) (SLam \<sigma> M')"

lemma sterm_translation_beta:
  assumes step: "sbeta_contract M N"
    and ren: "\<And>r l. prename r (W l) = W l"
    and sub: "\<And>s l. psubst s (W l) = W l"
  shows "pbeta_contract (sterm_translation W M) (sterm_translation W N)"
  using step
  by (induction rule: sbeta_contract.induct)
    (simp only: sterm_translation.simps sterm_translation_subst0[OF ren sub];
      rule pbeta_contract.beta)

lemma sterm_translation_eta:
  assumes step: "seta_contract M N"
    and ren: "\<And>r l. prename r (W l) = W l"
  shows "peta_contract (sterm_translation W M) (sterm_translation W N)"
  using step
  by (induction rule: seta_contract.induct)
    (simp only: sterm_translation.simps sterm_translation_shift[OF ren];
      rule peta_contract.eta)

lemma sterm_translation_compatible:
  assumes step: "scompatible_step R M N"
    and roots: "\<And>A B. R A B \<Longrightarrow>
      Q (sterm_translation W A) (sterm_translation W B)"
  shows "pcompatible_step Q (sterm_translation W M) (sterm_translation W N)"
  using step
proof (induction rule: scompatible_step.induct)
  case (root M N)
  have translated: "Q (sterm_translation W M) (sterm_translation W N)"
    by (rule roots[OF root.hyps])
  show ?case by (rule pcompatible_step.root[where R=Q and
      M="sterm_translation W M" and N="sterm_translation W N", OF translated])
next
  case App_left
  show ?case unfolding sterm_translation.simps
    by (rule pcompatible_step.App_left[OF App_left.IH])
next
  case App_right
  show ?case unfolding sterm_translation.simps
    by (rule pcompatible_step.App_right[OF App_right.IH])
next
  case Lam_body
  show ?case unfolding sterm_translation.simps
    by (rule pcompatible_step.Lam_body[OF Lam_body.IH])
qed

lemma sterm_translation_beta_step:
  fixes W :: "'l \<Rightarrow> 'c pterm" and M N :: "('c, 'l) sterm"
  assumes step: "scompatible_step sbeta_contract M N"
    and ren: "\<And>r l. prename r (W l) = W l"
    and sub: "\<And>s l. psubst s (W l) = W l"
  shows "pcompatible_step pbeta_contract (sterm_translation W M) (sterm_translation W N)"
proof (rule sterm_translation_compatible[OF step])
  fix A B :: "('c, 'l) sterm"
  assume root: "sbeta_contract A B"
  show "pbeta_contract (sterm_translation W A) (sterm_translation W B)"
    by (rule sterm_translation_beta[OF root ren sub])
qed

lemma sterm_translation_eta_step:
  fixes W :: "'l \<Rightarrow> 'c pterm" and M N :: "('c, 'l) sterm"
  assumes step: "scompatible_step seta_contract M N"
    and ren: "\<And>r l. prename r (W l) = W l"
  shows "pcompatible_step peta_contract (sterm_translation W M) (sterm_translation W N)"
proof (rule sterm_translation_compatible[OF step])
  fix A B :: "('c, 'l) sterm"
  assume root: "seta_contract A B"
  show "peta_contract (sterm_translation W A) (sterm_translation W B)"
    by (rule sterm_translation_eta[OF root ren])
qed

section \<open>Conversion within the declared language\<close>

text \<open>
  A ≡βη B is conversion between terms of a common type in ℒ(Σ).
  Bacon–Dorr Definition 3.1(ii.d) restricts the semantic conversion clause
  to this language; Figure 2 supplies the contextual β and η patterns.
  The book's Chapter 5 uses the same binding conversions in its own basis.

  Isabelle representation: sbeta_eta_equiv_in_signature fixes the logical
  type function and Σ.  Each generating step guards both endpoints.
  Symmetry and transitivity retain these guards, including the intermediate
  term in transitivity.  No raw equivalence relation is introduced here.

  Status: forward conversion preservation into the signature-indexed target
  relation, separately for paper and book syntax.  This does not prove
  conversion reflection, H-proof preservation, or book-model semantics.
\<close>

inductive sbeta_eta_equiv_in_signature ::
  "('l \<Rightarrow> otype) \<Rightarrow> 'c ssignature \<Rightarrow> ctx \<Rightarrow> otype \<Rightarrow>
    ('c, 'l) sterm \<Rightarrow> ('c, 'l) sterm \<Rightarrow> bool"
  for logical_type :: "'l \<Rightarrow> otype" and \<Sigma> :: "'c ssignature" where
  Refl: "has_stype logical_type \<Gamma> M \<tau> \<Longrightarrow> sterm_in_signature \<Sigma> M \<Longrightarrow>
    sbeta_eta_equiv_in_signature logical_type \<Sigma> \<Gamma> \<tau> M M"
| Beta: "has_stype logical_type \<Gamma> M \<tau> \<Longrightarrow> has_stype logical_type \<Gamma> N \<tau> \<Longrightarrow>
    sterm_in_signature \<Sigma> M \<Longrightarrow> sterm_in_signature \<Sigma> N \<Longrightarrow>
    scompatible_step sbeta_contract M N \<Longrightarrow>
    sbeta_eta_equiv_in_signature logical_type \<Sigma> \<Gamma> \<tau> M N"
| Eta: "has_stype logical_type \<Gamma> M \<tau> \<Longrightarrow> has_stype logical_type \<Gamma> N \<tau> \<Longrightarrow>
    sterm_in_signature \<Sigma> M \<Longrightarrow> sterm_in_signature \<Sigma> N \<Longrightarrow>
    scompatible_step seta_contract M N \<Longrightarrow>
    sbeta_eta_equiv_in_signature logical_type \<Sigma> \<Gamma> \<tau> M N"
| Sym: "sbeta_eta_equiv_in_signature logical_type \<Sigma> \<Gamma> \<tau> M N \<Longrightarrow>
    sbeta_eta_equiv_in_signature logical_type \<Sigma> \<Gamma> \<tau> N M"
| Trans: "sbeta_eta_equiv_in_signature logical_type \<Sigma> \<Gamma> \<tau> M N \<Longrightarrow>
    sbeta_eta_equiv_in_signature logical_type \<Sigma> \<Gamma> \<tau> N P \<Longrightarrow>
    sbeta_eta_equiv_in_signature logical_type \<Sigma> \<Gamma> \<tau> M P"

lemma sbeta_eta_equiv_in_signature_language:
  assumes "sbeta_eta_equiv_in_signature logical_type \<Sigma> \<Gamma> \<tau> M N"
  shows "sterm_in_language logical_type \<Sigma> \<Gamma> M \<tau> \<and>
    sterm_in_language logical_type \<Sigma> \<Gamma> N \<tau>"
  using assms
proof (induction rule: sbeta_eta_equiv_in_signature.induct)
  case (Refl \<Gamma> M \<tau>)
  have member: "sterm_in_language logical_type \<Sigma> \<Gamma> M \<tau>"
    unfolding sterm_in_language_def by (rule conjI[OF Refl.hyps])
  show ?case by (rule conjI[OF member member])
next
  case Beta
  show ?case unfolding sterm_in_language_def
    by (rule conjI[OF conjI[OF Beta.hyps(1,3)] conjI[OF Beta.hyps(2,4)]])
next
  case Eta
  show ?case unfolding sterm_in_language_def
    by (rule conjI[OF conjI[OF Eta.hyps(1,3)] conjI[OF Eta.hyps(2,4)]])
next
  case Sym
  show ?case by (rule conjI[OF conjunct2[OF Sym.IH] conjunct1[OF Sym.IH]])
next
  case Trans
  show ?case by (rule conjI[OF conjunct1[OF Trans.IH(1)] conjunct2[OF Trans.IH(2)]])
qed

lemma sterm_translation_conversion:
  fixes W :: "'l \<Rightarrow> 'c pterm" and M N :: "('c, 'l) sterm"
  assumes step: "sbeta_eta_equiv_in_signature logical_type \<Sigma> \<Gamma> \<tau> M N"
    and wrapper_types: "\<And>\<Delta> l. has_ptype \<Delta> (W l) (logical_type l)"
    and wrapper_names: "\<And>l. pterm_in_signature \<Sigma> (W l)"
    and wrapper_ren: "\<And>r l. prename r (W l) = W l"
    and wrapper_sub: "\<And>s l. psubst s (W l) = W l"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau>
    (sterm_translation W M) (sterm_translation W N)"
proof -
  have types: "\<And>\<Delta> A \<rho>. has_stype logical_type \<Delta> A \<rho> \<Longrightarrow>
    has_ptype \<Delta> (sterm_translation W A) \<rho>"
  proof -
    fix \<Delta> \<rho> and A :: "('c, 'l) sterm"
    assume typed: "has_stype logical_type \<Delta> A \<rho>"
    show "has_ptype \<Delta> (sterm_translation W A) \<rho>"
      by (rule sterm_translation_type[OF typed wrapper_types])
  qed
  have names: "\<And>A. sterm_in_signature \<Sigma> A \<Longrightarrow>
    pterm_in_signature \<Sigma> (sterm_translation W A)"
    by (simp only: sterm_translation_signature_iff[OF wrapper_names])
  show ?thesis using step
  proof (induction rule: sbeta_eta_equiv_in_signature.induct)
    case Refl
    show ?case by (rule pbeta_eta_equiv_in_signature.Refl[
        OF types[OF Refl.hyps(1)] names[OF Refl.hyps(2)]])
  next
    case Beta
    show ?case by (rule pbeta_eta_equiv_in_signature.Beta[
        OF types[OF Beta.hyps(1)] types[OF Beta.hyps(2)]
        names[OF Beta.hyps(3)] names[OF Beta.hyps(4)]
        sterm_translation_beta_step[OF Beta.hyps(5) wrapper_ren wrapper_sub]])
  next
    case Eta
    show ?case by (rule pbeta_eta_equiv_in_signature.Eta[
        OF types[OF Eta.hyps(1)] types[OF Eta.hyps(2)]
        names[OF Eta.hyps(3)] names[OF Eta.hyps(4)]
        sterm_translation_eta_step[OF Eta.hyps(5) wrapper_ren]])
  next
    case Sym
    show ?case by (rule pbeta_eta_equiv_in_signature.Sym[OF Sym.IH])
  next
    case Trans
    show ?case by (rule pbeta_eta_equiv_in_signature.Trans[OF Trans.IH])
  qed
qed

theorem paper_to_pterm_conversion:
  assumes "sbeta_eta_equiv_in_signature paper_logical_type \<Sigma> \<Gamma> \<tau> M N"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> (paper_to_pterm M) (paper_to_pterm N)"
  by (rule sterm_translation_conversion[OF assms paper_logical_translation_type
      paper_logical_translation_signature paper_logical_translation_rename
      paper_logical_translation_subst])

theorem book_minimal_to_pterm_conversion:
  assumes "sbeta_eta_equiv_in_signature book_minimal_logical_type \<Sigma> \<Gamma> \<tau> M N"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau>
    (book_minimal_to_pterm M) (book_minimal_to_pterm N)"
  by (rule sterm_translation_conversion[OF assms book_minimal_logical_translation_type
      book_minimal_logical_translation_signature book_minimal_logical_translation_rename
      book_minimal_logical_translation_subst])

end
