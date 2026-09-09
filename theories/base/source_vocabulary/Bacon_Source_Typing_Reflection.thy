theory Bacon_Source_Typing_Reflection
  imports Bacon_Source_Conversion
begin

section \<open>The closed wrappers have exactly their declared types\<close>

text \<open>
  Each constant has a fixed type: for example, =σ:σ → σ → t and
  ∀σ:(σ → t) → t (Bacon–Dorr §1.1, pp. 5–6).  The book's Λ⁻ has
  →:t → t → t and ∀σ:(σ → t) → t (Bacon pp. 92–93; Chapter 5).

  Isabelle representation: constructor-typing inversions show that each
  closed wrapper has no type other than its declared logical type.  These
  are elementary syntax arguments, with no canonical-domain dependency.

  Status: uniqueness of wrapper types only.  No identity between the
  paper's defined implication and the book's primitive implication follows.
\<close>

lemma source_pconst_type:
  assumes "has_ptype \<Gamma> (PConst c \<sigma>) \<tau>"
  shows "\<tau> = \<sigma>"
  using assms by (cases rule: has_ptype.cases) assumption

lemma paper_logical_translation_type_unique:
  assumes "has_ptype \<Gamma> (paper_logical_translation l) \<tau>"
  shows "\<tau> = paper_logical_type l"
  using assms
  by (cases l)
    (simp_all add: ptype_lam_iff ptype_neg_iff ptype_conj_iff ptype_disj_iff
      ptype_forall_iff ptype_exists_iff ptype_eq_iff)

lemma book_minimal_logical_translation_type_unique:
  assumes "has_ptype \<Gamma> (book_minimal_logical_translation l) \<tau>"
  shows "\<tau> = book_minimal_logical_type l"
  using assms
  by (cases l) (simp_all add: ptype_lam_iff ptype_imp_iff ptype_forall_iff)

section \<open>Typing reflection through the five-constructor translation\<close>

text \<open>
  Γ ⊢ ⟦A⟧:τ iff Γ ⊢ A:τ.  Here ⟦A⟧ is syntax translation, not
  semantic denotation.  The source formation rules are Bacon–Dorr §1.1,
  pp. 5–6, and Bacon Chapter 4.

  Isabelle representation: the reverse direction is induction on the raw
  source term.  Application and abstraction use target typing inversions;
  the logical-constant case uses the wrapper's unique type.

  Status: exact typing correspondence for both bases.  This neither proves
  conversion reflection nor transports H proofs or models.
\<close>

lemma sterm_translation_reflects_typing:
  assumes typed: "has_ptype \<Gamma> (sterm_translation W A) \<tau>"
    and wrappers: "\<And>\<Delta> l \<rho>. has_ptype \<Delta> (W l) \<rho> \<Longrightarrow> \<rho> = logical_type l"
  shows "has_stype logical_type \<Gamma> A \<tau>"
  using typed
proof (induction A arbitrary: \<Gamma> \<tau>)
  case (SVar n)
  have look: "lookup \<Gamma> n = Some \<tau>"
    using SVar.prems by (simp only: sterm_translation.simps pvar_typing_iff)
  show ?case by (rule has_stype.Var[OF look])
next
  case (SConst c \<sigma>)
  have target: "has_ptype \<Gamma> (PConst c \<sigma>) \<tau>"
    using SConst.prems by (simp only: sterm_translation.simps)
  have eq: "\<tau> = \<sigma>" by (rule source_pconst_type[OF target])
  show ?case unfolding eq by (rule has_stype.Const)
next
  case (SLogical l)
  have target: "has_ptype \<Gamma> (W l) \<tau>"
    using SLogical.prems by (simp only: sterm_translation.simps)
  have eq: "\<tau> = logical_type l" by (rule wrappers[OF target])
  show ?case unfolding eq by (rule has_stype.Logical)
next
  case (SApp M N)
  have target: "has_ptype \<Gamma> (PApp (sterm_translation W M) (sterm_translation W N)) \<tau>"
    using SApp.prems by (simp only: sterm_translation.simps)
  obtain \<sigma> where M_type: "has_ptype \<Gamma> (sterm_translation W M) (Arr \<sigma> \<tau>)"
    and N_type: "has_ptype \<Gamma> (sterm_translation W N) \<sigma>"
    using target[unfolded ptype_app_iff] by (elim exE conjE)
  have M_source: "has_stype logical_type \<Gamma> M (Arr \<sigma> \<tau>)"
    by (rule SApp.IH(1)[OF M_type])
  have N_source: "has_stype logical_type \<Gamma> N \<sigma>"
    by (rule SApp.IH(2)[OF N_type])
  show ?case by (rule has_stype.App[OF M_source N_source])
next
  case (SLam \<sigma> M)
  have target: "has_ptype \<Gamma> (PLam \<sigma> (sterm_translation W M)) \<tau>"
    using SLam.prems by (simp only: sterm_translation.simps)
  obtain \<rho> where eq: "\<tau> = Arr \<sigma> \<rho>"
    and body: "has_ptype (\<sigma> # \<Gamma>) (sterm_translation W M) \<rho>"
    using target[unfolded ptype_lam_iff] by (elim exE conjE)
  have source: "has_stype logical_type (\<sigma> # \<Gamma>) M \<rho>"
    by (rule SLam.IH[OF body])
  show ?case unfolding eq by (rule has_stype.Lam[OF source])
qed

lemma sterm_translation_type_iff:
  assumes types: "\<And>\<Delta> l. has_ptype \<Delta> (W l) (logical_type l)"
    and unique: "\<And>\<Delta> l \<rho>. has_ptype \<Delta> (W l) \<rho> \<Longrightarrow> \<rho> = logical_type l"
  shows "has_ptype \<Gamma> (sterm_translation W A) \<tau> \<longleftrightarrow>
    has_stype logical_type \<Gamma> A \<tau>"
proof
  assume "has_ptype \<Gamma> (sterm_translation W A) \<tau>"
  then show "has_stype logical_type \<Gamma> A \<tau>"
    by (rule sterm_translation_reflects_typing[OF _ unique])
next
  assume "has_stype logical_type \<Gamma> A \<tau>"
  then show "has_ptype \<Gamma> (sterm_translation W A) \<tau>"
    by (rule sterm_translation_type[OF _ types])
qed

lemma paper_to_pterm_type_iff:
  "has_ptype \<Gamma> (paper_to_pterm A) \<tau> \<longleftrightarrow>
    has_stype paper_logical_type \<Gamma> A \<tau>"
  by (rule sterm_translation_type_iff[OF paper_logical_translation_type
      paper_logical_translation_type_unique])

lemma book_minimal_to_pterm_type_iff:
  "has_ptype \<Gamma> (book_minimal_to_pterm A) \<tau> \<longleftrightarrow>
    has_stype book_minimal_logical_type \<Gamma> A \<tau>"
  by (rule sterm_translation_type_iff[OF book_minimal_logical_translation_type
      book_minimal_logical_translation_type_unique])

subsection \<open>Exact membership in the declared language\<close>

text \<open>
  A:τ belongs to ℒ(Σ) iff its translation belongs to the corresponding
  target language at τ.  The stock Σσ is unchanged, as in Bacon–Dorr
  §1.1, p. 6, and Definition 3.1.

  Isabelle representation: combine typing reflection/preservation with the
  already proved exact nonlogical-signature correspondence.

  Status: language membership, including ill-typed and out-of-signature
  exclusions.  No source/target proof-theoretic conservativity is asserted.
\<close>

theorem paper_to_pterm_language_iff:
  "pterm_in_language \<Sigma> \<Gamma> (paper_to_pterm A) \<tau> \<longleftrightarrow>
    sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<tau>"
  by (simp only: pterm_in_language_def sterm_in_language_def
      paper_to_pterm_type_iff paper_to_pterm_signature_iff)

theorem book_minimal_to_pterm_language_iff:
  "pterm_in_language \<Sigma> \<Gamma> (book_minimal_to_pterm A) \<tau> \<longleftrightarrow>
    sterm_in_language book_minimal_logical_type \<Sigma> \<Gamma> A \<tau>"
  by (simp only: pterm_in_language_def sterm_in_language_def
      book_minimal_to_pterm_type_iff book_minimal_to_pterm_signature_iff)

end
