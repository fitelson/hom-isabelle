theory Bacon_Source_Translation
  imports Bacon_Source_Syntax
    Bacon_Parametric_Signature_Development.Bacon_Parametric_Syntax
begin

section \<open>Closed representations of the source logical constants\<close>

text \<open>
  ¬, ∧, ∨, ∀σ, ∃σ, and =σ are first-class terms in Bacon–Dorr §1.1,
  pp. 5–6.  We write ⟦A⟧ for syntax translation, not model denotation.
  For example, ⟦=σ⟧ is λx:σ.λy:σ.x =σ y, so =σ A remains a
  partially applied predicate.

  Isabelle representation: each primitive maps to a closed pterm wrapper.
  Empty-context typing expresses closedness here; no free-variable or
  substitution operation is introduced.  The stronger wrapper-type lemmas
  allow every ambient context Γ.

  Status: representation and typing only.  No βη correspondence, identity
  of operations, H-proof transport, or semantic preservation is claimed.
\<close>

fun paper_logical_translation :: "paper_logical \<Rightarrow> 'c pterm" where
  "paper_logical_translation SNot = PLam Prop (PNeg (PVar 0))"
| "paper_logical_translation SAnd =
    PLam Prop (PLam Prop (PConj (PVar 1) (PVar 0)))"
| "paper_logical_translation SOr =
    PLam Prop (PLam Prop (PDisj (PVar 1) (PVar 0)))"
| "paper_logical_translation (SAll \<sigma>) =
    PLam (Arr \<sigma> Prop) (PForall \<sigma> (PApp (PVar 1) (PVar 0)))"
| "paper_logical_translation (SEx \<sigma>) =
    PLam (Arr \<sigma> Prop) (PExists \<sigma> (PApp (PVar 1) (PVar 0)))"
| "paper_logical_translation (SEq \<sigma>) =
    PLam \<sigma> (PLam \<sigma> (PEq \<sigma> (PVar 1) (PVar 0)))"

lemma paper_logical_translation_type:
  "has_ptype \<Gamma> (paper_logical_translation l) (paper_logical_type l)"
proof (cases l)
  case SNot
  show ?thesis unfolding SNot paper_logical_translation.simps paper_logical_type.simps
    by (intro has_ptype.PLam has_ptype.PNeg has_ptype.PVar) (rule lookup_Cons_0)
next
  case SAnd
  show ?thesis unfolding SAnd paper_logical_translation.simps paper_logical_type.simps
    by (intro has_ptype.PLam has_ptype.PConj has_ptype.PVar)
      (simp_all add: lookup_def)
next
  case SOr
  show ?thesis unfolding SOr paper_logical_translation.simps paper_logical_type.simps
    by (intro has_ptype.PLam has_ptype.PDisj has_ptype.PVar)
      (simp_all add: lookup_def)
next
  case (SAll \<sigma>)
  show ?thesis unfolding SAll paper_logical_translation.simps paper_logical_type.simps
    by (intro has_ptype.PLam has_ptype.PForall has_ptype.PApp has_ptype.PVar)
      (simp_all add: lookup_def)
next
  case (SEx \<sigma>)
  show ?thesis unfolding SEx paper_logical_translation.simps paper_logical_type.simps
    by (intro has_ptype.PLam has_ptype.PExists has_ptype.PApp has_ptype.PVar)
      (simp_all add: lookup_def)
next
  case (SEq \<sigma>)
  show ?thesis unfolding SEq paper_logical_translation.simps paper_logical_type.simps
    by (intro has_ptype.PLam has_ptype.PEq has_ptype.PVar)
      (simp_all add: lookup_def)
qed

lemma paper_logical_translation_closed:
  "has_ptype [] (paper_logical_translation l) (paper_logical_type l)"
  by (rule paper_logical_translation_type)

lemma paper_logical_translation_signature:
  "pterm_in_signature \<Sigma> (paper_logical_translation l)"
  by (cases l)
    (simp_all add: paper_logical_translation.simps)

subsection \<open>The book's primitive implication remains distinct\<close>

text \<open>
  Λ⁻ contains → and ∀σ (Bacon pp. 92–93 and Chapter 5).
  Here ⟦→⟧ is λp:t.λq:t.p → q.  The paper instead defines its →
  as λpq.¬p ∨ q (Figure 1); that abbreviation must first be expanded
  in the paper syntax.

  Isabelle representation: book_minimal_logical_translation is a separate
  function on a separate logical-symbol datatype.

  Status: these wrappers do not identify the two choices of implication.
  Bacon's general-model interpretation (Definition 15.1) is not supplied.
\<close>

fun book_minimal_logical_translation :: "book_minimal_logical \<Rightarrow> 'c pterm" where
  "book_minimal_logical_translation SImp =
    PLam Prop (PLam Prop (PImp (PVar 1) (PVar 0)))"
| "book_minimal_logical_translation (SBAll \<sigma>) =
    PLam (Arr \<sigma> Prop) (PForall \<sigma> (PApp (PVar 1) (PVar 0)))"

lemma book_minimal_logical_translation_type:
  "has_ptype \<Gamma> (book_minimal_logical_translation l) (book_minimal_logical_type l)"
proof (cases l)
  case SImp
  show ?thesis unfolding SImp book_minimal_logical_translation.simps
    book_minimal_logical_type.simps
    by (intro has_ptype.PLam has_ptype.PImp has_ptype.PVar)
      (simp_all add: lookup_def)
next
  case (SBAll \<sigma>)
  show ?thesis unfolding SBAll book_minimal_logical_translation.simps
    book_minimal_logical_type.simps
    by (intro has_ptype.PLam has_ptype.PForall has_ptype.PApp has_ptype.PVar)
      (simp_all add: lookup_def)
qed

lemma book_minimal_logical_translation_closed:
  "has_ptype [] (book_minimal_logical_translation l) (book_minimal_logical_type l)"
  by (rule book_minimal_logical_translation_type)

lemma book_minimal_logical_translation_signature:
  "pterm_in_signature \<Sigma> (book_minimal_logical_translation l)"
  by (cases l)
    (simp_all add: book_minimal_logical_translation.simps)

section \<open>A homomorphic translation of the five-constructor grammar\<close>

text \<open>
  ⟦AB⟧ = ⟦A⟧⟦B⟧ and ⟦λx:σ.A⟧ = λx:σ.⟦A⟧.
  This follows the source formation clauses (Bacon–Dorr pp. 5–6;
  Bacon Chapter 4), including applications of partially applied operators.

  Isabelle representation: sterm_translation takes a logical-wrapper map W.
  The same name carrier and de Bruijn indices are retained.  The paper and
  book abbreviations below instantiate W without mixing their vocabularies.

  Status: a total syntax map.  The following lemmas prove typing preservation
  and exact nonlogical-signature correspondence.  Typing reflection and
  substitution/conversion/proof correspondence are later obligations.
\<close>

fun sterm_translation :: "('l \<Rightarrow> 'c pterm) \<Rightarrow> ('c, 'l) sterm \<Rightarrow> 'c pterm"
  where
  "sterm_translation W (SVar n) = PVar n"
| "sterm_translation W (SConst c \<sigma>) = PConst c \<sigma>"
| "sterm_translation W (SLogical l) = W l"
| "sterm_translation W (SApp M N) =
    PApp (sterm_translation W M) (sterm_translation W N)"
| "sterm_translation W (SLam \<sigma> M) = PLam \<sigma> (sterm_translation W M)"

abbreviation paper_to_pterm :: "'c paper_term \<Rightarrow> 'c pterm" where
  "paper_to_pterm A \<equiv> sterm_translation paper_logical_translation A"

abbreviation book_minimal_to_pterm :: "'c book_minimal_term \<Rightarrow> 'c pterm" where
  "book_minimal_to_pterm A \<equiv> sterm_translation book_minimal_logical_translation A"

lemma sterm_translation_type:
  assumes typed: "has_stype logical_type \<Gamma> A \<tau>"
    and wrappers: "\<And>\<Delta> l. has_ptype \<Delta> (W l) (logical_type l)"
  shows "has_ptype \<Gamma> (sterm_translation W A) \<tau>"
  using typed
proof (induction rule: has_stype.induct)
  case Var
  show ?case unfolding sterm_translation.simps
    by (rule has_ptype.PVar[OF Var.hyps])
next
  case Const
  show ?case unfolding sterm_translation.simps by (rule has_ptype.PConst)
next
  case Logical
  show ?case unfolding sterm_translation.simps by (rule wrappers)
next
  case App
  show ?case unfolding sterm_translation.simps by (rule has_ptype.PApp[OF App.IH])
next
  case Lam
  show ?case unfolding sterm_translation.simps by (rule has_ptype.PLam[OF Lam.IH])
qed

lemma paper_to_pterm_type:
  assumes "has_stype paper_logical_type \<Gamma> A \<tau>"
  shows "has_ptype \<Gamma> (paper_to_pterm A) \<tau>"
  by (rule sterm_translation_type[OF assms paper_logical_translation_type])

lemma book_minimal_to_pterm_type:
  assumes "has_stype book_minimal_logical_type \<Gamma> A \<tau>"
  shows "has_ptype \<Gamma> (book_minimal_to_pterm A) \<tau>"
  by (rule sterm_translation_type[OF assms book_minimal_logical_translation_type])

lemma sterm_translation_signature_iff:
  assumes wrappers: "\<And>l. pterm_in_signature \<Sigma> (W l)"
  shows "pterm_in_signature \<Sigma> (sterm_translation W A) =
    sterm_in_signature \<Sigma> A"
  by (induction A)
    (simp_all only: sterm_translation.simps sterm_in_signature.simps
      pterm_in_signature.simps wrappers)

lemma paper_to_pterm_signature_iff:
  "pterm_in_signature \<Sigma> (paper_to_pterm A) = sterm_in_signature \<Sigma> A"
  by (rule sterm_translation_signature_iff[OF paper_logical_translation_signature])

lemma book_minimal_to_pterm_signature_iff:
  "pterm_in_signature \<Sigma> (book_minimal_to_pterm A) = sterm_in_signature \<Sigma> A"
  by (rule sterm_translation_signature_iff[OF book_minimal_logical_translation_signature])

lemma sterm_translation_language:
  assumes language: "sterm_in_language logical_type \<Sigma> \<Gamma> A \<tau>"
    and wrapper_types: "\<And>\<Delta> l. has_ptype \<Delta> (W l) (logical_type l)"
    and wrapper_names: "\<And>l. pterm_in_signature \<Sigma> (W l)"
  shows "pterm_in_language \<Sigma> \<Gamma> (sterm_translation W A) \<tau>"
proof -
  have typed: "has_stype logical_type \<Gamma> A \<tau>"
    using language unfolding sterm_in_language_def by (rule conjunct1)
  have names: "sterm_in_signature \<Sigma> A"
    using language unfolding sterm_in_language_def by (rule conjunct2)
  have translated_type: "has_ptype \<Gamma> (sterm_translation W A) \<tau>"
    by (rule sterm_translation_type[OF typed wrapper_types])
  have translated_names: "pterm_in_signature \<Sigma> (sterm_translation W A)"
    using names by (simp only: sterm_translation_signature_iff[OF wrapper_names])
  show ?thesis unfolding pterm_in_language_def
    by (rule conjI[OF translated_type translated_names])
qed

end
