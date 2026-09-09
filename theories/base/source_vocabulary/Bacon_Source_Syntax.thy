theory Bacon_Source_Syntax
  imports Bacon_Base.Bacon_Typing
begin

section \<open>First-class source vocabularies\<close>

text \<open>
  A:σ, AB:τ, and λx:σ.A are source terms; a logical constant is a term
  before it is applied.  Bacon–Dorr §1.1, pp. 5–6, specifies this grammar.
  Types are e, t, and unrestricted σ → τ (F); the paper's default R is
  a separate restriction.

  Isabelle representation: ('c,'l) sterm has variables, nonlogical constants,
  logical constants, application, and abstraction.  The logical-symbol
  carrier 'l selects a basis.  The arbitrary carrier 'c has no countability
  constraint; a nonlogical constant is the pair (c,σ).

  Status: raw de Bruijn syntax with a separate typing judgment, not an
  intrinsically typed datatype.  Translation, named-variable correspondence,
  conversion, proof theory, and semantics remain separate obligations.
\<close>

datatype ('c, 'l) sterm =
    SVar nat
  | SConst 'c otype
  | SLogical 'l
  | SApp "('c, 'l) sterm" "('c, 'l) sterm"
  | SLam otype "('c, 'l) sterm"

subsection \<open>The paper's primitive logical constants\<close>

text \<open>
  ¬:t → t; ∧,∨:t → t → t; ∀σ,∃σ:(σ → t) → t; =σ:σ → σ → t.
  These are precisely the primitive families in Bacon–Dorr pp. 5–6.
  Figure 1, p. 6, defines →, ↔, ⊤, ⊥, □, and the lifted operations.

  Isabelle representation: paper_logical has exactly the six primitive
  families.  Quantifier and identity indices range over all F types.

  Status: the primitive symbol stock and its fixed types only.  Figure 1
  abbreviations are not new constructors and are not expanded in this file.
\<close>

datatype paper_logical =
    SNot | SAnd | SOr
  | SAll otype | SEx otype | SEq otype

fun paper_logical_type :: "paper_logical \<Rightarrow> otype" where
  "paper_logical_type SNot = Arr Prop Prop"
| "paper_logical_type SAnd = Arr Prop (Arr Prop Prop)"
| "paper_logical_type SOr = Arr Prop (Arr Prop Prop)"
| "paper_logical_type (SAll \<sigma>) = Arr (Arr \<sigma> Prop) Prop"
| "paper_logical_type (SEx \<sigma>) = Arr (Arr \<sigma> Prop) Prop"
| "paper_logical_type (SEq \<sigma>) = Arr \<sigma> (Arr \<sigma> Prop)"

type_synonym 'c paper_term = "('c, paper_logical) sterm"

subsection \<open>The book's minimal basis is distinct\<close>

text \<open>
  Λ⁻ contains →:t → t → t and ∀σ:(σ → t) → t.
  Bacon pp. 92–93, Table 4.1, and Chapter 5 use this minimal basis.
  In particular, =σ is defined there by Leibniz equivalence, not introduced
  as the paper's primitive identity predicate.

  Isabelle representation: book_minimal_logical is a different symbol
  datatype, with its own total type function.  The larger primitive bases
  considered in Bacon §5.2, pp. 104ff., are not silently included.

  Status: syntax only.  This distinction supplies no identification of
  primitive and defined operations and no general-model semantic theorem.
\<close>

datatype book_minimal_logical =
    SImp | SBAll otype

fun book_minimal_logical_type :: "book_minimal_logical \<Rightarrow> otype" where
  "book_minimal_logical_type SImp = Arr Prop (Arr Prop Prop)"
| "book_minimal_logical_type (SBAll \<sigma>) = Arr (Arr \<sigma> Prop) Prop"

type_synonym 'c book_minimal_term = "('c, book_minimal_logical) sterm"

section \<open>Typing and a declared nonlogical signature\<close>

text \<open>
  Γ ⊢ A:τ records variable types; A ∈ ℒ(Σ) additionally requires each
  nonlogical c:σ in A to belong to Σσ.  See Bacon–Dorr §1.1, pp. 5–6,
  and Bacon Chapter 4.

  Isabelle representation: has_stype is parameterized by the fixed type
  function of the selected logical basis.  Γ is a list, not a set of formula
  assumptions.  SVar 0 denotes the nearest binder; SLam σ extends Γ by σ.
  Logical constants belong to the chosen basis independently of Σ.

  Status: syntactic well-formedness only.  No H relation, denotation, or
  substitution operation is defined here.
\<close>

inductive has_stype ::
  "('l \<Rightarrow> otype) \<Rightarrow> ctx \<Rightarrow> ('c, 'l) sterm \<Rightarrow> otype \<Rightarrow> bool"
  for logical_type :: "'l \<Rightarrow> otype" where
  Var: "lookup \<Gamma> n = Some \<tau> \<Longrightarrow> has_stype logical_type \<Gamma> (SVar n) \<tau>"
| Const: "has_stype logical_type \<Gamma> (SConst c \<tau>) \<tau>"
| Logical: "has_stype logical_type \<Gamma> (SLogical l) (logical_type l)"
| App: "has_stype logical_type \<Gamma> M (Arr \<sigma> \<tau>) \<Longrightarrow>
    has_stype logical_type \<Gamma> N \<sigma> \<Longrightarrow>
    has_stype logical_type \<Gamma> (SApp M N) \<tau>"
| Lam: "has_stype logical_type (\<sigma> # \<Gamma>) M \<tau> \<Longrightarrow>
    has_stype logical_type \<Gamma> (SLam \<sigma> M) (Arr \<sigma> \<tau>)"

type_synonym 'c ssignature = "otype \<Rightarrow> 'c set"

fun sterm_in_signature ::
  "'c ssignature \<Rightarrow> ('c, 'l) sterm \<Rightarrow> bool" where
  "sterm_in_signature \<Sigma> (SVar n) = True"
| "sterm_in_signature \<Sigma> (SConst c \<sigma>) = (c \<in> \<Sigma> \<sigma>)"
| "sterm_in_signature \<Sigma> (SLogical l) = True"
| "sterm_in_signature \<Sigma> (SApp M N) =
    (sterm_in_signature \<Sigma> M \<and> sterm_in_signature \<Sigma> N)"
| "sterm_in_signature \<Sigma> (SLam \<sigma> M) = sterm_in_signature \<Sigma> M"

definition sterm_in_language ::
  "('l \<Rightarrow> otype) \<Rightarrow> 'c ssignature \<Rightarrow> ctx \<Rightarrow>
    ('c, 'l) sterm \<Rightarrow> otype \<Rightarrow> bool" where
  "sterm_in_language logical_type \<Sigma> \<Gamma> A \<tau> \<longleftrightarrow>
    has_stype logical_type \<Gamma> A \<tau> \<and> sterm_in_signature \<Sigma> A"

text \<open>
  =σ A:σ → t is a partially applied identity predicate, and ∀σ is itself
  a term of type (σ → t) → t.  These examples exhibit the first-class
  treatment in Bacon–Dorr pp. 5–6, unlike a binder-only quantifier grammar.

  Isabelle representation: SApp applies an ordinary SLogical term.

  Status: elementary typing examples, not logical axioms or truth claims.
\<close>

lemma paper_identity_partial_type:
  assumes A_type: "has_stype paper_logical_type \<Gamma> A \<sigma>"
  shows "has_stype paper_logical_type \<Gamma> (SApp (SLogical (SEq \<sigma>)) A)
    (Arr \<sigma> Prop)"
proof (rule has_stype.App)
  show "has_stype paper_logical_type \<Gamma> (SLogical (SEq \<sigma>))
    (Arr \<sigma> (Arr \<sigma> Prop))"
    using has_stype.Logical[where logical_type=paper_logical_type and
      \<Gamma>=\<Gamma> and l="SEq \<sigma>"] by (simp only: paper_logical_type.simps)
  show "has_stype paper_logical_type \<Gamma> A \<sigma>" by (rule A_type)
qed

lemma paper_quantifier_type:
  "has_stype paper_logical_type \<Gamma> (SLogical (SAll \<sigma>))
    (Arr (Arr \<sigma> Prop) Prop)"
  using has_stype.Logical[where logical_type=paper_logical_type and
    \<Gamma>=\<Gamma> and l="SAll \<sigma>"] by (simp only: paper_logical_type.simps)

lemma book_implication_type:
  "has_stype book_minimal_logical_type \<Gamma> (SLogical SImp)
    (Arr Prop (Arr Prop Prop))"
  using has_stype.Logical[where logical_type=book_minimal_logical_type and
    \<Gamma>=\<Gamma> and l=SImp] by (simp only: book_minimal_logical_type.simps)

end
