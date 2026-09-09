theory Bacon_Parametric_Syntax
  imports Bacon_Base.Bacon_Deduction
begin

section \<open>Object languages with unrestricted constant-name carriers\<close>

text \<open>
  Σσ is the stock of constants of type σ; ℒ(Σ) is the resulting language.
  Γ ⊢ A:τ is typing, not ⊢H A.  Types are e, t, and unrestricted σ → τ (F).

  Isabelle representation: 'c pterm uses an arbitrary HOL name carrier; a
  'c psignature selects names at each type.  A constant is the pair (c,σ).
  Names need not be countable.  Choose a carrier containing the given
  signature; no single HOL type is claimed to contain every possible set.

  Status: syntax, typing, and the string comparison only in this file.
  Bacon–Dorr Theorem 3.2 and Bacon’s Chapters 4–5 motivate the signature
  scope; first-class logical-constant translation remains separate.
\<close>

datatype 'c pterm =
    PVar nat
  | PConst 'c otype
  | PApp "'c pterm" "'c pterm"
  | PLam otype "'c pterm"
  | PEq otype "'c pterm" "'c pterm"
  | PNeg "'c pterm"
  | PConj "'c pterm" "'c pterm"
  | PDisj "'c pterm" "'c pterm"
  | PImp "'c pterm" "'c pterm"
  | PForall otype "'c pterm"
  | PExists otype "'c pterm"

type_synonym 'c psignature = "otype \<Rightarrow> 'c set"

fun pterm_in_signature :: "'c psignature \<Rightarrow> 'c pterm \<Rightarrow> bool" where
  "pterm_in_signature \<Sigma> (PVar n) = True"
| "pterm_in_signature \<Sigma> (PConst c \<sigma>) = (c \<in> \<Sigma> \<sigma>)"
| "pterm_in_signature \<Sigma> (PApp M N) =
    (pterm_in_signature \<Sigma> M \<and> pterm_in_signature \<Sigma> N)"
| "pterm_in_signature \<Sigma> (PLam \<sigma> M) = pterm_in_signature \<Sigma> M"
| "pterm_in_signature \<Sigma> (PEq \<sigma> M N) =
    (pterm_in_signature \<Sigma> M \<and> pterm_in_signature \<Sigma> N)"
| "pterm_in_signature \<Sigma> (PNeg A) = pterm_in_signature \<Sigma> A"
| "pterm_in_signature \<Sigma> (PConj A B) =
    (pterm_in_signature \<Sigma> A \<and> pterm_in_signature \<Sigma> B)"
| "pterm_in_signature \<Sigma> (PDisj A B) =
    (pterm_in_signature \<Sigma> A \<and> pterm_in_signature \<Sigma> B)"
| "pterm_in_signature \<Sigma> (PImp A B) =
    (pterm_in_signature \<Sigma> A \<and> pterm_in_signature \<Sigma> B)"
| "pterm_in_signature \<Sigma> (PForall \<sigma> A) = pterm_in_signature \<Sigma> A"
| "pterm_in_signature \<Sigma> (PExists \<sigma> A) = pterm_in_signature \<Sigma> A"

text \<open>
  Γ ⊢ A:σ states that A has type σ in the displayed variable context.
  A ∈ ℒ(Σ) additionally restricts its constants to Σσ.

  Isabelle representation: has_ptype handles types independently of the name
  stock; pterm_in_language combines it with pterm_in_signature.

  Status: typing and language membership, with no theoremhood assertion.
\<close>

inductive has_ptype :: "ctx \<Rightarrow> 'c pterm \<Rightarrow> otype \<Rightarrow> bool" where
  PVar[intro]: "lookup \<Gamma> n = Some \<tau> \<Longrightarrow> has_ptype \<Gamma> (PVar n) \<tau>"
| PConst[intro]: "has_ptype \<Gamma> (PConst c \<tau>) \<tau>"
| PApp[intro]: "has_ptype \<Gamma> M (\<sigma> \<rightarrow>\<^sub>o \<tau>) \<Longrightarrow> has_ptype \<Gamma> N \<sigma> \<Longrightarrow>
    has_ptype \<Gamma> (PApp M N) \<tau>"
| PLam[intro]: "has_ptype (\<sigma> # \<Gamma>) M \<tau> \<Longrightarrow>
    has_ptype \<Gamma> (PLam \<sigma> M) (\<sigma> \<rightarrow>\<^sub>o \<tau>)"
| PEq[intro]: "has_ptype \<Gamma> M \<sigma> \<Longrightarrow> has_ptype \<Gamma> N \<sigma> \<Longrightarrow>
    has_ptype \<Gamma> (PEq \<sigma> M N) Prop"
| PNeg[intro]: "has_ptype \<Gamma> A Prop \<Longrightarrow> has_ptype \<Gamma> (PNeg A) Prop"
| PConj[intro]: "has_ptype \<Gamma> A Prop \<Longrightarrow> has_ptype \<Gamma> B Prop \<Longrightarrow>
    has_ptype \<Gamma> (PConj A B) Prop"
| PDisj[intro]: "has_ptype \<Gamma> A Prop \<Longrightarrow> has_ptype \<Gamma> B Prop \<Longrightarrow>
    has_ptype \<Gamma> (PDisj A B) Prop"
| PImp[intro]: "has_ptype \<Gamma> A Prop \<Longrightarrow> has_ptype \<Gamma> B Prop \<Longrightarrow>
    has_ptype \<Gamma> (PImp A B) Prop"
| PForall[intro]: "has_ptype (\<sigma> # \<Gamma>) A Prop \<Longrightarrow>
    has_ptype \<Gamma> (PForall \<sigma> A) Prop"
| PExists[intro]: "has_ptype (\<sigma> # \<Gamma>) A Prop \<Longrightarrow>
    has_ptype \<Gamma> (PExists \<sigma> A) Prop"

definition pterm_in_language :: "'c psignature \<Rightarrow> ctx \<Rightarrow> 'c pterm \<Rightarrow> otype \<Rightarrow> bool" where
  "pterm_in_language \<Sigma> \<Gamma> M \<tau> \<longleftrightarrow>
    has_ptype \<Gamma> M \<tau> \<and> pterm_in_signature \<Sigma> M"

lemma pterm_signature_mono:
  assumes "pterm_in_signature \<Sigma> M" and "\<And>\<sigma>. \<Sigma> \<sigma> \<subseteq> \<Sigma>' \<sigma>"
  shows "pterm_in_signature \<Sigma>' M"
  using assms by (induction M) auto

lemma pterm_all_names[simp]:
  "pterm_in_signature (\<lambda>_. UNIV) M"
  by (induction M) simp_all

lemma pterm_constant_in_language:
  "pterm_in_language \<Sigma> \<Gamma> (PConst c \<sigma>) \<sigma> \<longleftrightarrow> c \<in> \<Sigma> \<sigma>"
  by (simp add: pterm_in_language_def has_ptype.PConst)

lemma pterm_constant_names_injective:
  "inj (\<lambda>c :: 'c. PConst c \<sigma>)"
proof (rule injI)
  fix c d :: 'c
  assume "PConst c \<sigma> = PConst d \<sigma>"
  then show "c = d" by simp
qed

section \<open>The string instance is exactly the existing syntax\<close>

text \<open>
  For string names, A:σ is preserved and reflected by the translation
  between the two presentations of ℒ(Σ).

  Isabelle representation: pterm_of_oterm and pterm_to_oterm are inverse maps;
  their typing lemmas compare has_ptype with the existing has_type relation.

  Status: syntax and typing isomorphism, not automatic transport of proofs,
  models, or completeness.
\<close>

fun pterm_of_oterm :: "oterm \<Rightarrow> string pterm" where
  "pterm_of_oterm (Var n) = PVar n"
| "pterm_of_oterm (Const c \<sigma>) = PConst c \<sigma>"
| "pterm_of_oterm (App M N) = PApp (pterm_of_oterm M) (pterm_of_oterm N)"
| "pterm_of_oterm (Lam \<sigma> M) = PLam \<sigma> (pterm_of_oterm M)"
| "pterm_of_oterm (Eq \<sigma> M N) = PEq \<sigma> (pterm_of_oterm M) (pterm_of_oterm N)"
| "pterm_of_oterm (Neg A) = PNeg (pterm_of_oterm A)"
| "pterm_of_oterm (Conj A B) = PConj (pterm_of_oterm A) (pterm_of_oterm B)"
| "pterm_of_oterm (Disj A B) = PDisj (pterm_of_oterm A) (pterm_of_oterm B)"
| "pterm_of_oterm (Imp A B) = PImp (pterm_of_oterm A) (pterm_of_oterm B)"
| "pterm_of_oterm (Forall \<sigma> A) = PForall \<sigma> (pterm_of_oterm A)"
| "pterm_of_oterm (Exists \<sigma> A) = PExists \<sigma> (pterm_of_oterm A)"

fun pterm_to_oterm :: "string pterm \<Rightarrow> oterm" where
  "pterm_to_oterm (PVar n) = Var n"
| "pterm_to_oterm (PConst c \<sigma>) = Const c \<sigma>"
| "pterm_to_oterm (PApp M N) = App (pterm_to_oterm M) (pterm_to_oterm N)"
| "pterm_to_oterm (PLam \<sigma> M) = Lam \<sigma> (pterm_to_oterm M)"
| "pterm_to_oterm (PEq \<sigma> M N) = Eq \<sigma> (pterm_to_oterm M) (pterm_to_oterm N)"
| "pterm_to_oterm (PNeg A) = Neg (pterm_to_oterm A)"
| "pterm_to_oterm (PConj A B) = Conj (pterm_to_oterm A) (pterm_to_oterm B)"
| "pterm_to_oterm (PDisj A B) = Disj (pterm_to_oterm A) (pterm_to_oterm B)"
| "pterm_to_oterm (PImp A B) = Imp (pterm_to_oterm A) (pterm_to_oterm B)"
| "pterm_to_oterm (PForall \<sigma> A) = Forall \<sigma> (pterm_to_oterm A)"
| "pterm_to_oterm (PExists \<sigma> A) = Exists \<sigma> (pterm_to_oterm A)"

lemma pterm_to_of[simp]: "pterm_to_oterm (pterm_of_oterm M) = M"
  by (induction M) simp_all

lemma pterm_of_to[simp]: "pterm_of_oterm (pterm_to_oterm M) = M"
  by (induction M) simp_all

lemma pterm_of_preserves_typing:
  assumes "\<Gamma> \<turnstile> M : \<tau>"
  shows "has_ptype \<Gamma> (pterm_of_oterm M) \<tau>"
  using assms by (induction rule: has_type.induct) auto

lemma pterm_to_preserves_typing:
  assumes "has_ptype \<Gamma> M \<tau>"
  shows "\<Gamma> \<turnstile> pterm_to_oterm M : \<tau>"
  using assms by (induction rule: has_ptype.induct) auto

theorem pterm_string_typing_iff:
  "has_ptype \<Gamma> M \<tau> \<longleftrightarrow> \<Gamma> \<turnstile> pterm_to_oterm M : \<tau>"
proof
  assume "has_ptype \<Gamma> M \<tau>"
  then show "\<Gamma> \<turnstile> pterm_to_oterm M : \<tau>" by (rule pterm_to_preserves_typing)
next
  assume "\<Gamma> \<turnstile> pterm_to_oterm M : \<tau>"
  then have "has_ptype \<Gamma> (pterm_of_oterm (pterm_to_oterm M)) \<tau>"
    by (rule pterm_of_preserves_typing)
  then show "has_ptype \<Gamma> M \<tau>" by simp
qed

text \<open>
  A ∈ ℒ(Σ) requires every constant c:σ in A to belong to Σσ.

  Isabelle representation: oterm_in_string_signature is the local guard for
  oterm.  pterm_string_signature_iff compares it with pterm_in_signature.

  Status: syntactic guard correspondence; this group does not identify the
  local predicate with the later BBK session’s bbk_in_signature.
\<close>

fun oterm_in_string_signature :: "(otype \<Rightarrow> string set) \<Rightarrow> oterm \<Rightarrow> bool" where
  "oterm_in_string_signature \<Sigma> (Var n) = True"
| "oterm_in_string_signature \<Sigma> (Const c \<sigma>) = (c \<in> \<Sigma> \<sigma>)"
| "oterm_in_string_signature \<Sigma> (App M N) =
    (oterm_in_string_signature \<Sigma> M \<and> oterm_in_string_signature \<Sigma> N)"
| "oterm_in_string_signature \<Sigma> (Lam \<sigma> M) = oterm_in_string_signature \<Sigma> M"
| "oterm_in_string_signature \<Sigma> (Eq \<sigma> M N) =
    (oterm_in_string_signature \<Sigma> M \<and> oterm_in_string_signature \<Sigma> N)"
| "oterm_in_string_signature \<Sigma> (Neg A) = oterm_in_string_signature \<Sigma> A"
| "oterm_in_string_signature \<Sigma> (Conj A B) =
    (oterm_in_string_signature \<Sigma> A \<and> oterm_in_string_signature \<Sigma> B)"
| "oterm_in_string_signature \<Sigma> (Disj A B) =
    (oterm_in_string_signature \<Sigma> A \<and> oterm_in_string_signature \<Sigma> B)"
| "oterm_in_string_signature \<Sigma> (Imp A B) =
    (oterm_in_string_signature \<Sigma> A \<and> oterm_in_string_signature \<Sigma> B)"
| "oterm_in_string_signature \<Sigma> (Forall \<sigma> A) = oterm_in_string_signature \<Sigma> A"
| "oterm_in_string_signature \<Sigma> (Exists \<sigma> A) = oterm_in_string_signature \<Sigma> A"

lemma pterm_string_signature_iff:
  "pterm_in_signature \<Sigma> M = oterm_in_string_signature \<Sigma> (pterm_to_oterm M)"
  by (induction M) simp_all

lemma pterm_of_signature_iff:
  "pterm_in_signature \<Sigma> (pterm_of_oterm M) = oterm_in_string_signature \<Sigma> M"
  by (induction M) simp_all

section \<open>Migration obligations\<close>

text \<open>
  A[B/v], A ≡βη B, ⊢H A, and M,g ⊨ A belong to different stages:
  substitution, conversion, proof, and semantics.

  Isabelle representation: Bacon_Parametric_Substitution, Beta, Deduction,
  BBK_Semantics, and H_Soundness supply those respective interfaces and
  preservation results.  Henkin_One_Step adds a disjoint witness signature.

  Status: arbitrary-name syntax and soundness do not themselves establish
  arbitrary-signature completeness.  Witness-axiom consistency, iterated
  Henkin closure, and named-variable/first-class-constant translation remain
  separate obligations; no countable enumeration settles them.
\<close>

end
