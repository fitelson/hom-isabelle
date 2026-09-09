theory Bacon_Book_Primitive_Conjunction_Syntax
  imports Bacon_Book_Minimal_Formula_Syntax
begin

section \<open>The minimal basis with an independent conjunction symbol\<close>

text \<open>
  Add ∧:t→t→t to the minimal symbols → and ∀σ.
  Source: Bacon, §5.2, p.104. The new ∧ is a primitive symbol;
  its later axioms govern material truth without identifying it with
  a λ-defined operator. Definition 15.1, p.314, gives the corresponding
  semantic clause, which is not assumed or proved in this syntax leaf.

  Representation. BCMinimal injects the existing minimal logical datatype,
  while BCAnd is a separate constructor. The generic named-term datatype
  is instantiated with this new logical carrier. Application and binding
  remain explicit. No new proof rule, truth clause or definition of ∧
  by other connectives is introduced.
\<close>

datatype book_conj_logical = BCMinimal book_minimal_logical | BCAnd

abbreviation book_conj_type :: otype where
  "book_conj_type \<equiv> Arr Prop (Arr Prop Prop)"

fun book_conj_logical_type :: "book_conj_logical \<Rightarrow> otype" where
  "book_conj_logical_type (BCMinimal l) = book_minimal_logical_type l"
| "book_conj_logical_type BCAnd = book_conj_type"

type_synonym 'c book_conj_term = "('c,book_conj_logical) named_term"

abbreviation book_conj_formula :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_conj_term \<Rightarrow> bool" where
  "book_conj_formula \<Sigma> G A \<equiv> book_in_language book_conj_logical_type UNIV \<Sigma> G A Prop"

definition book_conj_apply :: "'c book_conj_term \<Rightarrow> 'c book_conj_term \<Rightarrow> 'c book_conj_term" where
  "book_conj_apply A B = NApp (NApp (NLogical BCAnd) A) B"

lemma book_conj_symbol_language:
  "book_in_language book_conj_logical_type UNIV \<Sigma> G (NLogical BCAnd) book_conj_type"
  by (simp only: book_language_logical_iff book_conj_logical_type.simps; simp)

lemma book_conj_minimal_symbol_language:
  "book_in_language book_conj_logical_type UNIV \<Sigma> G
    (NLogical (BCMinimal l)) (book_minimal_logical_type l)"
  by (simp only: book_language_logical_iff book_conj_logical_type.simps; simp)

lemma book_conj_apply_language:
  assumes first: "book_conj_formula \<Sigma> G A" and second: "book_conj_formula \<Sigma> G B"
  shows "book_conj_formula \<Sigma> G (book_conj_apply A B)"
  unfolding book_conj_apply_def
  by (rule book_language_App[OF book_language_App[OF book_conj_symbol_language first] second])

lemma book_conj_apply_fv:
  "named_fv (book_conj_apply A B) = named_fv A \<union> named_fv B"
  by (simp add: book_conj_apply_def)

end
