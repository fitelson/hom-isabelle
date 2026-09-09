theory Bacon_Book_Primitive_Disjunction_Syntax
  imports Bacon_Book_Primitive_Conjunction_Syntax
begin

section \<open>Adding independent disjunction to the conjunction vocabulary\<close>

text \<open>
  Add ∨:t→t→t to the already represented →, ∀σ and primitive ∧.
  Source: Bacon §5.2, p.104, and the corresponding disjunction truth
  clause of Definition 15.1, p.314. This leaf declares syntax only;
  neither the three disjunction schemas nor their semantic clause is
  imposed here.

  BDConjunction injects EVERY existing conjunction-language logical
  symbol. BDOr is a separate primitive, and A∨B is its actual saturated
  application. No λ-definition replaces it or the existing ∧.
\<close>

datatype book_disj_logical = BDConjunction book_conj_logical | BDOr

abbreviation book_disj_type :: otype where
  "book_disj_type \<equiv> Arr Prop (Arr Prop Prop)"

fun book_disj_logical_type :: "book_disj_logical \<Rightarrow> otype" where
  "book_disj_logical_type (BDConjunction l) = book_conj_logical_type l"
| "book_disj_logical_type BDOr = book_disj_type"

type_synonym 'c book_disj_term = "('c,book_disj_logical) named_term"

abbreviation book_disj_formula :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_disj_term \<Rightarrow> bool" where
  "book_disj_formula \<Sigma> G A \<equiv> book_in_language book_disj_logical_type UNIV \<Sigma> G A Prop"

definition book_disj_apply :: "'c book_disj_term \<Rightarrow> 'c book_disj_term \<Rightarrow> 'c book_disj_term" where
  "book_disj_apply A B = NApp (NApp (NLogical BDOr) A) B"

lemma book_disj_symbol_language:
  "book_in_language book_disj_logical_type UNIV \<Sigma> G (NLogical BDOr) book_disj_type"
  by (simp only: book_language_logical_iff book_disj_logical_type.simps; simp)

lemma book_disj_conjunction_symbol_language:
  "book_in_language book_disj_logical_type UNIV \<Sigma> G
    (NLogical (BDConjunction l)) (book_conj_logical_type l)"
  by (simp only: book_language_logical_iff book_disj_logical_type.simps; simp)

lemma book_disj_apply_language:
  assumes first: "book_disj_formula \<Sigma> G A" and second: "book_disj_formula \<Sigma> G B"
  shows "book_disj_formula \<Sigma> G (book_disj_apply A B)"
  unfolding book_disj_apply_def
  by (rule book_language_App[OF book_language_App[OF book_disj_symbol_language first] second])

lemma book_disj_apply_fv:
  "named_fv (book_disj_apply A B) = named_fv A \<union> named_fv B"
  by (simp add: book_disj_apply_def)

end
