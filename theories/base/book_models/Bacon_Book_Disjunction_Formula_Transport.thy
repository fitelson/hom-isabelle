theory Bacon_Book_Disjunction_Formula_Transport
  imports Bacon_Book_Primitive_Disjunction_Decoding Bacon_Book_Disjunction_Formula_Syntax
    Bacon_Book_Primitive_Conjunction_Formula_Syntax
begin

section \<open>Formula operations retain their inherited logical symbols\<close>

text \<open>
  Encoding removes only the BDConjunction injection from inherited
  logical symbols. Thus source →, ∀, ⊥ and ¬ become the existing
  conjunction-language operations, with identical binder-name choices.
  Inherited primitive ∧ becomes book_conj_apply, still a logical-symbol
  application. The NEW primitive ∨ instead becomes its atomic right tag.
  Source role: the cumulative primitive extensions of Bacon §5.2, p.104.

  These equations hold on raw syntax. They are not proof rules or
  operator identities equating primitives with λ-definitions. Decoding
  typing and target roundtrips continue to require the separate target
  signature guard, even though these operation equations are unconditional.
\<close>

lemma book_disj_encode_imp:
  "book_disj_encode (book_disj_imp A B) = book_conj_imp (book_disj_encode A) (book_disj_encode B)"
  by (simp add: book_disj_imp_def book_conj_imp_def)

lemma book_disj_encode_all:
  "book_disj_encode (book_disj_all G n A) = book_conj_all G n (book_disj_encode A)"
  by (simp add: book_disj_all_def book_conj_all_def)

lemma book_disj_encode_bottom:
  "book_disj_encode (book_disj_bottom G) = book_conj_bottom G"
  by (simp add: book_disj_bottom_def book_conj_bottom_def)

lemma book_disj_encode_not_const:
  "book_disj_encode (book_disj_not_const G) = book_conj_not_const G"
  by (simp add: book_disj_not_const_def book_conj_not_const_def book_disj_encode_imp book_disj_encode_bottom)

lemma book_disj_encode_not:
  "book_disj_encode (book_disj_not G A) = book_conj_not G (book_disj_encode A)"
  by (simp add: book_disj_not_def book_conj_not_def book_disj_encode_not_const)

lemma book_disj_encode_conj:
  "book_disj_encode (book_disj_conj A B) = book_conj_apply (book_disj_encode A) (book_disj_encode B)"
  by (simp add: book_disj_conj_def book_conj_apply_def)

lemma book_disj_decode_imp:
  "book_disj_decode (book_conj_imp A B) = book_disj_imp (book_disj_decode A) (book_disj_decode B)"
  by (simp add: book_conj_imp_def book_disj_imp_def)

lemma book_disj_decode_all:
  "book_disj_decode (book_conj_all G n A) = book_disj_all G n (book_disj_decode A)"
  by (simp add: book_conj_all_def book_disj_all_def)

lemma book_disj_decode_bottom:
  "book_disj_decode (book_conj_bottom G) = book_disj_bottom G"
  by (simp add: book_conj_bottom_def book_disj_bottom_def)

lemma book_disj_decode_not_const:
  "book_disj_decode (book_conj_not_const G) = book_disj_not_const G"
  by (simp add: book_conj_not_const_def book_disj_not_const_def book_disj_decode_imp book_disj_decode_bottom)

lemma book_disj_decode_not:
  "book_disj_decode (book_conj_not G A) = book_disj_not G (book_disj_decode A)"
  by (simp add: book_conj_not_def book_disj_not_def book_disj_decode_not_const)

lemma book_disj_decode_conj:
  "book_disj_decode (book_conj_apply A B) = book_disj_conj (book_disj_decode A) (book_disj_decode B)"
  by (simp add: book_conj_apply_def book_disj_conj_def)

lemma book_disj_decode_tag_application:
  "book_disj_decode (NApp (NApp (NConst (Inr ()) book_disj_type) A) B) =
    book_disj_apply (book_disj_decode A) (book_disj_decode B)"
  by (simp add: book_disj_apply_def)

end
