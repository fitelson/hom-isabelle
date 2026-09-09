theory Bacon_Book_Disjunction_Binding_Transport
  imports Bacon_Book_Disjunction_Formula_Transport Bacon_Book_Printed_Free_For
begin

section \<open>Variable substitution and both capture tests are preserved\<close>

text \<open>
  Encoding and decoding commute with literal A[B/x], since variable
  names, application and binders are unchanged. Every logical symbol or
  tagged constant remains an atomic term with no free variables. Thus
  both the printed free-for predicate (Definition 3.7, p.70) and the
  exact-capture predicate are preserved in each direction.

  The two capture predicates are not identified with one another: their
  distinct vacuous and shadowed-binder cases remain distinct. These are
  raw syntax facts supporting the primitive extension of §5.2, p.104.
  No typing of an incorrectly typed tag, proof correspondence, model,
  or substitution rule for primitive logical symbols is asserted.
\<close>

lemma book_disj_encode_subst:
  "book_disj_encode (named_subst x B A) =
    named_subst x (book_disj_encode B) (book_disj_encode A)"
  by (induction A) (auto split: if_splits book_disj_logical.splits)

lemma book_disj_decode_subst:
  "book_disj_decode (named_subst x B A) =
    named_subst x (book_disj_decode B) (book_disj_decode A)"
  by (induction A) (auto split: if_splits sum.splits)

lemma book_disj_encode_printed_free_for:
  "book_printed_free_for (book_disj_encode B) x (book_disj_encode A) \<longleftrightarrow>
    book_printed_free_for B x A"
  by (induction A) (simp_all add: book_disj_encode_fv split: book_disj_logical.splits)

lemma book_disj_decode_printed_free_for:
  "book_printed_free_for (book_disj_decode B) x (book_disj_decode A) \<longleftrightarrow>
    book_printed_free_for B x A"
  by (induction A) (simp_all add: book_disj_decode_fv split: sum.splits)

lemma book_disj_encode_named_free_for:
  "named_free_for (book_disj_encode B) x (book_disj_encode A) \<longleftrightarrow> named_free_for B x A"
  by (induction A) (simp_all add: book_disj_encode_fv split: book_disj_logical.splits)

lemma book_disj_decode_named_free_for:
  "named_free_for (book_disj_decode B) x (book_disj_decode A) \<longleftrightarrow> named_free_for B x A"
  by (induction A) (simp_all add: book_disj_decode_fv split: sum.splits)

end
