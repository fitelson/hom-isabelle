theory Bacon_Book_Conjunction_Binding_Transport
  imports Bacon_Book_Primitive_Conjunction_Decoding Bacon_Book_Printed_Free_For
begin

section \<open>Binding is unchanged by the conjunction-tag translation\<close>

text \<open>
  Encoding and decoding preserve variables, application, and binders.
  Consequently they commute with literal A[B/x] and preserve the
  printed free-for predicate in BOTH directions. The λ binder clause
  uses the already proved equality of free-variable sets.
  Source role: the primitive-symbol distinction of §5.2, p.104, with
  Definition 3.7's substitution proviso, p.70.

  These are raw syntax equations. They do not imply that decoding an
  incorrectly typed distinguished constant preserves its type; the
  separate target-signature guard remains necessary for that claim.
\<close>

lemma book_conj_encode_subst:
  "book_conj_encode (named_subst x B A) =
    named_subst x (book_conj_encode B) (book_conj_encode A)"
  by (induction A) (auto split: if_splits book_conj_logical.splits)

lemma book_conj_decode_subst:
  "book_conj_decode (named_subst x B A) =
    named_subst x (book_conj_decode B) (book_conj_decode A)"
  by (induction A) (auto split: if_splits sum.splits)

lemma book_conj_encode_printed_free_for:
  "book_printed_free_for (book_conj_encode B) x (book_conj_encode A) \<longleftrightarrow>
    book_printed_free_for B x A"
  by (induction A) (simp_all add: book_conj_encode_fv split: book_conj_logical.splits)

lemma book_conj_decode_printed_free_for:
  "book_printed_free_for (book_conj_decode B) x (book_conj_decode A) \<longleftrightarrow>
    book_printed_free_for B x A"
  by (induction A) (simp_all add: book_conj_decode_fv split: sum.splits)

lemma book_conj_decode_vars:
  "named_vars (book_conj_decode A) = named_vars A"
  by (induction A) (simp_all split: sum.splits)

end
