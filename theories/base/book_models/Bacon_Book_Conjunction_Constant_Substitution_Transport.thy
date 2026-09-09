theory Bacon_Book_Conjunction_Constant_Substitution_Transport
  imports Bacon_Book_Conjunction_Binding_Transport
begin

section \<open>The exact-capture variable proviso is preserved by encoding\<close>

text \<open>
  N is exact-capture-free for x in A iff enc(N) is exact-capture-free
  for x in enc(A). This concerns named_free_for, including its vacuous
  and shadowed-binder cases, not the stricter printed recursion.
  Free-variable preservation supplies both binder tests.
  Source role: transferring the already derived variable-substitution
  rule while keeping the printed and exact-capture predicates distinct.
\<close>

lemma book_conj_encode_named_free_for:
  "named_free_for (book_conj_encode B) x (book_conj_encode A) \<longleftrightarrow>
    named_free_for B x A"
  by (induction A) (simp_all add: book_conj_encode_fv split: book_conj_logical.splits)

section \<open>Typed nonlogical keys become left-summand keys only\<close>

text \<open>
  The typed key c:σ becomes Inl(c):σ. It occurs in enc(A) exactly
  when c:σ occurs in A, and
  enc(A[B/c:σ])=enc(A)[enc(B)/Inl(c):σ].
  Source: nonlogical-constant substitution in Definition 5.2, p.99,
  and the primitive extension of §5.2, p.104.

  The distinguished Inr(⋆) name is never selected by this replacement.
  The conjunction symbol is NOT replaced by a payload or a λ-definition.
  These are raw syntax equations and exact capture-guard correspondences;
  they assert no proof rule, theoremhood of Π∧, or model fact.
\<close>

lemma book_conj_encode_const_occurs:
  "book_const_occurs (Inl c) \<sigma> (book_conj_encode A) \<longleftrightarrow>
    book_const_occurs c \<sigma> A"
  by (induction A) (simp_all split: book_conj_logical.splits)

lemma book_conj_encode_const_subst:
  "book_conj_encode (book_const_subst c \<sigma> B A) =
    book_const_subst (Inl c) \<sigma> (book_conj_encode B) (book_conj_encode A)"
  by (induction A) (auto split: if_splits book_conj_logical.splits)

lemma book_conj_encode_const_free_for:
  "book_const_free_for (book_conj_encode B) (Inl c) \<sigma> (book_conj_encode A) \<longleftrightarrow>
    book_const_free_for B c \<sigma> A"
  by (induction A)
    (simp_all add: book_conj_encode_const_occurs book_conj_encode_fv split: book_conj_logical.splits)

lemma book_conj_Inl_key_not_tag:
  "\<not> book_const_occurs (Inl c) \<sigma> (NConst (Inr ()) \<rho>)"
  by simp

lemma book_conj_Inl_subst_fixes_tag:
  fixes B :: "('c + unit) book_named_term"
  shows "book_const_subst (Inl c) \<sigma> B (NConst (Inr ()) \<rho>) = NConst (Inr ()) \<rho>"
  by simp

end
