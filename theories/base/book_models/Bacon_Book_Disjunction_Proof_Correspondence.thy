theory Bacon_Book_Disjunction_Proof_Correspondence
  imports Bacon_Book_Disjunction_Proof_Encoding Bacon_Book_Disjunction_Proof_Decoding
    Bacon_Book_Disjunction_Background_Decoding Bacon_Book_Conjunction_Proof_Correspondence
begin

section \<open>Exact fixed-background proof and consistency correspondence\<close>

text \<open>
  S⊢∧∨A iff enc(S)∪Π∨⊢∧enc(A). The target is the already
  verified conjunction calculus; its conjunction symbol remains logical.
  Only new primitive ∨ is encoded by a fixed atomic tag.
  Source role: Bacon's cumulative primitive extension, §5.2, p.104.

  The two independent proof inductions establish this correspondence
  before any richer-model construction. The reverse premise obligation
  is discharged by native assumptions or disjunction axiom instances.
  No model, richness, global typing of unused premises, or theoremhood
  of the fixed background is assumed. Consistency is separately defined
  by nonderivability of the literal inherited bottom, then transported.
\<close>

theorem book_disj_theory_decode:
  assumes derivation: "book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G
    (book_disj_encoded_premises \<Sigma> G S) A"
  shows "book_disj_theory_derivable \<Sigma> G S (book_disj_decode A)"
  by (rule book_disj_decode_conjunction_proof[OF derivation];
    rule book_disj_decode_background_premise; assumption)

theorem book_disj_theory_encoding_iff:
  "book_disj_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G
      (book_disj_encoded_premises \<Sigma> G S) (book_disj_encode A)"
proof
  assume derivation: "book_disj_theory_derivable \<Sigma> G S A"
  show "book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G
    (book_disj_encoded_premises \<Sigma> G S) (book_disj_encode A)"
    by (rule book_disj_theory_encode[OF derivation])
next
  assume derivation: "book_conj_theory_derivable (book_disj_target_signature \<Sigma>) G
    (book_disj_encoded_premises \<Sigma> G S) (book_disj_encode A)"
  have decoded: "book_disj_theory_derivable \<Sigma> G S (book_disj_decode (book_disj_encode A))"
    by (rule book_disj_theory_decode[OF derivation])
  show "book_disj_theory_derivable \<Sigma> G S A" using decoded by (simp only: book_disj_decode_encode)
qed

definition book_disj_theory_consistent ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_disj_term set \<Rightarrow> bool" where
  "book_disj_theory_consistent \<Sigma> G S \<longleftrightarrow>
    \<not> book_disj_theory_derivable \<Sigma> G S (book_disj_bottom G)"

theorem book_disj_consistency_iff_background:
  "book_disj_theory_consistent \<Sigma> G S \<longleftrightarrow>
    book_conj_theory_consistent (book_disj_target_signature \<Sigma>) G (book_disj_encoded_premises \<Sigma> G S)"
  by (simp only: book_disj_theory_consistent_def book_conj_theory_consistent_def
    book_disj_theory_encoding_iff book_disj_encode_bottom)

end
