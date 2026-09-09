theory Bacon_Book_Conjunction_Proof_Correspondence
  imports Bacon_Book_Conjunction_Proof_Encoding Bacon_Book_Conjunction_Proof_Decoding
    Bacon_Book_Conjunction_Background_Decoding Bacon_Book_Printed_Completeness
begin

section \<open>The fixed-background encoding preserves and reflects proofs\<close>

text \<open>
  S⊢∧A iff enc(S)∪Π∧⊢minimal enc(A). Every target proof is
  reflected, including auxiliary formulas not originally displayed as
  enc(A); its typed premise callback is discharged by native assumptions
  or the native conjunction schemas. Source role: a faithful encoding of
  the primitive conjunction extension in Bacon §5.2, p.104.

  The proof correspondence needs neither richness nor a global typing
  premise on S: individual uses of assumptions retain their formula guard.
  Model existence below the encoding still requires the usual well-formed
  premise set and rich variable stock. No model, consistency, or theoremhood
  of Π∧ is assumed to prove this correspondence.
\<close>

theorem book_conj_theory_decode:
  assumes derivation: "book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G
    (book_conj_encoded_premises \<Sigma> G S) A"
  shows "book_conj_theory_derivable \<Sigma> G S (book_conj_decode A)"
  by (rule book_conj_decode_printed_proof[OF derivation];
      rule book_conj_decode_background_premise; assumption)

theorem book_conj_theory_encoding_iff:
  "book_conj_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G
      (book_conj_encoded_premises \<Sigma> G S) (book_conj_encode A)"
proof
  assume derivation: "book_conj_theory_derivable \<Sigma> G S A"
  show "book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G
      (book_conj_encoded_premises \<Sigma> G S) (book_conj_encode A)"
    by (rule book_conj_theory_encode[OF derivation])
next
  assume derivation: "book_printed_theory_derivable (book_conj_target_signature \<Sigma>) G
    (book_conj_encoded_premises \<Sigma> G S) (book_conj_encode A)"
  have decoded: "book_conj_theory_derivable \<Sigma> G S (book_conj_decode (book_conj_encode A))"
    by (rule book_conj_theory_decode[OF derivation])
  show "book_conj_theory_derivable \<Sigma> G S A" using decoded by (simp only: book_conj_decode_encode)
qed

section \<open>Consistency is transported before invoking model existence\<close>

definition book_conj_theory_consistent ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_conj_term set \<Rightarrow> bool" where
  "book_conj_theory_consistent \<Sigma> G S \<longleftrightarrow>
    \<not> book_conj_theory_derivable \<Sigma> G S (book_conj_bottom G)"

theorem book_conj_consistency_iff_printed_background:
  "book_conj_theory_consistent \<Sigma> G S \<longleftrightarrow>
    book_printed_theory_consistent (book_conj_target_signature \<Sigma>) G (book_conj_encoded_premises \<Sigma> G S)"
  by (simp only: book_conj_theory_consistent_def book_printed_theory_consistent_def
      book_conj_theory_encoding_iff book_conj_encode_bottom)

corollary book_conj_consistency_iff_background:
  assumes rich: "sg_rich G"
  shows "book_conj_theory_consistent \<Sigma> G S \<longleftrightarrow>
    book_theory_consistent (book_conj_target_signature \<Sigma>) G (book_conj_encoded_premises \<Sigma> G S)"
  by (simp only: book_conj_consistency_iff_printed_background book_consistency_iff_printed[OF rich])

end
