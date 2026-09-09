theory Bacon_Book_Conjunction_Theory_Soundness
  imports Bacon_Book_Conjunction_Decoded_Background_Truth Bacon_Book_Conjunction_Proof_Encoding
    Bacon_Book_Printed_Completeness
begin

section \<open>Encoded formulas retain their original all-assignment truth\<close>

lemma book_conj_decoded_encode_valid_iff:
  "book_formula_valid D G (book_conj_decoded_denote J) V (book_conj_encode A) \<longleftrightarrow>
    book_formula_valid D G J V A"
  by (simp only: book_formula_valid_def book_conj_decoded_denote_def book_conj_decode_encode)

section \<open>Soundness of the twelve-rule primitive-conjunction calculus\<close>

text \<open>
  If every premise in S is globally true in a native conjunction model,
  then every native derivable A is globally true. Interpret the minimal
  target by decoding, encode the proof over enc(S)∪Π∧, and apply the
  printed minimal calculus's soundness theorem. Encoded original premises
  retain their truth; Π∧ is true by the independently verified three
  primitive truth calculations.

  Source: the Chapter 5 rules and §5.2 conjunction schemas, pp.97–98
  and 104, with the model clauses of Definition 15.1, p.314.
  The semantic carrier is arbitrary. S and A may be open, and no
  global language guard on unused premises is imposed beyond the
  native derivation's own guards. This theorem assumes the displayed
  native model; it does not assume a minimal or richer model-existence
  theorem, a definition of ∧ by λ, or theoremhood of Π∧.
\<close>

context book_conjunction_model
begin

theorem book_conj_theory_soundness:
  assumes rich: "sg_rich stock"
    and derivation: "book_conj_theory_derivable signature stock S A"
    and premise_truth: "\<And>B. B \<in> S \<Longrightarrow> book_formula_valid domain stock denote V B"
  shows "book_formula_valid domain stock denote V A"
proof -
  interpret Target: book_full_minimal_model domain app "book_conj_target_signature signature" stock
    "book_conj_decoded_denote denote" V "\<lambda>l. \<kappa> (BCMinimal l)"
    by (rule book_conj_decoded_minimal_model[OF rich book_conjunction_model_axioms])
  have encoded: "book_printed_theory_derivable (book_conj_target_signature signature) stock
    (book_conj_encoded_premises signature stock S) (book_conj_encode A)"
    by (rule book_conj_theory_encode[OF derivation])
  have encoded_premise_truth: "book_formula_valid domain stock (book_conj_decoded_denote denote) V B"
    if member: "B \<in> book_conj_encoded_premises signature stock S" for B
  proof (cases "B \<in> image book_conj_encode S")
    case True
    obtain C where original: "C \<in> S" and shape: "B = book_conj_encode C"
      using True by blast
    have source_truth: "book_formula_valid domain stock denote V C"
      by (rule premise_truth[OF original])
    show ?thesis by (simp only: shape book_conj_decoded_encode_valid_iff; rule source_truth)
  next
    case False
    have background_member: "B \<in> book_conj_axioms signature stock"
      using member False unfolding book_conj_encoded_premises_def by blast
    show ?thesis by (rule book_conj_decoded_axiom_valid[OF background_member])
  qed
  have target_truth: "book_formula_valid domain stock (book_conj_decoded_denote denote) V (book_conj_encode A)"
    by (rule Target.book_printed_theory_soundness[OF rich encoded encoded_premise_truth])
  show ?thesis by (rule iffD1[OF book_conj_decoded_encode_valid_iff target_truth])
qed

end

end
