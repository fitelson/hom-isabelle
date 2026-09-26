theory Bacon_Book_Lambda_I_Henkin_Stage_Consistency
  imports Bacon_Book_Lambda_I_Henkin_Stage_Witnesses Bacon_Book_Lambda_I_Infinite_Witness_Family
begin

section \<open>All closed λI-predicate witnesses at one stage preserve λI consistency\<close>

text \<open>
  At stage n, use the ACTUAL family of all closed λI predicates of Σₙ,
  with the constructed names Witness(n,σ,F). The generic arbitrary-family
  consistency theorem applies because these names are injective and fresh
  in Σₙ, and its output signature is exactly Σₙ₊₁.
  Source role: the witness extension of Bacon, Proposition 15.4, p.319,
  in the explicitly closed-predicate formulation.

  This is a consistency theorem for the whole stage, not a finite sample
  or an assumed supply of names. Each stage may have arbitrary cardinality.
  The premises S may be open and infinite, but must belong to Σₙ.
  Iteration through every stage, consistency of its union, and the final
  term-model construction remain separate obligations.
\<close>

theorem book_lambda_I_henkin_stage_consistent:
  assumes rich: "sg_rich G"
    and consistent: "book_lambda_I_consistent (book_lambda_I_henkin_signature \<Sigma> G n) G S"
    and language: "\<And>A. A \<in> S \<Longrightarrow>
      book_lambda_I_formula (book_lambda_I_henkin_signature \<Sigma> G n) G A"
  shows "book_lambda_I_consistent (book_lambda_I_henkin_signature \<Sigma> G (Suc n)) G
    (S \<union> book_lambda_I_henkin_stage_axioms \<Sigma> G n)"
proof -
  let ?I = "book_lambda_I_henkin_stage_indices \<Sigma> G n"
  let ?c = "book_lambda_I_henkin_stage_name n"
  have predicates: "book_in_language book_minimal_logical_type UNIV
      (book_lambda_I_henkin_signature \<Sigma> G n) G (snd i) (Arr (fst i) Prop)"
    if "i \<in> ?I" for i
    by (rule book_lambda_I_henkin_stage_index_language[OF that])
  have closed: "named_fv (snd i) = {}" if "i \<in> ?I" for i
    by (rule book_lambda_I_henkin_stage_index_closed[OF that])
  have lambda_I: "book_lambda_I (snd i)" if "i \<in> ?I" for i
    by (rule book_lambda_I_henkin_stage_index_lambda_I[OF that])
  have fresh: "?c i \<notin> book_lambda_I_henkin_signature \<Sigma> G n (fst i)" if "i \<in> ?I" for i
    by (rule book_lambda_I_henkin_stage_name_fresh)
  have injective: "inj_on ?c ?I" by (rule book_lambda_I_henkin_stage_name_inj_on)
  have family: "book_lambda_I_consistent
      (book_witness_family_signature (book_lambda_I_henkin_signature \<Sigma> G n) fst ?c ?I) G
      (S \<union> book_witness_family_axioms G fst snd ?c ?I)"
    by (rule book_lambda_I_consistent_witness_family[where \<Sigma>="book_lambda_I_henkin_signature \<Sigma> G n"
      and G=G and S=S and \<tau>=fst and F=snd and c="?c" and I="?I",
      OF rich consistent language predicates closed lambda_I fresh injective])
  show ?thesis using family
    by (simp only: book_lambda_I_henkin_signature_family book_lambda_I_henkin_stage_axioms_def)
qed

end
