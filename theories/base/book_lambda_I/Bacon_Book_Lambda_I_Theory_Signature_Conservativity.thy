theory Bacon_Book_Lambda_I_Theory_Signature_Conservativity
  imports Bacon_Book_Lambda_I_Theory_Retraction Bacon_Book_Lambda_I_Theory_Signature_Monotonicity
begin

section \<open>Removing foreign constants used only inside a proof\<close>

text \<open>
  If S ⊢Σ A and the premises and conclusion use only constants in Ω,
  then S ⊢Ω A. Choose typed variables outside the proof's finite
  forbidden-name support and retract foreign constants to those variables.
  Retraction fixes S and A literally. Source role: the proof substitution
  and signature arguments of Bacon, pp.99–103, and the fresh-constant
  reasoning needed by the later Henkin construction.

  Freshness is required only against the proof's finite support, not
  against the names in every member of a possibly infinite S. No model,
  completeness theorem, or arbitrary payload-substitution rule is assumed.
\<close>

theorem book_lambda_I_foreign_constants_eliminate:
  assumes rich: "sg_rich G" and derivation: "book_lambda_I_derivable \<Sigma> G S A"
    and conclusion_names: "named_in_signature \<Omega> A"
    and premise_names: "\<And>B. B \<in> S \<Longrightarrow> named_in_signature \<Omega> B"
  shows "book_lambda_I_derivable \<Omega> G S A"
proof -
  obtain N where support: "book_lambda_I_retraction_support \<Omega> G S A N"
    using book_lambda_I_derivable_retraction_support[where \<Omega>=\<Omega>, OF derivation] by (elim exE)
  have finite: "finite N" by (rule book_lambda_I_retraction_support_finite[OF support])
  let ?v = "\<lambda>\<tau>. SOME n. G n = \<tau> \<and> n \<notin> N"
  have chosen: "G (?v \<tau>) = \<tau> \<and> ?v \<tau> \<notin> N" for \<tau>
    by (rule someI_ex, rule sg_rich_fresh[OF rich finite])
  have stock: "\<And>\<tau>. G (?v \<tau>) = \<tau>" by (rule conjunct1[OF chosen])
  have avoids: "\<And>\<tau>. ?v \<tau> \<notin> N" by (rule conjunct2[OF chosen])
  have retracted: "book_lambda_I_derivable \<Omega> G (image (named_retract \<Omega> ?v) S) (named_retract \<Omega> ?v A)"
    by (rule book_lambda_I_retraction_support_apply[OF support stock avoids])
  have fixed_conclusion: "named_retract \<Omega> ?v A = A" by (rule named_retract_fixed[OF conclusion_names])
  have fixed_premise: "named_retract \<Omega> ?v B = B" if "B \<in> S" for B
    by (rule named_retract_fixed[OF premise_names[OF that]])
  have fixed_set: "image (named_retract \<Omega> ?v) S = S" using fixed_premise by auto
  show ?thesis using retracted by (simp only: fixed_conclusion fixed_set)
qed

theorem book_lambda_I_signature_conservativity:
  assumes rich: "sg_rich G" and inclusion: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> \<Omega> \<tau>"
    and conclusion_names: "named_in_signature \<Sigma> A"
    and premise_names: "\<And>B. B \<in> S \<Longrightarrow> named_in_signature \<Sigma> B"
  shows "book_lambda_I_derivable \<Omega> G S A \<longleftrightarrow> book_lambda_I_derivable \<Sigma> G S A"
proof
  assume derivation: "book_lambda_I_derivable \<Omega> G S A"
  show "book_lambda_I_derivable \<Sigma> G S A"
    by (rule book_lambda_I_foreign_constants_eliminate[OF rich derivation conclusion_names premise_names])
next
  assume derivation: "book_lambda_I_derivable \<Sigma> G S A"
  show "book_lambda_I_derivable \<Omega> G S A" by (rule book_lambda_I_signature_mono[OF derivation inclusion])
qed

end
