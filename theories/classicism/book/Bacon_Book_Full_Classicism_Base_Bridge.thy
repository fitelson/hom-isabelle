theory Bacon_Book_Full_Classicism_Base_Bridge
  imports Bacon_Book_Full_Equivalence_Presentation
    Bacon_Book_Full_Classicism_Theory_Consistency Bacon_Book_Classicism_Theory_Consistency
begin

theorem book_C_base_theory_embeds_full:
  assumes rich: "sg_rich G" and derivation: "book_C_theory_derivable \<Sigma> G S A"
  shows "book_full_C_theory_derivable \<Sigma> G S A"
proof -
  have base: "book_theory_derivable \<Sigma> G ({B. book_C_proves \<Sigma> G B} \<union> S) A"
    using derivation unfolding book_C_theory_derivable_def .
  have included: "{B. book_C_proves \<Sigma> G B} \<union> S \<subseteq> {B. book_full_C_proves \<Sigma> G B} \<union> S"
    using book_C_base_embeds_full[OF rich] by blast
  show ?thesis unfolding book_full_C_theory_derivable_def by (rule book_theory_derivable_mono[OF base included])
qed

theorem book_full_C_consistency_implies_base:
  assumes rich: "sg_rich G" and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "book_C_theory_consistent \<Sigma> G S"
proof (unfold book_C_theory_consistent_def, rule notI)
  assume contradiction: "book_C_theory_derivable \<Sigma> G S (book_bottom G)"
  have full: "book_full_C_theory_derivable \<Sigma> G S (book_bottom G)"
    by (rule book_C_base_theory_embeds_full[OF rich contradiction])
  show False using consistent full unfolding book_full_C_theory_consistent_def by contradiction
qed

text \<open>
  Every base consequence survives in full C. Consequently full-C
  consistency implies base consistency. The converse is not claimed:
  a base-consistent theory need not remain consistent after adding MF.
  Full-background witness and canonical-model existence still need
  their own proofs; the old model-existence claims are not promoted.
\<close>

end
