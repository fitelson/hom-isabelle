theory Bacon_Book_Full_Classicism_Boxed_Consequence
  imports Bacon_Book_Full_Classicism_Boxed_Lists Bacon_Book_Full_Classicism_Closed_Refutation
begin

section \<open>The finite boxed-consequence step for canonical successors\<close>

theorem book_full_C_theory_box_lift:
  assumes rich: "sg_rich G"
    and sentences: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A \<and> named_fv A = {}"
    and derivation: "book_full_C_theory_derivable \<Sigma> G S P"
  shows "book_full_C_theory_derivable \<Sigma> G (book_box G ` S) (book_box G P)"
proof -
  have pl: "book_theory_formula \<Sigma> G P" by (rule book_full_C_theory_language[OF rich derivation])
  obtain U where finite: "finite U" and subset: "U \<subseteq> S"
    and supported: "book_full_C_theory_derivable \<Sigma> G U P"
    by (rule book_full_C_theory_finite_support[OF derivation])
  obtain As where entries: "set As = U" using finite_distinct_list[OF finite] by blast
  have all_sentences: "list_all (\<lambda>A. book_theory_formula \<Sigma> G A \<and> named_fv A = {}) As"
    using sentences subset by (auto simp: list_all_iff entries)
  have all_formulas: "list_all (book_theory_formula \<Sigma> G) As"
    using all_sentences by (auto simp: list_all_iff)
  have list_proof: "book_full_C_theory_derivable \<Sigma> G (set As \<union> {}) P" using supported by (simp only: entries Un_empty_right)
  have discharged: "book_full_C_theory_derivable \<Sigma> G {} (book_C_imp_list As P)"
    by (rule book_full_C_theory_closed_list_deduction[OF rich all_sentences list_proof])
  have original: "book_full_C_proves \<Sigma> G (book_C_imp_list As P)"
    using discharged by (simp only: book_full_C_theory_empty_iff[OF rich])
  have necessary: "book_full_C_proves \<Sigma> G (book_box G (book_C_imp_list As P))"
    by (rule book_full_C_necessitation[OF rich original])
  have implication: "book_full_C_theory_derivable \<Sigma> G (book_box G ` S) (book_box G (book_C_imp_list As P))"
    by (rule book_full_C_theory_from_C[OF rich necessary])
  have each: "book_full_C_theory_derivable \<Sigma> G (book_box G ` S) (book_box G A)"
    if member: "A \<in> set As" for A
  proof -
    have in_S: "A \<in> S" using member subset by (simp only: entries; blast)
    have al: "book_theory_formula \<Sigma> G A" by (rule conjunct1[OF sentences[OF in_S]])
    have box_member: "book_box G A \<in> book_box G ` S" by (rule imageI[OF in_S])
    show ?thesis by (rule book_full_C_theory_assume[OF box_member book_box_language[OF rich al]])
  qed
  show ?thesis by (rule book_full_C_theory_boxed_list_MP[OF rich pl all_formulas implication each])
qed

theorem book_full_C_successor_seed_consistent:
  assumes rich: "sg_rich G"
    and sentences: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A \<and> named_fv A = {}"
    and pl: "book_theory_formula \<Sigma> G P" and closed: "named_fv P = {}"
    and boxes: "book_box G ` S \<subseteq> w"
    and missing: "\<not> book_full_C_theory_derivable \<Sigma> G w (book_box G P)"
  shows "book_full_C_theory_consistent \<Sigma> G (insert (book_not G P) S)"
proof -
  have underivable: "\<not> book_full_C_theory_derivable \<Sigma> G S P"
  proof
    assume proof_P: "book_full_C_theory_derivable \<Sigma> G S P"
    have lifted: "book_full_C_theory_derivable \<Sigma> G (book_box G ` S) (book_box G P)"
      by (rule book_full_C_theory_box_lift[OF rich sentences proof_P])
    have contradiction: "book_full_C_theory_derivable \<Sigma> G w (book_box G P)"
      by (rule book_full_C_theory_derivable_mono[OF lifted boxes])
    show False by (rule notE[OF missing contradiction])
  qed
  show ?thesis by (rule book_full_C_theory_consistent_negative_extension[OF rich pl closed underivable])
qed

text \<open>
  Proposition 18.3, p.399: a finite derivation from the unboxed
  successor premises is discharged first. Necessitation applies to
  the resulting theorem of C, not to any temporary premise. Iterated
  K then reconstructs the boxed conclusion from the boxed premises.
  Closedness is required of those discharged premises; P can be open
  in the lifting theorem, but is closed in the negative-extension result.

  This proves consistency of the successor seed over the full fixed C
  background. It does not yet construct a negation/witness-complete
  successor, preserve C in its expanded signature, or supply the fixed
  reserve of names required in the canonical frame.
\<close>

end
