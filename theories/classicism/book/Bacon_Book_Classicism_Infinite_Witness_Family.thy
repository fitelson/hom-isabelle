theory Bacon_Book_Classicism_Infinite_Witness_Family
  imports Bacon_Book_Classicism_Finite_Witness_Family
    Bacon_Book_Environment_Development.Bacon_Book_Finite_Image_Cover
begin

lemma book_C_consistent_subset:
  assumes consistent: "book_C_theory_consistent \<Sigma> G S" and subset: "T \<subseteq> S"
  shows "book_C_theory_consistent \<Sigma> G T"
proof (unfold book_C_theory_consistent_def, rule notI)
  assume contradiction: "book_C_theory_derivable \<Sigma> G T (book_bottom G)"
  have lifted: "book_C_theory_derivable \<Sigma> G S (book_bottom G)"
    by (rule book_C_theory_derivable_mono[OF contradiction subset])
  show False using consistent lifted unfolding book_C_theory_consistent_def by contradiction
qed

section \<open>Arbitrary witness families with the full enlarged C retained\<close>

theorem book_C_consistent_witness_family:
  assumes rich: "sg_rich G" and consistent: "book_C_theory_consistent \<Sigma> G S"
    and language: "\<And>A. A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A"
    and predicates: "\<And>i. i \<in> I \<Longrightarrow>
      book_in_language book_minimal_logical_type UNIV \<Sigma> G (F i) (Arr (\<tau> i) Prop)"
    and closed: "\<And>i. i \<in> I \<Longrightarrow> named_fv (F i) = {}"
    and fresh: "\<And>i. i \<in> I \<Longrightarrow> c i \<notin> \<Sigma> (\<tau> i)"
    and injective: "inj_on c I"
  shows "book_C_theory_consistent (book_witness_family_signature \<Sigma> \<tau> c I) G
    (S \<union> book_witness_family_axioms G \<tau> F c I)"
proof (rule iffD2[OF book_C_theory_consistent_finite_character])
  let ?full = "book_witness_family_signature \<Sigma> \<tau> c I"
  let ?W = "\<lambda>i. book_witness_axiom G (\<tau> i) (F i) (c i)"
  show "\<forall>B. finite B \<longrightarrow> B \<subseteq> S \<union> book_witness_family_axioms G \<tau> F c I \<longrightarrow>
    book_C_theory_consistent ?full G B"
  proof (intro allI impI)
    fix B
    assume finite_B: "finite B" and covered: "B \<subseteq> S \<union> book_witness_family_axioms G \<tau> F c I"
    have image_cover: "B \<subseteq> S \<union> ?W ` I" using covered by (simp only: book_witness_family_axioms_def)
    obtain J where finite_J: "finite J" and subset_J: "J \<subseteq> I" and covered_J: "B \<subseteq> S \<union> ?W ` J"
      using book_finite_image_cover[OF finite_B image_cover] by blast
    let ?partial = "book_witness_family_signature \<Sigma> \<tau> c J"
    let ?P = "S \<union> book_witness_family_axioms G \<tau> F c J"
    have predicates_J: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (F j) (Arr (\<tau> j) Prop)"
      if "j \<in> J" for j by (rule predicates[OF subsetD[OF subset_J that]])
    have closed_J: "named_fv (F j) = {}" if "j \<in> J" for j by (rule closed[OF subsetD[OF subset_J that]])
    have fresh_J: "c j \<notin> \<Sigma> (\<tau> j)" if "j \<in> J" for j by (rule fresh[OF subsetD[OF subset_J that]])
    have injective_J: "inj_on c J" by (rule inj_on_subset[OF injective subset_J])
    have partial_consistent: "book_C_theory_consistent ?partial G ?P"
      by (rule book_C_consistent_finite_witness_family[where \<Sigma>=\<Sigma> and G=G and S=S
        and \<tau>=\<tau> and F=F and c=c and I=J,
        OF finite_J rich consistent language predicates_J closed_J fresh_J injective_J])
    have partial_language: "book_theory_formula ?partial G A" if "A \<in> ?P" for A
      by (rule book_witness_family_premises_language[OF rich language predicates_J that])
    have full_consistent: "book_C_theory_consistent ?full G ?P"
      by (rule book_C_theory_consistency_signature_preservation[OF rich partial_consistent partial_language])
    have subset: "B \<subseteq> ?P" using covered_J by (simp only: book_witness_family_axioms_def)
    show "book_C_theory_consistent ?full G B" by (rule book_C_consistent_subset[OF full_consistent subset])
  qed
qed

text \<open>
  The family can have arbitrary cardinality. Finite proof support
  selects finitely many witness axioms. Their finite-family consistency
  is transported to the full signature by the proved C-background
  retraction theorem, before finite character is applied there.
  No common finite support for all C axioms is postulated.

  Every Fᵢ still belongs to the old stage language and is closed.
  The fresh injective name supply is an explicit premise. Neither
  witnesses for formulas containing the new names, nor the fixed
  unused-name reserve, nor modal-model existence follows without the
  subsequent construction and iteration.
\<close>

end
