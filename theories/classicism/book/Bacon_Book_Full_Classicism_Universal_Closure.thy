theory Bacon_Book_Full_Classicism_Universal_Closure
  imports Bacon_Book_Full_Classicism_Theory_Rules
begin

lemma book_full_C_theory_cut:
  assumes rich: "sg_rich G" and derivation: "book_full_C_theory_derivable \<Sigma> G T A"
    and replacements: "\<And>B. B \<in> T \<Longrightarrow> book_full_C_theory_derivable \<Sigma> G S B"
  shows "book_full_C_theory_derivable \<Sigma> G S A"
proof -
  let ?C = "{B. book_full_C_proves \<Sigma> G B}"
  have original: "book_theory_derivable \<Sigma> G (?C \<union> T) A" using derivation unfolding book_full_C_theory_derivable_def .
  show ?thesis unfolding book_full_C_theory_derivable_def
  proof (rule book_theory_derivable_cut[OF original])
    fix B
    assume member: "B \<in> ?C \<union> T"
    have result: "book_full_C_theory_derivable \<Sigma> G S B"
    proof (cases "B \<in> T")
      case True
      show ?thesis by (rule replacements[OF True])
    next
      case False
      have theorem_C: "book_full_C_proves \<Sigma> G B" using member False by simp
      show ?thesis by (rule book_full_C_theory_from_C[OF rich theorem_C])
    qed
    show "book_theory_derivable \<Sigma> G (?C \<union> S) B" using result unfolding book_full_C_theory_derivable_def .
  qed
qed

lemma book_full_C_theory_universal_closure_iff:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A"
  shows "book_full_C_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_full_C_theory_derivable \<Sigma> G S (book_universal_closure G A)"
  unfolding book_full_C_theory_derivable_def by (rule book_theory_universal_closure_iff[OF rich al])

theorem book_full_C_theory_universal_closures_equivalent:
  assumes rich: "sg_rich G" and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_full_C_theory_derivable \<Sigma> G (book_universal_closure G ` S) A \<longleftrightarrow>
    book_full_C_theory_derivable \<Sigma> G S A"
proof
  assume derivation: "book_full_C_theory_derivable \<Sigma> G (book_universal_closure G ` S) A"
  show "book_full_C_theory_derivable \<Sigma> G S A"
  proof (rule book_full_C_theory_cut[OF rich derivation])
    fix B
    assume member: "B \<in> book_universal_closure G ` S"
    obtain P where pm: "P \<in> S" and shape: "B = book_universal_closure G P" using member by blast
    have premise: "book_full_C_theory_derivable \<Sigma> G S P" by (rule book_full_C_theory_assume[OF pm language[OF pm]])
    show "book_full_C_theory_derivable \<Sigma> G S B"
      using premise by (simp only: shape book_full_C_theory_universal_closure_iff[OF rich language[OF pm]])
  qed
next
  assume derivation: "book_full_C_theory_derivable \<Sigma> G S A"
  show "book_full_C_theory_derivable \<Sigma> G (book_universal_closure G ` S) A"
  proof (rule book_full_C_theory_cut[OF rich derivation])
    fix B
    assume member: "B \<in> S"
    have image_member: "book_universal_closure G B \<in> book_universal_closure G ` S" by (rule imageI[OF member])
    have premise: "book_full_C_theory_derivable \<Sigma> G (book_universal_closure G ` S) (book_universal_closure G B)"
      by (rule book_full_C_theory_assume[OF image_member book_universal_closure_language[OF language[OF member]]])
    show "book_full_C_theory_derivable \<Sigma> G (book_universal_closure G ` S) B"
      using premise by (simp only: book_full_C_theory_universal_closure_iff[OF rich language[OF member]])
  qed
qed

corollary book_full_C_consistent_universal_closures:
  assumes rich: "sg_rich G" and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_full_C_theory_consistent \<Sigma> G (book_universal_closure G ` S) \<longleftrightarrow> book_full_C_theory_consistent \<Sigma> G S"
  by (simp only: book_full_C_theory_consistent_def book_full_C_theory_universal_closures_equivalent[OF rich language])

end
