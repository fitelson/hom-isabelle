theory Bacon_Book_Closed_Maximal_Truth
  imports Bacon_Book_Closed_Negation_Complete Bacon_Book_Theory_Conversion
begin

section \<open>Membership facts for the later characteristic valuation\<close>

text \<open>
  On closed formulas, membership in a maximal consistent closed set M
  respects βη conversion, excludes ⊥, and interprets A→B materially.
  Source role: the characteristic-function construction on p.320, with
  the closed-formula qualification explicit.

  These are syntactic membership theorems. No valuation or model is
  assumed or defined here; a separately constructed interpretation must
  still be shown to satisfy every required semantic clause. M is not
  asserted to be a global theory or to decide open formulas.
\<close>

theorem book_closed_maximal_raw_conversion_iff:
  assumes rich: "sg_rich G" and maximal: "book_closed_maximal_extension \<Sigma> G S M"
    and al: "book_theory_formula \<Sigma> G A" and bl: "book_theory_formula \<Sigma> G B"
    and ac: "named_fv A = {}" and bc: "named_fv B = {}"
    and conversion: "named_raw_beta_eta book_minimal_logical_type G Prop A B"
  shows "A \<in> M \<longleftrightarrow> B \<in> M"
proof -
  have equivalent: "book_theory_derivable \<Sigma> G M A \<longleftrightarrow> book_theory_derivable \<Sigma> G M B"
    by (rule book_theory_raw_conversion_iff[OF rich al bl conversion])
  show ?thesis
  proof
    assume member: "A \<in> M"
    have original: "book_theory_derivable \<Sigma> G M A"
      by (rule book_theory_derivable.Assumption[OF member al])
    have converted: "book_theory_derivable \<Sigma> G M B" by (rule iffD1[OF equivalent original])
    show "B \<in> M" by (rule book_closed_maximal_derivable_member[OF maximal bl bc converted])
  next
    assume member: "B \<in> M"
    have original: "book_theory_derivable \<Sigma> G M B"
      by (rule book_theory_derivable.Assumption[OF member bl])
    have converted: "book_theory_derivable \<Sigma> G M A" by (rule iffD2[OF equivalent original])
    show "A \<in> M" by (rule book_closed_maximal_derivable_member[OF maximal al ac converted])
  qed
qed

theorem book_closed_maximal_bottom_absent:
  assumes maximal: "book_closed_maximal_extension \<Sigma> G S M"
  shows "book_bottom G \<notin> M"
proof
  assume member: "book_bottom G \<in> M"
  have closed_M: "book_closed_formula_set \<Sigma> G M"
    and consistent_M: "book_theory_consistent \<Sigma> G M"
    using maximal unfolding book_closed_maximal_extension_def by blast+
  have bottom_language: "book_theory_formula \<Sigma> G (book_bottom G)"
    by (rule conjunct1[OF book_closed_formula_set_member[OF closed_M member]])
  have contradiction: "book_theory_derivable \<Sigma> G M (book_bottom G)"
    by (rule book_theory_derivable.Assumption[OF member bottom_language])
  show False using consistent_M contradiction unfolding book_theory_consistent_def by blast
qed

section \<open>The material implication membership clause\<close>

theorem book_closed_maximal_implication_iff:
  assumes rich: "sg_rich G" and maximal: "book_closed_maximal_extension \<Sigma> G S M"
    and al: "book_theory_formula \<Sigma> G A" and bl: "book_theory_formula \<Sigma> G B"
    and ac: "named_fv A = {}" and bc: "named_fv B = {}"
  shows "book_imp A B \<in> M \<longleftrightarrow> (A \<notin> M \<or> B \<in> M)"
proof -
  have implication_language: "book_theory_formula \<Sigma> G (book_imp A B)"
    by (rule book_imp_language[OF al bl])
  have implication_closed: "named_fv (book_imp A B) = {}"
    by (simp only: book_imp_fv ac bc Un_empty_left)
  show ?thesis
  proof
    assume implication_member: "book_imp A B \<in> M"
    show "A \<notin> M \<or> B \<in> M"
    proof (cases "A \<in> M")
      case True
      have antecedent: "book_theory_derivable \<Sigma> G M A"
        by (rule book_theory_derivable.Assumption[OF True al])
      have conditional: "book_theory_derivable \<Sigma> G M (book_imp A B)"
        by (rule book_theory_derivable.Assumption[OF implication_member implication_language])
      have consequent: "book_theory_derivable \<Sigma> G M B"
        by (rule book_theory_derivable.MP[OF antecedent conditional bl])
      have member: "B \<in> M" by (rule book_closed_maximal_derivable_member[OF maximal bl bc consequent])
      show ?thesis by (rule disjI2[OF member])
    next
      case False
      show ?thesis by (rule disjI1[OF False])
    qed
  next
    assume alternative: "A \<notin> M \<or> B \<in> M"
    have derivation: "book_theory_derivable \<Sigma> G M (book_imp A B)"
    proof (rule disjE[OF alternative])
      assume absent: "A \<notin> M"
      have negative_member: "book_not G A \<in> M"
        by (rule iffD2[OF book_closed_maximal_negation_iff[OF rich maximal al ac] absent])
      have negative_language: "book_theory_formula \<Sigma> G (book_not G A)"
        by (rule book_not_language[OF rich al])
      have negative: "book_theory_derivable \<Sigma> G M (book_not G A)"
        by (rule book_theory_derivable.Assumption[OF negative_member negative_language])
      have schema: "book_theory_derivable \<Sigma> G {} (book_imp (book_not G A) (book_imp A B))"
        by (rule book_theory_explosion_curried[OF rich al bl])
      have lifted: "book_theory_derivable \<Sigma> G M (book_imp (book_not G A) (book_imp A B))"
        by (rule book_theory_derivable_mono[OF schema empty_subsetI])
      show ?thesis by (rule book_theory_derivable.MP[OF negative lifted implication_language])
    next
      assume member: "B \<in> M"
      have consequent: "book_theory_derivable \<Sigma> G M B"
        by (rule book_theory_derivable.Assumption[OF member bl])
      show ?thesis by (rule book_theory_imp_weaken[OF consequent al bl])
    qed
    show "book_imp A B \<in> M"
      by (rule book_closed_maximal_derivable_member[OF maximal implication_language implication_closed derivation])
  qed
qed

end
