theory Bacon_Book_Full_Classicism_Theory_Retraction
  imports Bacon_Book_Full_Classicism_Signature_Conservativity Bacon_Book_Full_Classicism_Theory_Consistency
begin

section \<open>One fresh retraction for the finitely used C background\<close>

theorem book_full_C_theory_retraction_fresh:
  assumes rich: "sg_rich G" and derivation: "book_full_C_theory_derivable \<Sigma> G S A"
    and old_premises: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Omega> G B"
    and finite_avoid: "finite Avoid"
  shows "\<exists>v. (\<forall>\<tau>. G (v \<tau>) = \<tau>) \<and> (\<forall>\<tau>. v \<tau> \<notin> Avoid) \<and>
    book_full_C_theory_derivable \<Omega> G S (named_retract \<Omega> v A)"
proof -
  let ?C = "{B. book_full_C_proves \<Sigma> G B}"
  have original: "book_theory_derivable \<Sigma> G (?C \<union> S) A"
    using derivation unfolding book_full_C_theory_derivable_def .
  obtain U where finite_U: "finite U" and subset: "U \<subseteq> ?C \<union> S"
    and proof_U: "book_theory_derivable \<Sigma> G U A"
    using book_theory_derivable_finite_support[OF original] by blast
  let ?Used = "U \<inter> ?C"
  let ?N = "\<lambda>B. SOME N. book_full_C_retraction_support \<Omega> G B N"
  have support_C: "book_full_C_retraction_support \<Omega> G B (?N B)" if member: "B \<in> ?Used" for B
  proof -
    have theorem_C: "book_full_C_proves \<Sigma> G B" using member by simp
    show ?thesis by (rule someI_ex, rule book_full_C_retraction_support_exists[OF rich theorem_C])
  qed
  have finite_C: "finite ?Used" using finite_U by simp
  have finite_N: "finite (?N B)" if "B \<in> ?Used" for B
    using support_C[OF that] unfolding book_full_C_retraction_support_def by blast
  have finite_union: "finite (\<Union>B\<in>?Used. ?N B)" by (rule finite_UN_I[OF finite_C finite_N])
  obtain NH where support_H: "book_theory_retraction_support \<Omega> G U A NH"
    using book_theory_derivable_retraction_support[where \<Omega>=\<Omega>, OF proof_U] by blast
  have finite_H: "finite NH" by (rule book_theory_retraction_support_finite[OF support_H])
  let ?All = "NH \<union> (\<Union>B\<in>?Used. ?N B) \<union> Avoid"
  have finite_all: "finite ?All" using finite_H finite_union finite_avoid by simp
  let ?v = "\<lambda>\<tau>. SOME n. G n = \<tau> \<and> n \<notin> ?All"
  have chosen: "G (?v \<tau>) = \<tau> \<and> ?v \<tau> \<notin> ?All" for \<tau>
    by (rule someI_ex, rule sg_rich_fresh[OF rich finite_all])
  have stock: "\<And>\<tau>. G (?v \<tau>) = \<tau>" by (rule conjunct1[OF chosen])
  have fresh_H: "\<And>\<tau>. ?v \<tau> \<notin> NH" using chosen by blast
  have fresh_C: "\<And>\<tau>. ?v \<tau> \<notin> ?N B" if "B \<in> ?Used" for B using chosen that by blast
  have retracted: "book_theory_derivable \<Omega> G (named_retract \<Omega> ?v ` U) (named_retract \<Omega> ?v A)"
    by (rule book_theory_retraction_support_apply[OF support_H stock fresh_H])
  have lifted: "book_theory_derivable \<Omega> G ({B. book_full_C_proves \<Omega> G B} \<union> S) (named_retract \<Omega> ?v A)"
  proof (rule book_theory_derivable_cut[OF retracted])
    fix Q
    assume image: "Q \<in> named_retract \<Omega> ?v ` U"
    obtain B where member: "B \<in> U" and shape: "Q = named_retract \<Omega> ?v B" using image by blast
    show "book_theory_derivable \<Omega> G ({B. book_full_C_proves \<Omega> G B} \<union> S) Q"
    proof (cases "book_full_C_proves \<Sigma> G B")
      case True
      have used: "B \<in> ?Used" using member True by simp
      have target_C: "book_full_C_proves \<Omega> G (named_retract \<Omega> ?v B)"
        by (rule book_full_C_retraction_apply[OF support_C[OF used] stock fresh_C[OF used]])
      have target_type: "book_theory_formula \<Omega> G (named_retract \<Omega> ?v B)"
        by (rule book_full_C_proves_language[OF rich target_C])
      have target_member: "named_retract \<Omega> ?v B \<in> {P. book_full_C_proves \<Omega> G P} \<union> S"
        by (rule UnI1; simp only: mem_Collect_eq; rule target_C)
      show ?thesis by (simp only: shape; rule book_theory_derivable.Assumption[OF target_member target_type])
    next
      case False
      have old: "B \<in> S" using member subset False by blast
      have language: "book_theory_formula \<Omega> G B" by (rule old_premises[OF old])
      have fixed: "named_retract \<Omega> ?v B = B" by (rule named_retract_fixed[OF book_language_signature[OF language]])
      show ?thesis by (simp only: shape fixed; rule book_theory_derivable.Assumption[OF UnI2[OF old] language])
    qed
  qed
  have result: "book_full_C_theory_derivable \<Omega> G S (named_retract \<Omega> ?v A)"
    using lifted unfolding book_full_C_theory_derivable_def .
  have avoids: "\<forall>\<tau>. ?v \<tau> \<notin> Avoid" using chosen by blast
  have types: "\<forall>\<tau>. G (?v \<tau>) = \<tau>" by (rule allI, rule stock)
  show ?thesis by (rule exI[where x="?v"], rule conjI[OF types conjI[OF avoids result]])
qed

theorem book_full_C_theory_foreign_constants_eliminate:
  assumes rich: "sg_rich G" and derivation: "book_full_C_theory_derivable \<Sigma> G S A"
    and old_premises: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Omega> G B"
    and old_conclusion: "named_in_signature \<Omega> A"
  shows "book_full_C_theory_derivable \<Omega> G S A"
proof -
  have finite: "finite ({} :: nat set)" by simp
  obtain v where retracted: "book_full_C_theory_derivable \<Omega> G S (named_retract \<Omega> v A)"
    using book_full_C_theory_retraction_fresh[OF rich derivation old_premises finite] by blast
  show ?thesis using retracted by (simp only: named_retract_fixed[OF old_conclusion])
qed

corollary book_full_C_theory_consistency_signature_preservation:
  assumes rich: "sg_rich G" and consistent: "book_full_C_theory_consistent \<Omega> G S"
    and old_premises: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Omega> G B"
  shows "book_full_C_theory_consistent \<Sigma> G S"
proof (unfold book_full_C_theory_consistent_def, rule notI)
  assume contradiction: "book_full_C_theory_derivable \<Sigma> G S (book_bottom G)"
  have old_bottom: "named_in_signature \<Omega> (book_bottom G)" by (simp add: book_bottom_def)
  have reflected: "book_full_C_theory_derivable \<Omega> G S (book_bottom G)"
    by (rule book_full_C_theory_foreign_constants_eliminate[OF rich contradiction old_premises old_bottom])
  show False using consistent reflected unfolding book_full_C_theory_consistent_def by contradiction
qed

text \<open>
  No finite fresh-name set is assumed to work for all C theorems.
  Finite H proof support selects the C theorems actually used, and the
  finite union of their individually proved retraction supports is
  combined with the H proof's support and the requested avoidance set.
  The additional assumptions remain in their old language.

  The first theorem retains the retracted conclusion and the fresh
  variable choices, as needed for a fresh-witness argument. The second
  returns an old-language conclusion unchanged. Neither supplies witness
  completeness or assumes C in the new signature by fiat.
  The consistency corollary needs no signature-inclusion premise:
  eliminating foreign constants reflects any putative contradiction
  into the signature where S is already well typed. In the intended
  expansion application, inclusion separately ensures S remains a
  well-formed premise set in the enlarged language.
\<close>

end
