theory Bacon_Book_Classicism_Closed_Fragment
  imports Bacon_Book_Classicism_Theory_Rules
    Bacon_Book_Environment_Development.Bacon_Book_Closed_Negation_Complete
begin

section \<open>Closed C theorems recover the entire C background\<close>

definition book_C_closed_theorems :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set" where
  "book_C_closed_theorems \<Sigma> G = {A. book_C_proves \<Sigma> G A \<and> named_fv A = {}}"

lemma book_C_closed_theorems_closed:
  assumes rich: "sg_rich G"
  shows "book_closed_formula_set \<Sigma> G (book_C_closed_theorems \<Sigma> G)"
  using book_C_proves_language[OF rich] by (auto simp: book_closed_formula_set_def book_C_closed_theorems_def)

theorem book_C_universal_closure:
  assumes rich: "sg_rich G" and premise: "book_C_proves \<Sigma> G A"
  shows "book_C_proves \<Sigma> G (book_universal_closure G A)"
proof -
  have al: "book_theory_formula \<Sigma> G A" by (rule book_C_proves_language[OF rich premise])
  have initial: "book_theory_derivable \<Sigma> G {B. book_C_proves \<Sigma> G B} A"
    by (rule book_theory_derivable.Assumption; (simp add: premise | rule al))
  have universal: "book_theory_derivable \<Sigma> G {B. book_C_proves \<Sigma> G B} (book_universal_closure G A)"
    using initial by (simp only: book_theory_universal_closure_iff[OF rich al])
  show ?thesis by (rule book_C_contains_theory_derivation[OF rich universal]; simp)
qed

theorem book_C_theorem_from_closed_fragment:
  assumes rich: "sg_rich G" and premise: "book_C_proves \<Sigma> G A"
  shows "book_theory_derivable \<Sigma> G (book_C_closed_theorems \<Sigma> G \<union> S) A"
proof -
  have al: "book_theory_formula \<Sigma> G A" by (rule book_C_proves_language[OF rich premise])
  have member: "book_universal_closure G A \<in> book_C_closed_theorems \<Sigma> G"
    using book_C_universal_closure[OF rich premise] book_universal_closure_closed[of G A]
    by (simp add: book_C_closed_theorems_def)
  have universal: "book_theory_derivable \<Sigma> G (book_C_closed_theorems \<Sigma> G \<union> S) (book_universal_closure G A)"
    by (rule book_theory_derivable.Assumption[OF UnI1[OF member] book_universal_closure_language[OF al]])
  show ?thesis using universal by (simp only: book_theory_universal_closure_iff[OF rich al])
qed

theorem book_C_consequence_closed_fragment_iff:
  assumes rich: "sg_rich G" and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_C_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    book_theory_derivable \<Sigma> G (book_C_closed_theorems \<Sigma> G \<union> S) A"
proof
  assume derivation: "book_C_theory_derivable \<Sigma> G S A"
  have base: "book_theory_derivable \<Sigma> G ({B. book_C_proves \<Sigma> G B} \<union> S) A"
    using derivation unfolding book_C_theory_derivable_def .
  show "book_theory_derivable \<Sigma> G (book_C_closed_theorems \<Sigma> G \<union> S) A"
  proof (rule book_theory_derivable_cut[OF base])
    fix B
    assume member: "B \<in> {B. book_C_proves \<Sigma> G B} \<union> S"
    show "book_theory_derivable \<Sigma> G (book_C_closed_theorems \<Sigma> G \<union> S) B"
    proof (cases "book_C_proves \<Sigma> G B")
      case True
      show ?thesis by (rule book_C_theorem_from_closed_fragment[OF rich True])
    next
      case False
      have in_S: "B \<in> S" using member False by simp
      show ?thesis by (rule book_theory_derivable.Assumption[OF UnI2[OF in_S] language[OF in_S]])
    qed
  qed
next
  assume derivation: "book_theory_derivable \<Sigma> G (book_C_closed_theorems \<Sigma> G \<union> S) A"
  have subset: "book_C_closed_theorems \<Sigma> G \<union> S \<subseteq> {B. book_C_proves \<Sigma> G B} \<union> S"
    by (auto simp: book_C_closed_theorems_def)
  show "book_C_theory_derivable \<Sigma> G S A" unfolding book_C_theory_derivable_def
    by (rule book_theory_derivable_mono[OF derivation subset])
qed

corollary book_C_consistency_closed_fragment_iff:
  assumes rich: "sg_rich G" and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_C_theory_consistent \<Sigma> G S \<longleftrightarrow>
    book_theory_consistent \<Sigma> G (book_C_closed_theorems \<Sigma> G \<union> S)"
  by (simp only: book_C_theory_consistent_def book_theory_consistent_def
    book_C_consequence_closed_fragment_iff[OF rich language])

text \<open>
  A canonical world contains only closed sentences, not every open C
  theorem. The universal closure of each C theorem is itself a closed
  C theorem; ordinary H quantifier elimination recovers the original.
  This proves, rather than assumes, that the closed fragment suffices
  for the entire fixed C background in the consistency construction.
\<close>

end
