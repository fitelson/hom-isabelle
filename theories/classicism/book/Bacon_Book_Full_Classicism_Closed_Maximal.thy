theory Bacon_Book_Full_Classicism_Closed_Maximal
  imports Bacon_Book_Full_Classicism_Closed_Fragment
begin

section \<open>Actual closed maximal extensions above the C background\<close>

definition book_full_C_closed_maximal_extension ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_full_C_closed_maximal_extension \<Sigma> G S M \<longleftrightarrow>
    book_closed_maximal_extension \<Sigma> G (book_full_C_closed_theorems \<Sigma> G \<union> S) M"

lemma book_full_C_closed_maximal_data:
  assumes maximal: "book_full_C_closed_maximal_extension \<Sigma> G S M"
  shows "book_closed_formula_set \<Sigma> G M"
    and "book_theory_consistent \<Sigma> G M"
    and "book_full_C_closed_theorems \<Sigma> G \<subseteq> M" and "S \<subseteq> M"
  using maximal unfolding book_full_C_closed_maximal_extension_def book_closed_maximal_extension_def by blast+

lemma book_full_C_closed_maximal_consequence_iff:
  assumes rich: "sg_rich G" and maximal: "book_full_C_closed_maximal_extension \<Sigma> G S M"
  shows "book_full_C_theory_derivable \<Sigma> G M A \<longleftrightarrow> book_theory_derivable \<Sigma> G M A"
proof -
  have language: "book_theory_formula \<Sigma> G B" if "B \<in> M" for B
    by (rule conjunct1[OF book_closed_formula_set_member[OF book_full_C_closed_maximal_data(1)[OF maximal] that]])
  have absorbed: "book_full_C_closed_theorems \<Sigma> G \<union> M = M"
    using book_full_C_closed_maximal_data(3)[OF maximal] by blast
  show ?thesis by (simp only: book_full_C_consequence_closed_fragment_iff[OF rich language] absorbed)
qed

theorem book_full_C_closed_maximal_consistent:
  assumes rich: "sg_rich G" and maximal: "book_full_C_closed_maximal_extension \<Sigma> G S M"
  shows "book_full_C_theory_consistent \<Sigma> G M"
  using book_full_C_closed_maximal_data(2)[OF maximal]
  by (simp add: book_full_C_theory_consistent_def book_theory_consistent_def book_full_C_closed_maximal_consequence_iff[OF rich maximal])

theorem book_full_C_closed_maximal_consequence:
  assumes rich: "sg_rich G" and maximal: "book_full_C_closed_maximal_extension \<Sigma> G S M"
    and derivation: "book_full_C_theory_derivable \<Sigma> G M A" and closed: "named_fv A = {}"
  shows "A \<in> M"
proof -
  have al: "book_theory_formula \<Sigma> G A" by (rule book_full_C_theory_language[OF rich derivation])
  have base: "book_theory_derivable \<Sigma> G M A"
    using derivation by (simp only: book_full_C_closed_maximal_consequence_iff[OF rich maximal])
  have old: "book_closed_maximal_extension \<Sigma> G (book_full_C_closed_theorems \<Sigma> G \<union> S) M"
    using maximal unfolding book_full_C_closed_maximal_extension_def .
  show ?thesis by (rule book_closed_maximal_derivable_member[OF old al closed base])
qed

theorem book_full_C_closed_maximal_decides:
  assumes rich: "sg_rich G" and maximal: "book_full_C_closed_maximal_extension \<Sigma> G S M"
    and al: "book_theory_formula \<Sigma> G A" and closed: "named_fv A = {}"
  shows "A \<in> M \<or> book_not G A \<in> M"
  using maximal unfolding book_full_C_closed_maximal_extension_def
  by (rule book_closed_maximal_decides[OF rich _ al closed])

theorem book_full_C_closed_maximal_extension_exists:
  assumes rich: "sg_rich G" and closed: "book_closed_formula_set \<Sigma> G S"
    and consistent: "book_full_C_theory_consistent \<Sigma> G S"
  shows "\<exists>M. book_full_C_closed_maximal_extension \<Sigma> G S M"
proof -
  have language: "book_theory_formula \<Sigma> G B" if "B \<in> S" for B
    by (rule conjunct1[OF book_closed_formula_set_member[OF closed that]])
  have closed_base: "book_closed_formula_set \<Sigma> G (book_full_C_closed_theorems \<Sigma> G \<union> S)"
    using book_full_C_closed_theorems_closed[OF rich] closed unfolding book_closed_formula_set_def by blast
  have consistent_base: "book_theory_consistent \<Sigma> G (book_full_C_closed_theorems \<Sigma> G \<union> S)"
    using consistent by (simp only: book_full_C_consistency_closed_fragment_iff[OF rich language])
  show ?thesis unfolding book_full_C_closed_maximal_extension_def
    by (rule book_closed_maximal_extension_exists[OF closed_base consistent_base])
qed

text \<open>
  These maximal extensions are actually constructed by the previously
  verified closed-set Zorn argument, with the complete C background
  recovered from its closed fragment. They decide all closed formulas
  and are closed under closed C-theory consequences in the fixed signature.
  They are not yet witness-complete canonical worlds with the expanded
  language and infinite unused-name reserve of Definition 18.8.
\<close>

end
