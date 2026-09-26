theory Bacon_Book_ZF_Full_C_Declared_Names_Completeness
  imports Bacon_Book_ZF_Full_C_Small_Carrier_Completeness
    Bacon_Book_ZF_Modal_Representation.Bacon_Book_ZF_Declared_Names_Existence
begin

section \<open>Completeness of full-type Classicism for ZF-small declared names\<close>

text \<open>
  The only signature-size hypothesis is now declared-name ZF-smallness:
  the union of the declared constants injects into the elements of an
  actual ZF set, while the name carrier is arbitrary. The proofs are the
  earlier ones with the declared-names existence theorem substituted;
  soundness never needed a cardinality hypothesis. The countable and
  small-carrier equivalences are retained with their own proofs and also
  follow from these.
\<close>

theorem book_full_C_theory_complete_small_declared:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes rich: "sg_rich G"
    and declared: "book_ZF_small_declared \<Sigma> f U"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
    and consequence: "book_ZF_full_C_consequence \<Sigma> G S A"
  shows "book_full_C_theory_derivable \<Sigma> G S A"
proof (rule book_full_C_theory_complete_from_existence[OF rich _ language al consequence])
  fix T assume tl: "\<And>B. B \<in> T \<Longrightarrow> book_theory_formula \<Sigma> G B" and tc: "book_full_C_theory_consistent \<Sigma> G T"
  show "book_ZF_full_C_satisfiable \<Sigma> G T"
    unfolding book_ZF_full_C_satisfiable_def
    by (rule book_full_C_small_declared_nontrivial_modal_model_exists[OF rich declared tl tc])
qed

theorem book_full_C_theory_derivable_iff_consequence_small_declared:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes rich: "sg_rich G"
    and declared: "book_ZF_small_declared \<Sigma> f U"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
  shows "book_full_C_theory_derivable \<Sigma> G S A \<longleftrightarrow> book_ZF_full_C_consequence \<Sigma> G S A"
  using book_full_C_theory_sound[OF rich] book_full_C_theory_complete_small_declared[OF rich declared language al] by blast

theorem book_full_C_theory_consistent_iff_satisfiable_small_declared:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes rich: "sg_rich G"
    and declared: "book_ZF_small_declared \<Sigma> f U"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_full_C_theory_consistent \<Sigma> G S \<longleftrightarrow> book_ZF_full_C_satisfiable \<Sigma> G S"
proof
  assume consistent: "book_full_C_theory_consistent \<Sigma> G S"
  show "book_ZF_full_C_satisfiable \<Sigma> G S"
    unfolding book_ZF_full_C_satisfiable_def
    by (rule book_full_C_small_declared_nontrivial_modal_model_exists[OF rich declared language consistent])
next
  assume satisfiable: "book_ZF_full_C_satisfiable \<Sigma> G S"
  show "book_full_C_theory_consistent \<Sigma> G S" by (rule book_full_C_satisfiable_consistent[OF rich satisfiable])
qed

subsection \<open>The type ZF as name carrier with set-bounded declared names\<close>

corollary book_full_C_theory_derivable_iff_consequence_ZF_carrier:
  fixes \<Sigma> :: "ZF ssignature"
  assumes rich: "sg_rich G"
    and bounded: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> explode U"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
  shows "book_full_C_theory_derivable \<Sigma> G S A \<longleftrightarrow> book_ZF_full_C_consequence \<Sigma> G S A"
proof -
  have declared: "book_ZF_small_declared \<Sigma> id U"
    by (rule book_ZF_small_declaredI[OF inj_on_id]; use bounded in auto)
  show ?thesis by (rule book_full_C_theory_derivable_iff_consequence_small_declared[OF rich declared language al])
qed

corollary book_full_C_theory_consistent_iff_satisfiable_ZF_carrier:
  fixes \<Sigma> :: "ZF ssignature"
  assumes rich: "sg_rich G"
    and bounded: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> explode U"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_full_C_theory_consistent \<Sigma> G S \<longleftrightarrow> book_ZF_full_C_satisfiable \<Sigma> G S"
proof -
  have declared: "book_ZF_small_declared \<Sigma> id U"
    by (rule book_ZF_small_declaredI[OF inj_on_id]; use bounded in auto)
  show ?thesis by (rule book_full_C_theory_consistent_iff_satisfiable_small_declared[OF rich declared language])
qed

text \<open>
  Scope. As for the earlier theorems: full simple types over the minimal
  primitive language in HOL-ZF, rich variable stock, the nontrivial model
  class, root (local) consequence under every typed assignment, the
  documented future-restricted implication and literal box conventions.
  Neither equivalence assumes consistency of S. Declared-name smallness
  is a sufficient hypothesis of this construction; Theorem 18.4's printed
  statement carries no cardinality qualification and its displayed proof
  is countable.
\<close>

end
