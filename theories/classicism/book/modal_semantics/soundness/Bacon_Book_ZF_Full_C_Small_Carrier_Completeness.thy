theory Bacon_Book_ZF_Full_C_Small_Carrier_Completeness
  imports Bacon_Book_ZF_Full_C_Completeness
    Bacon_Book_ZF_Modal_Representation.Bacon_Book_ZF_Small_Carrier_Existence
begin

section \<open>Completeness of full-type Classicism for ZF-small name carriers\<close>

text \<open>
  The countability of the declared signature is replaced by ZF-smallness
  of the name carrier: any type that injects into the elements of a ZF
  set, for instance every countable type, nat set, or the powerset of a
  ZF-small type. All constants of such a carrier may be declared. The
  proofs are the countable ones with the small-carrier existence theorem
  substituted; soundness never needed countability. Neither theorem
  subsumes the other (the countable one allows any carrier type), so
  both are kept.
\<close>

theorem book_full_C_theory_complete_small_carrier:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes rich: "sg_rich G"
    and carrier: "book_ZF_small_carrier f U"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
    and consequence: "book_ZF_full_C_consequence \<Sigma> G S A"
  shows "book_full_C_theory_derivable \<Sigma> G S A"
proof (rule book_full_C_theory_complete_from_existence[OF rich _ language al consequence])
  fix T assume tl: "\<And>B. B \<in> T \<Longrightarrow> book_theory_formula \<Sigma> G B" and tc: "book_full_C_theory_consistent \<Sigma> G T"
  show "book_ZF_full_C_satisfiable \<Sigma> G T"
    unfolding book_ZF_full_C_satisfiable_def
    by (rule book_full_C_small_carrier_nontrivial_modal_model_exists[OF rich carrier tl tc])
qed

theorem book_full_C_theory_derivable_iff_consequence_small_carrier:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes rich: "sg_rich G"
    and carrier: "book_ZF_small_carrier f U"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
  shows "book_full_C_theory_derivable \<Sigma> G S A \<longleftrightarrow> book_ZF_full_C_consequence \<Sigma> G S A"
  using book_full_C_theory_sound[OF rich] book_full_C_theory_complete_small_carrier[OF rich carrier language al] by blast

theorem book_full_C_theory_consistent_iff_satisfiable_small_carrier:
  fixes \<Sigma> :: "'c ssignature" and f :: "'c \<Rightarrow> ZF"
  assumes rich: "sg_rich G"
    and carrier: "book_ZF_small_carrier f U"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_full_C_theory_consistent \<Sigma> G S \<longleftrightarrow> book_ZF_full_C_satisfiable \<Sigma> G S"
proof
  assume consistent: "book_full_C_theory_consistent \<Sigma> G S"
  show "book_ZF_full_C_satisfiable \<Sigma> G S"
    unfolding book_ZF_full_C_satisfiable_def
    by (rule book_full_C_small_carrier_nontrivial_modal_model_exists[OF rich carrier language consistent])
next
  assume satisfiable: "book_ZF_full_C_satisfiable \<Sigma> G S"
  show "book_full_C_theory_consistent \<Sigma> G S" by (rule book_full_C_satisfiable_consistent[OF rich satisfiable])
qed

subsection \<open>An uncountable carrier with no cardinality hypothesis\<close>

corollary book_full_C_theory_derivable_iff_consequence_nat_set:
  fixes \<Sigma> :: "(nat set) ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
    and al: "book_theory_formula \<Sigma> G A"
  shows "book_full_C_theory_derivable \<Sigma> G S A \<longleftrightarrow> book_ZF_full_C_consequence \<Sigma> G S A"
  by (rule book_full_C_theory_derivable_iff_consequence_small_carrier[OF rich book_ZF_small_carrier_nat_set language al])

corollary book_full_C_theory_consistent_iff_satisfiable_nat_set:
  fixes \<Sigma> :: "(nat set) ssignature"
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_full_C_theory_consistent \<Sigma> G S \<longleftrightarrow> book_ZF_full_C_satisfiable \<Sigma> G S"
  by (rule book_full_C_theory_consistent_iff_satisfiable_small_carrier[OF rich book_ZF_small_carrier_nat_set language])

text \<open>
  Scope. As for the countable theorems: full simple types over the
  minimal primitive language in HOL-ZF, rich variable stock, the
  nontrivial model class, root (local) consequence, the documented
  future-restricted implication and literal box conventions. The
  carrier hypothesis is sufficient, not necessary for each particular
  theory; the HOL type ZF itself is not ZF-small, and is covered instead by
  Bacon_Book_ZF_Full_C_Declared_Names_Completeness when the declared union
  is bounded by a ZF set.
\<close>

end
