theory Bacon_Book_Conjunction_Logic
  imports Bacon_Book_Conjunction_Theory Bacon_Book_Conjunction_Simultaneous_Substitution
begin

section \<open>The least theory equals the least logic with primitive conjunction\<close>

text \<open>
  A logic is a theory closed under finite, typed, capture-free simultaneous
  substitution for free variables and ordinary nonlogical constants.
  H∧ is membership in every such logic. These are independent definitions;
  H∧ = {A : ⊢∧A} is proved below using substitution admissibility.

  Sources: Definitions 5.2–5.3, pp.99–100, Comprehension Check 5.1,
  p.102, and the primitive-conjunction extension of §5.2, p.104.
  Definition 5.2 forbids capture upon replacement; the table predicate
  implements that condition, not the stricter printed recursive test 3.7.

  Scope: full F over →, ∀ and primitive ∧, arbitrary nonlogical
  signatures, and rich G. A table uses first-match entries and inserts
  each original payload once. Logical symbols, including ∧, stay fixed.
  Neither model existence nor semantic completeness proves this identity.
\<close>

definition book_conj_higher_order_logic ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_conj_term set \<Rightarrow> bool" where
  "book_conj_higher_order_logic \<Sigma> G T \<longleftrightarrow>
    book_conj_higher_order_theory \<Sigma> G T \<and>
    (\<forall>A\<in>T. \<forall>\<theta>.
      book_subst_table_language book_conj_logical_type UNIV \<Sigma> G \<theta> \<longrightarrow>
      book_simult_free_for G \<theta> A \<longrightarrow> book_simult_subst G \<theta> A \<in> T)"

definition book_conj_H ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_conj_term \<Rightarrow> bool" where
  "book_conj_H \<Sigma> G A \<longleftrightarrow>
    (\<forall>T. book_conj_higher_order_logic \<Sigma> G T \<longrightarrow> A \<in> T)"

lemma book_conj_logic_is_theory:
  "book_conj_higher_order_logic \<Sigma> G T \<Longrightarrow> book_conj_higher_order_theory \<Sigma> G T"
  unfolding book_conj_higher_order_logic_def by (rule conjunct1)

theorem book_conj_least_theory_is_logic:
  assumes rich: "sg_rich G"
  shows "book_conj_higher_order_logic \<Sigma> G {A. book_conj_theory_derivable \<Sigma> G {} A}"
proof (unfold book_conj_higher_order_logic_def, rule conjI)
  show "book_conj_higher_order_theory \<Sigma> G {A. book_conj_theory_derivable \<Sigma> G {} A}"
    by (rule book_conj_least_theory_is_theory[OF rich])
next
  show "\<forall>A\<in>{A. book_conj_theory_derivable \<Sigma> G {} A}. \<forall>\<theta>.
    book_subst_table_language book_conj_logical_type UNIV \<Sigma> G \<theta> \<longrightarrow>
    book_simult_free_for G \<theta> A \<longrightarrow>
    book_simult_subst G \<theta> A \<in> {A. book_conj_theory_derivable \<Sigma> G {} A}"
  proof (intro ballI allI impI)
    fix A \<theta>
    assume member: "A \<in> {A. book_conj_theory_derivable \<Sigma> G {} A}"
      and table: "book_subst_table_language book_conj_logical_type UNIV \<Sigma> G \<theta>"
      and permitted: "book_simult_free_for G \<theta> A"
    have derivation: "book_conj_theory_derivable \<Sigma> G {} A" using member by simp
    have result: "book_conj_theory_derivable \<Sigma> G {} (book_simult_subst G \<theta> A)"
      by (rule book_conj_theory_simultaneous_substitution[OF rich derivation table permitted])
    show "book_simult_subst G \<theta> A \<in> {A. book_conj_theory_derivable \<Sigma> G {} A}"
      using result by simp
  qed
qed

theorem book_conj_H_iff_theory:
  assumes rich: "sg_rich G"
  shows "book_conj_H \<Sigma> G A \<longleftrightarrow> book_conj_theory_derivable \<Sigma> G {} A"
proof
  assume in_H: "book_conj_H \<Sigma> G A"
  have least_is_logic:
    "book_conj_higher_order_logic \<Sigma> G {B. book_conj_theory_derivable \<Sigma> G {} B}"
    by (rule book_conj_least_theory_is_logic[OF rich])
  show "book_conj_theory_derivable \<Sigma> G {} A"
    using in_H least_is_logic unfolding book_conj_H_def by blast
next
  assume derivation: "book_conj_theory_derivable \<Sigma> G {} A"
  show "book_conj_H \<Sigma> G A"
  proof (unfold book_conj_H_def, intro allI impI)
    fix T
    assume logic: "book_conj_higher_order_logic \<Sigma> G T"
    have theory_ok: "book_conj_higher_order_theory \<Sigma> G T"
      by (rule book_conj_logic_is_theory[OF logic])
    show "A \<in> T"
      by (rule book_conj_theory_contains_derivation[OF theory_ok derivation empty_subsetI])
  qed
qed

corollary book_conj_H_language:
  assumes rich: "sg_rich G" and in_H: "book_conj_H \<Sigma> G A"
  shows "book_conj_formula \<Sigma> G A"
proof -
  have derivation: "book_conj_theory_derivable \<Sigma> G {} A"
    using in_H by (simp only: book_conj_H_iff_theory[OF rich])
  show ?thesis by (rule book_conj_theory_derivable_language[OF derivation rich])
qed

end
