theory Bacon_Book_Logic
  imports Bacon_Book_Theory_Simultaneous_Substitution
begin

section \<open>The least theory is the least logic\<close>

text \<open>
  A logic is a theory closed under uniform typed, capture-free replacement
  of finitely many free variables and nonlogical constants (Definition 5.2,
  p.99). H is membership in every such logic (Definition 5.3). We prove,
  rather than stipulate, that H equals empty-premise derivability in the
  original theory calculus (Comprehension Check 5.1, p.102).

  Scope: the represented full F named language over the book's minimal
  logical basis, a declared nonlogical signature Σ and rich variable stock
  G. The finite-table representation uses effective first-match entries;
  payloads have their declared key types and belong to the same language.
  Substitution is derived; it is not an extra constructor of the calculus.
  No semantic, completeness, or paper-H premise enters this identification.
\<close>

definition book_higher_order_logic ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_higher_order_logic \<Sigma> G T \<longleftrightarrow>
    book_higher_order_theory \<Sigma> G T \<and>
    (\<forall>A\<in>T. \<forall>\<theta>.
      book_subst_table_language book_minimal_logical_type UNIV \<Sigma> G \<theta> \<longrightarrow>
      book_simult_free_for G \<theta> A \<longrightarrow> book_simult_subst G \<theta> A \<in> T)"

definition book_H :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> bool" where
  "book_H \<Sigma> G A \<longleftrightarrow> (\<forall>T. book_higher_order_logic \<Sigma> G T \<longrightarrow> A \<in> T)"

lemma book_logic_is_theory:
  "book_higher_order_logic \<Sigma> G T \<Longrightarrow> book_higher_order_theory \<Sigma> G T"
  unfolding book_higher_order_logic_def by (rule conjunct1)

theorem book_least_theory_is_logic:
  assumes rich: "sg_rich G"
  shows "book_higher_order_logic \<Sigma> G {A. book_theory_derivable \<Sigma> G {} A}"
proof (unfold book_higher_order_logic_def, rule conjI)
  show "book_higher_order_theory \<Sigma> G {A. book_theory_derivable \<Sigma> G {} A}"
    by (rule book_derivable_consequences_form_theory[OF rich])
next
  show "\<forall>A\<in>{A. book_theory_derivable \<Sigma> G {} A}. \<forall>\<theta>.
    book_subst_table_language book_minimal_logical_type UNIV \<Sigma> G \<theta> \<longrightarrow>
    book_simult_free_for G \<theta> A \<longrightarrow>
    book_simult_subst G \<theta> A \<in> {A. book_theory_derivable \<Sigma> G {} A}"
  proof (intro ballI allI impI)
    fix A \<theta>
    assume member: "A \<in> {A. book_theory_derivable \<Sigma> G {} A}"
      and table: "book_subst_table_language book_minimal_logical_type UNIV \<Sigma> G \<theta>"
      and permitted: "book_simult_free_for G \<theta> A"
    have derivation: "book_theory_derivable \<Sigma> G {} A" using member by simp
    have result: "book_theory_derivable \<Sigma> G {} (book_simult_subst G \<theta> A)"
      by (rule book_theory_simultaneous_substitution[OF rich derivation table permitted])
    show "book_simult_subst G \<theta> A \<in> {A. book_theory_derivable \<Sigma> G {} A}"
      using result by simp
  qed
qed

theorem book_H_iff_theory:
  assumes rich: "sg_rich G"
  shows "book_H \<Sigma> G A \<longleftrightarrow> book_theory_derivable \<Sigma> G {} A"
proof
  assume in_H: "book_H \<Sigma> G A"
  have least_is_logic: "book_higher_order_logic \<Sigma> G {B. book_theory_derivable \<Sigma> G {} B}"
    by (rule book_least_theory_is_logic[OF rich])
  show "book_theory_derivable \<Sigma> G {} A"
    using in_H least_is_logic unfolding book_H_def by blast
next
  assume derivation: "book_theory_derivable \<Sigma> G {} A"
  show "book_H \<Sigma> G A"
  proof (unfold book_H_def, intro allI impI)
    fix T
    assume logic: "book_higher_order_logic \<Sigma> G T"
    have theory_ok: "book_higher_order_theory \<Sigma> G T"
      by (rule book_logic_is_theory[OF logic])
    show "A \<in> T" by (rule book_theory_contains_derivation[OF theory_ok derivation empty_subsetI])
  qed
qed

corollary book_H_language:
  assumes rich: "sg_rich G" and in_H: "book_H \<Sigma> G A"
  shows "book_theory_formula \<Sigma> G A"
proof -
  have derivation: "book_theory_derivable \<Sigma> G {} A"
    using in_H by (simp only: book_H_iff_theory[OF rich])
  show ?thesis by (rule book_theory_derivable_language[OF derivation rich])
qed

end
