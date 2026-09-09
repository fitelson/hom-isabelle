theory Bacon_Book_Full_Classicism_Fresh_Background
  imports Bacon_Book_Full_Classicism_Theory_Retraction
    Bacon_Book_Environment_Development.Bacon_Book_Conditional_Witness
begin

section \<open>Recovering the new full-C background from old C theorems\<close>

lemma book_full_C_restore_one_constant:
  assumes names: "named_in_signature (book_add_constant \<Sigma> c \<sigma>) A"
    and fresh: "v \<sigma> \<notin> named_vars A"
  shows "named_subst (v \<sigma>) (NConst c \<sigma>) (named_retract \<Sigma> v A) = A"
  using names fresh by (induction A) (auto simp: book_add_constant_def split: if_splits)

theorem book_full_C_new_constant_theorem_from_old_background:
  assumes rich: "sg_rich G"
    and derivation: "book_full_C_proves (book_add_constant \<Sigma> c \<sigma>) G A"
  shows "book_theory_derivable (book_add_constant \<Sigma> c \<sigma>) G
    ({B. book_full_C_proves \<Sigma> G B} \<union> S) A"
proof -
  let ?\<Omega> = "book_add_constant \<Sigma> c \<sigma>"
  obtain N where support: "book_full_C_retraction_support \<Sigma> G A N"
    using book_full_C_retraction_support_exists[where \<Omega>=\<Sigma>, OF rich derivation] by blast
  have finite: "finite N" and contains: "named_vars A \<subseteq> N"
    using support unfolding book_full_C_retraction_support_def by blast+
  let ?v = "\<lambda>\<tau>. SOME n. G n = \<tau> \<and> n \<notin> N"
  have chosen: "G (?v \<tau>) = \<tau> \<and> ?v \<tau> \<notin> N" for \<tau>
    by (rule someI_ex, rule sg_rich_fresh[OF rich finite])
  have stock: "\<And>\<tau>. G (?v \<tau>) = \<tau>" by (rule conjunct1[OF chosen])
  have avoid: "\<And>\<tau>. ?v \<tau> \<notin> N" by (rule conjunct2[OF chosen])
  have old_C: "book_full_C_proves \<Sigma> G (named_retract \<Sigma> ?v A)"
    by (rule book_full_C_retraction_apply[OF support stock avoid])
  have old_type: "book_theory_formula \<Sigma> G (named_retract \<Sigma> ?v A)"
    by (rule book_full_C_proves_language[OF rich old_C])
  have inclusion: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> ?\<Omega> \<tau>" by (rule book_add_constant_subset)
  have new_type: "book_theory_formula ?\<Omega> G (named_retract \<Sigma> ?v A)"
    by (rule book_language_signature_mono[OF old_type inclusion])
  have old_member: "named_retract \<Sigma> ?v A \<in> {B. book_full_C_proves \<Sigma> G B} \<union> S"
    by (rule UnI1; simp only: mem_Collect_eq; rule old_C)
  have premise: "book_theory_derivable ?\<Omega> G ({B. book_full_C_proves \<Sigma> G B} \<union> S) (named_retract \<Sigma> ?v A)"
    by (rule book_theory_derivable.Assumption[OF old_member new_type])
  have payload: "book_in_language book_minimal_logical_type UNIV ?\<Omega> G (NConst c \<sigma>) (G (?v \<sigma>))"
    by (simp only: stock; simp add: book_language_const_iff book_add_constant_def)
  have free_for: "named_free_for (NConst c \<sigma>) (?v \<sigma>) (named_retract \<Sigma> ?v A)"
    by (rule book_exists_closed_free_for; simp)
  have restored: "book_theory_derivable ?\<Omega> G ({B. book_full_C_proves \<Sigma> G B} \<union> S)
      (named_subst (?v \<sigma>) (NConst c \<sigma>) (named_retract \<Sigma> ?v A))"
    by (rule book_theory_variable_substitution[OF rich premise payload free_for])
  have original_names: "named_in_signature ?\<Omega> A"
    by (rule book_language_signature[OF book_full_C_proves_language[OF rich derivation]])
  have fresh: "?v \<sigma> \<notin> named_vars A" using avoid contains by blast
  show ?thesis using restored by (simp only: book_full_C_restore_one_constant[
    where \<Sigma>=\<Sigma> and c=c and \<sigma>=\<sigma> and v="?v", OF original_names fresh])
qed

text \<open>
  For one added constant, retraction gives an old C theorem with a fresh
  free variable in its place. Ordinary H theory generalization and UI
  restore that constant without changing the background assumptions.
  Consequently all new-language C theorems are available from the old
  C background in the enlarged language. This uses no uniform fresh
  variable for the entire infinite C theorem set and no model premise.
\<close>

end
