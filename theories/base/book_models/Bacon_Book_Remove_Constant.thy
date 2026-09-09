theory Bacon_Book_Remove_Constant
  imports Bacon_Book_Constant_Substitution_Syntax Bacon_Book_Theory_Signature_Conservativity
begin

section \<open>Removing one typed constant from the declared signature\<close>

text \<open>
  Remove only c:σ, retaining occurrences of the same name at other
  types. On a term of ℒ(Σ), retraction into the reduced signature is
  literally replacement of c:σ by vσ. This raw equation does not require
  freshness: both operations preserve binders and can capture variables.
  Source role: the typed constant-substitution mechanism of Definition 5.2,
  p.99, separated from its free-for condition.
\<close>

definition book_remove_constant :: "'c ssignature \<Rightarrow> 'c \<Rightarrow> otype \<Rightarrow> 'c ssignature" where
  "book_remove_constant \<Sigma> c \<sigma> \<tau> = (if \<tau> = \<sigma> then \<Sigma> \<tau> - {c} else \<Sigma> \<tau>)"

lemma book_remove_constant_subset:
  "book_remove_constant \<Sigma> c \<sigma> \<tau> \<subseteq> \<Sigma> \<tau>"
  by (auto simp: book_remove_constant_def)

theorem book_remove_constant_retract:
  assumes names: "named_in_signature \<Sigma> A"
  shows "named_retract (book_remove_constant \<Sigma> c \<sigma>) v A =
    book_const_subst c \<sigma> (NVar (v \<sigma>)) A"
  using names
proof (induction A)
  case (NVar n)
  show ?case by simp
next
  case (NConst d \<tau>)
  have original: "d \<in> \<Sigma> \<tau>" using NConst.prems by simp
  show ?case using original by (cases "\<tau> = \<sigma>"; cases "d = c")
    (auto simp: book_remove_constant_def)
next
  case (NLogical l)
  show ?case by simp
next
  case (NApp F A)
  have fn: "named_in_signature \<Sigma> F" and an: "named_in_signature \<Sigma> A"
    using NApp.prems by simp_all
  show ?case by (simp only: named_retract.simps book_const_subst.simps NApp.IH(1)[OF fn] NApp.IH(2)[OF an])
next
  case (NLam n A)
  have body: "named_in_signature \<Sigma> A" using NLam.prems by simp
  show ?case by (simp only: named_retract.simps book_const_subst.simps NLam.IH[OF body])
qed

section \<open>An empty-premise proof admits a fresh variable in place of c:σ\<close>

text \<open>
  If ⊢Σ A and F is a finite set of forbidden names, choose x:σ
  outside F and every name in the proof's retraction support. Retract
  into Σ without c:σ, identify the resulting term by the raw equation,
  then enlarge the signature back to Σ.

  Status: this derives only the fresh-variable replacement of an
  empty-premise proof. It does not assume an arbitrary payload-substitution
  rule, a model, or the identification of theory derivability with H.
  The proof support contains Vars(A), and it also protects intermediate
  β/η and Gen side conditions. No premise c ∈ Σσ is necessary.
\<close>

theorem book_theory_fresh_constant_variable:
  assumes rich: "sg_rich G" and derivation: "book_theory_derivable \<Sigma> G {} A"
    and finite_F: "finite F"
  shows "\<exists>x. G x = \<sigma> \<and> x \<notin> named_vars A \<union> F \<and>
    book_theory_derivable \<Sigma> G {} (book_const_subst c \<sigma> (NVar x) A)"
proof -
  let ?\<Omega> = "book_remove_constant \<Sigma> c \<sigma>"
  obtain N where support: "book_theory_retraction_support ?\<Omega> G {} A N"
    using book_theory_derivable_retraction_support[where \<Omega>="?\<Omega>", OF derivation] by (elim exE)
  have finite_N: "finite N" by (rule book_theory_retraction_support_finite[OF support])
  have names_in_N: "named_vars A \<subseteq> N"
    by (rule conjunct1[OF conjunct2[OF support[unfolded book_theory_retraction_support_def]]])
  have finite_union: "finite (N \<union> F)" by (rule finite_UnI[OF finite_N finite_F])
  obtain x where x_type: "G x = \<sigma>" and x_fresh: "x \<notin> N \<union> F"
    using sg_rich_fresh[where \<sigma>=\<sigma> and S="N \<union> F", OF rich finite_union] by (elim exE conjE)
  have x_not_N: "x \<notin> N" using x_fresh by blast
  have endpoint_fresh: "x \<notin> named_vars A \<union> F" using x_fresh names_in_N by blast
  let ?w = "\<lambda>\<tau>. SOME n. G n = \<tau> \<and> n \<notin> N"
  have choices: "G (?w \<tau>) = \<tau> \<and> ?w \<tau> \<notin> N" for \<tau>
    by (rule someI_ex, rule sg_rich_fresh[OF rich finite_N])
  have w_type: "G (?w \<tau>) = \<tau>" for \<tau> by (rule conjunct1[OF choices])
  have w_fresh: "?w \<tau> \<notin> N" for \<tau> by (rule conjunct2[OF choices])
  let ?v = "\<lambda>\<tau>. if \<tau> = \<sigma> then x else ?w \<tau>"
  have stock: "G (?v \<tau>) = \<tau>" for \<tau>
    by (cases "\<tau> = \<sigma>") (simp_all add: x_type w_type)
  have avoids: "?v \<tau> \<notin> N" for \<tau>
    by (cases "\<tau> = \<sigma>") (simp_all add: x_not_N w_fresh)
  have retracted: "book_theory_derivable ?\<Omega> G (image (named_retract ?\<Omega> ?v) {})
    (named_retract ?\<Omega> ?v A)"
    by (rule book_theory_retraction_support_apply[OF support stock avoids])
  have empty_retracted: "book_theory_derivable ?\<Omega> G {} (named_retract ?\<Omega> ?v A)"
    using retracted by (simp only: image_empty)
  have inclusion: "?\<Omega> \<tau> \<subseteq> \<Sigma> \<tau>" for \<tau> by (rule book_remove_constant_subset)
  have widened: "book_theory_derivable \<Sigma> G {} (named_retract ?\<Omega> ?v A)"
    by (rule book_theory_signature_mono[OF empty_retracted inclusion])
  have original_names: "named_in_signature \<Sigma> A"
    by (rule book_language_signature[OF book_theory_derivable_language[OF derivation rich]])
  have representation: "named_retract ?\<Omega> ?v A = book_const_subst c \<sigma> (NVar x) A"
    using book_remove_constant_retract[where v="?v", OF original_names] by simp
  have replaced: "book_theory_derivable \<Sigma> G {} (book_const_subst c \<sigma> (NVar x) A)"
    using widened by (simp only: representation)
  show ?thesis by (rule exI[where x=x], rule conjI[OF x_type conjI[OF endpoint_fresh replaced]])
qed

end
