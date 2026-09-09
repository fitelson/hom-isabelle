theory Bacon_Book_Fresh_Constant_Generalization
  imports Bacon_Book_Theory_Retraction Bacon_Book_Theory_Variable_Substitution
begin

section \<open>Extending one typed component of a signature\<close>

text \<open>
  Σ[c:σ] adds c only at type σ. The freshness condition c∉Σσ does
  not forbid the same name from belonging to another typed component.
  Source role: the fresh constants used in the witness construction,
  Bacon, Proposition 15.4, p.319.
\<close>

definition book_add_constant :: "'c ssignature \<Rightarrow> 'c \<Rightarrow> otype \<Rightarrow> 'c ssignature" where
  "book_add_constant \<Sigma> c \<sigma> \<tau> = (if \<tau> = \<sigma> then insert c (\<Sigma> \<tau>) else \<Sigma> \<tau>)"

lemma book_add_constant_subset:
  "\<Sigma> \<tau> \<subseteq> book_add_constant \<Sigma> c \<sigma> \<tau>"
  by (auto simp: book_add_constant_def)

lemma book_add_constant_member:
  "c \<in> book_add_constant \<Sigma> c \<sigma> \<sigma>"
  by (simp add: book_add_constant_def)

section \<open>A foreign constant in the conclusion becomes a fresh variable\<close>

text \<open>
  If S ⊢Ω ¬Fc, where F and every premise use only Σ and c∉Σσ,
  retract the proof into Σ. Choose each replacement variable outside
  the finite proof support and Vars(F). Retraction fixes S and F
  literally and changes c:σ to a variable x:σ fresh for F.

  The proof signature Ω may be arbitrary; the one-constant extension is
  a specialization. All foreign constants used internally in the proof
  are retracted, not just c. No freshness against every variable name in
  an infinite S is required: old-signature premises are fixed by
  retraction regardless of their variable names.
  Status: a syntactic proof transformation, with no closedness assumption
  on F, model premise, H judgment, or completeness argument.
\<close>

theorem book_theory_fresh_constant_retraction:
  assumes rich: "sg_rich G"
    and fresh: "c \<notin> \<Sigma> \<sigma>"
    and premise_names: "\<And>A. A \<in> S \<Longrightarrow> named_in_signature \<Sigma> A"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and derivation: "book_theory_derivable \<Omega> G S (book_not G (NApp F (NConst c \<sigma>)))"
  shows "\<exists>x. G x = \<sigma> \<and> x \<notin> named_vars F \<and>
    book_theory_derivable \<Sigma> G S (book_not G (NApp F (NVar x)))"
proof -
  let ?A = "book_not G (NApp F (NConst c \<sigma>))"
  obtain N where support: "book_theory_retraction_support \<Sigma> G S ?A N"
    using book_theory_derivable_retraction_support[where \<Omega>=\<Sigma>, OF derivation] by (elim exE)
  have finite_N: "finite N" by (rule book_theory_retraction_support_finite[OF support])
  let ?K = "N \<union> named_vars F"
  have finite_K: "finite ?K" by (rule finite_UnI[OF finite_N named_vars_finite])
  let ?v = "\<lambda>\<tau>. SOME n. G n = \<tau> \<and> n \<notin> ?K"
  have choices: "G (?v \<tau>) = \<tau> \<and> ?v \<tau> \<notin> ?K" for \<tau>
    by (rule someI_ex, rule sg_rich_fresh[OF rich finite_K])
  have stock: "G (?v \<tau>) = \<tau>" for \<tau> by (rule conjunct1[OF choices])
  have avoids: "?v \<tau> \<notin> N" for \<tau> using choices[of \<tau>] by blast
  have x_fresh: "?v \<sigma> \<notin> named_vars F" using choices[of \<sigma>] by blast
  have retracted: "book_theory_derivable \<Sigma> G (image (named_retract \<Sigma> ?v) S)
    (named_retract \<Sigma> ?v ?A)"
    by (rule book_theory_retraction_support_apply[OF support stock avoids])
  have predicate_names: "named_in_signature \<Sigma> F"
    by (rule book_language_signature[OF predicate])
  have fixed_predicate: "named_retract \<Sigma> ?v F = F"
    by (rule named_retract_fixed[OF predicate_names])
  have fixed_premise: "named_retract \<Sigma> ?v B = B" if "B \<in> S" for B
    by (rule named_retract_fixed[OF premise_names[OF that]])
  have fixed_set: "image (named_retract \<Sigma> ?v) S = S" using fixed_premise by auto
  have endpoint: "named_retract \<Sigma> ?v ?A = book_not G (NApp F (NVar (?v \<sigma>)))"
    by (simp only: book_retract_not named_retract.simps fixed_predicate fresh if_False)
  have result: "book_theory_derivable \<Sigma> G S (book_not G (NApp F (NVar (?v \<sigma>))))"
    using retracted by (simp only: fixed_set endpoint)
  show ?thesis by (rule exI[where x="?v \<sigma>"],
    rule conjI[OF stock conjI[OF x_fresh result]])
qed

corollary book_theory_fresh_constant_variable_instance:
  assumes rich: "sg_rich G"
    and fresh: "c \<notin> \<Sigma> \<sigma>"
    and premise_names: "\<And>A. A \<in> S \<Longrightarrow> named_in_signature \<Sigma> A"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and derivation: "book_theory_derivable (book_add_constant \<Sigma> c \<sigma>) G S
      (book_not G (NApp F (NConst c \<sigma>)))"
  shows "\<exists>x. G x = \<sigma> \<and> x \<notin> named_vars F \<and>
    book_theory_derivable \<Sigma> G S (book_not G (NApp F (NVar x)))"
  by (rule book_theory_fresh_constant_retraction[where G=G and \<Sigma>=\<Sigma> and \<sigma>=\<sigma>
        and c=c and F=F, OF rich fresh premise_names predicate derivation])

section \<open>Generalizing the recovered instance in the old signature\<close>

text \<open>
  The recovered S ⊢Σ ¬Fx yields S ⊢Σ ∀x.¬Fx by the already
  derived theory generalization rule. This is still a statement about
  global theory premises. It neither changes Gen's printed side condition
  nor asserts a local fixed-assignment rule.
\<close>

theorem book_theory_fresh_constant_generalization:
  assumes rich: "sg_rich G"
    and fresh: "c \<notin> \<Sigma> \<sigma>"
    and premise_names: "\<And>A. A \<in> S \<Longrightarrow> named_in_signature \<Sigma> A"
    and predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and derivation: "book_theory_derivable (book_add_constant \<Sigma> c \<sigma>) G S
      (book_not G (NApp F (NConst c \<sigma>)))"
  shows "\<exists>x. G x = \<sigma> \<and> x \<notin> named_vars F \<and>
    book_theory_derivable \<Sigma> G S (book_all G x (book_not G (NApp F (NVar x))))"
proof -
  obtain x where xtype: "G x = \<sigma>" and xfresh: "x \<notin> named_vars F"
    and variable_instance: "book_theory_derivable \<Sigma> G S (book_not G (NApp F (NVar x)))"
    using book_theory_fresh_constant_variable_instance[where G=G and \<Sigma>=\<Sigma> and \<sigma>=\<sigma>
      and c=c and F=F,
      OF rich fresh premise_names predicate derivation] by blast
  have generalized: "book_theory_derivable \<Sigma> G S
    (book_all G x (book_not G (NApp F (NVar x))))"
    by (rule book_theory_generalize[OF rich variable_instance])
  show ?thesis by (rule exI[where x=x], rule conjI[OF xtype conjI[OF xfresh generalized]])
qed

end
