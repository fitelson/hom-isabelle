theory Bacon_Source_Relational_Binder_Vectors
  imports Bacon_Source_Relational_Vector_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Vectors
begin

section \<open>R-typed binder vectors in source order\<close>

text \<open>
  λn₁…nₖ.A has type G(n₁)→⋯→G(nₖ)→τ when A:τ,
  each binder type is in R, and τ≠e. Source: Bacon–Dorr §1.1,
  p.5, and the λ convention of Figure 1, p.6.

  We reuse the literal named_lam_vec fold, whose first name is the
  outermost binder. Repeated names are permitted and retain their
  ordinary shadowing meaning. There is no reversal or distinct-name
  assumption. The type proof uses the independent R judgment, not
  the existing F typing theorem. For an empty vector the raw fold
  is A; the nonindividual-result guard concerns this general R
  abstraction theorem and is automatic for propositional bodies.
\<close>

lemma paper_type_vector_nonindividual_result:
  assumes result: "\<tau> \<noteq> Ind"
  shows "paper_type_vector \<sigma>s \<tau> \<noteq> Ind"
  using result by (cases \<sigma>s) simp_all

lemma paper_R_named_lam_vec_type:
  assumes body: "paper_R_has_type G A \<tau>"
    and binders: "list_all paper_R_type (map G ns)" and result: "\<tau> \<noteq> Ind"
  shows "paper_R_has_type G (named_lam_vec ns A) (paper_type_vector (map G ns) \<tau>)"
  using binders
proof (induction ns)
  case Nil
  show ?case by (simp only: named_lam_vec.simps list.map paper_type_vector.simps; rule body)
next
  case (Cons n ns)
  have nt: "paper_R_type (G n)" and tail: "list_all paper_R_type (map G ns)"
    using Cons.prems by simp_all
  have inner: "paper_R_has_type G (named_lam_vec ns A) (paper_type_vector (map G ns) \<tau>)"
    by (rule Cons.IH[OF tail])
  have tail_result: "paper_type_vector (map G ns) \<tau> \<noteq> Ind"
    by (rule paper_type_vector_nonindividual_result[OF result])
  have abstraction: "paper_R_has_type G (NLam n (named_lam_vec ns A))
    (Arr (G n) (paper_type_vector (map G ns) \<tau>))"
    by (rule paper_R_has_type.Lam[OF inner nt tail_result])
  show ?case by (simp only: named_lam_vec.simps list.map paper_type_vector.simps; rule abstraction)
qed

lemma paper_R_named_lam_vec_signature:
  "named_in_signature \<Sigma> (named_lam_vec ns A) \<longleftrightarrow> named_in_signature \<Sigma> A"
  by (induction ns) simp_all

theorem paper_R_named_lam_vec_language:
  assumes body: "paper_R_in_language \<Sigma> G A \<tau>"
    and binders: "list_all paper_R_type (map G ns)" and result: "\<tau> \<noteq> Ind"
  shows "paper_R_in_language \<Sigma> G (named_lam_vec ns A) (paper_type_vector (map G ns) \<tau>)"
proof -
  have typed: "paper_R_has_type G A \<tau>" and names: "named_in_signature \<Sigma> A"
    using body unfolding paper_R_in_language_def by blast+
  have abstraction: "paper_R_has_type G (named_lam_vec ns A) (paper_type_vector (map G ns) \<tau>)"
    by (rule paper_R_named_lam_vec_type[OF typed binders result])
  have signature: "named_in_signature \<Sigma> (named_lam_vec ns A)"
    by (rule iffD2[OF paper_R_named_lam_vec_signature names])
  show ?thesis unfolding paper_R_in_language_def by (rule conjI[OF abstraction signature])
qed

corollary paper_R_named_lam_vec_prop_language:
  assumes body: "paper_R_in_language \<Sigma> G A Prop" and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_in_language \<Sigma> G (named_lam_vec ns A) (paper_type_vector (map G ns) Prop)"
  by (rule paper_R_named_lam_vec_language[OF body binders]; simp)

lemma paper_R_named_lam_vec_fv:
  "named_fv (named_lam_vec ns A) = named_fv A - set ns"
  by (rule named_lam_vec_fv)

lemma paper_R_named_lam_vec_adequate_iff:
  "named_adequate g (named_lam_vec ns A) \<longleftrightarrow> named_fv A - set ns \<subseteq> dom g"
  by (simp only: named_adequate_def named_lam_vec_fv)

lemma paper_R_named_lam_vec_head_update:
  "named_adequate (g(n := Some a)) (named_lam_vec ns A) \<longleftrightarrow>
    named_adequate g (named_lam_vec (n#ns) A)"
  by (simp only: named_lam_vec.simps named_binder_update_adequate_iff)

end
