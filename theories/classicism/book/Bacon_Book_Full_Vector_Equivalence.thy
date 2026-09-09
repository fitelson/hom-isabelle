theory Bacon_Book_Full_Vector_Equivalence
  imports Bacon_Book_Full_MF_Instances
begin

section \<open>Recovering vector Equivalence from all-type MF and PE\<close>

theorem book_full_C_vector_equivalence:
  assumes rich: "sg_rich G" and instance_ok: "book_equivalence_rule_instance \<Sigma> G ns R S"
    and premise: "book_full_C_proves \<Sigma> G (book_iff G (book_vector_application R ns) (book_vector_application S ns))"
  shows "book_full_C_proves \<Sigma> G (book_leibniz G (foldr Arr (map G ns) Prop) R S)"
  using instance_ok premise
proof (induction ns arbitrary: R S)
  case Nil
  have rl: "book_theory_formula \<Sigma> G R" and sl: "book_theory_formula \<Sigma> G S"
    using Nil.prems(1) unfolding book_equivalence_rule_instance_def by simp_all
  have equivalent: "book_full_C_proves \<Sigma> G (book_iff G R S)"
    using Nil.prems(2) by (simp only: book_vector_application_def list.map foldl.simps)
  have identity: "book_full_C_proves \<Sigma> G (book_leibniz G Prop R S)"
    by (rule book_full_C_proves.PE[OF equivalent rl sl])
  show ?case using identity by simp
next
  case (Cons n ns)
  let ?\<tau> = "foldr Arr (map G ns) Prop"
  let ?R = "NApp R (NVar n)"
  let ?S = "NApp S (NVar n)"
  have distinct: "distinct (n#ns)" and fresh: "set (n#ns) \<inter> (named_fv R \<union> named_fv S) = {}"
    and rl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G R (Arr (G n) ?\<tau>)"
    and sl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G S (Arr (G n) ?\<tau>)"
    using Cons.prems(1) unfolding book_equivalence_rule_instance_def by auto
  have nl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NVar n) (G n)" by (rule book_language_Var)
  have rapp: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?R ?\<tau>" by (rule book_language_App[OF rl nl])
  have sapp: "book_in_language book_minimal_logical_type UNIV \<Sigma> G ?S ?\<tau>" by (rule book_language_App[OF sl nl])
  have tail_distinct: "distinct ns" using distinct by simp
  have tail_fresh: "set ns \<inter> (named_fv ?R \<union> named_fv ?S) = {}" using distinct fresh by auto
  have tail_instance: "book_equivalence_rule_instance \<Sigma> G ns ?R ?S"
    unfolding book_equivalence_rule_instance_def by (rule conjI[OF tail_distinct conjI[OF tail_fresh conjI[OF rapp sapp]]])
  have tail_premise: "book_full_C_proves \<Sigma> G (book_iff G (book_vector_application ?R ns) (book_vector_application ?S ns))"
    using Cons.prems(2) by (simp only: book_vector_application_def list.map foldl.simps)
  have pointwise: "book_full_C_proves \<Sigma> G (book_leibniz G ?\<tau> ?R ?S)"
    by (rule Cons.IH[OF tail_instance tail_premise])
  have nr: "n \<notin> named_fv R" and ns: "n \<notin> named_fv S" using fresh by auto
  have identity: "book_full_C_proves \<Sigma> G (book_leibniz G (Arr (G n) ?\<tau>) R S)"
    by (rule book_full_C_function_identity_rule[OF rich rl sl nr ns pointwise])
  show ?case using identity by simp
qed

theorem book_C_base_embeds_full:
  assumes rich: "sg_rich G" and derivation: "book_C_proves \<Sigma> G A"
  shows "book_full_C_proves \<Sigma> G A"
  using derivation
proof (induction rule: book_C_proves.induct)
  case H
  show ?case by (rule book_full_C_proves.H[OF H.hyps])
next
  case MP
  show ?case by (rule book_full_C_proves.MP[OF MP.IH MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_full_C_proves.Gen[OF Gen.IH Gen.hyps(2,3,4)])
next
  case Equivalence
  show ?case by (rule book_full_C_vector_equivalence[OF rich Equivalence.hyps(2) Equivalence.IH])
qed

text \<open>
  The empty vector uses PE. Removing one argument uses the induction
  hypothesis for the applied heads, then the derived function-identity
  rule. Every removed variable is fresh for those heads; the tail's
  freshness additionally uses distinctness of the entire vector.
  Thus all four constructors of the retained Equivalence base translate
  into the independent MF+PE calculus. This is proof preservation, not
  a converse or preservation of consistency when MF is added.
\<close>

end
