theory Goodman_Book_Vector_Extension
  imports Goodman_Propositional_Equivalence_Bridge
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Vector_Equivalence
begin

section \<open>Generalization and MF above added axioms\<close>

lemma gi_goodman_generalize:
  assumes rich: "sg_rich G" and derivation: "goodman_book_proves \<Sigma> G T A"
  shows "goodman_book_proves \<Sigma> G T (book_all G n A)"
proof -
  have al: "book_theory_formula \<Sigma> G A" by (rule goodman_book_proves_language[OF rich derivation])
  have base: "book_theory_derivable \<Sigma> G {A} A"
    by (rule book_theory_derivable.Assumption; (simp | rule al))
  have quantified: "book_theory_derivable \<Sigma> G {A} (book_all G n A)"
    by (rule book_theory_generalize[OF rich base])
  show ?thesis by (rule goodman_book_contains_theory_derivation[OF rich quantified]; simp add: derivation)
qed

theorem gi_goodman_function_identity_rule:
  assumes rich: "sg_rich G"
    and fl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr (G n) \<tau>)"
    and hl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G H (Arr (G n) \<tau>)"
    and nf: "n \<notin> named_fv F" and nh: "n \<notin> named_fv H"
    and pointwise: "goodman_book_proves \<Sigma> G T
      (book_leibniz G \<tau> (NApp F (NVar n)) (NApp H (NVar n)))"
  shows "goodman_book_proves \<Sigma> G T (book_leibniz G (Arr (G n) \<tau>) F H)"
proof -
  have quantified: "goodman_book_proves \<Sigma> G T
    (book_all G n (book_leibniz G \<tau> (NApp F (NVar n)) (NApp H (NVar n))))"
    by (rule gi_goodman_generalize[OF rich pointwise])
  have necessary: "goodman_book_proves \<Sigma> G T
    (book_box G (book_all G n (book_leibniz G \<tau> (NApp F (NVar n)) (NApp H (NVar n)))))"
    by (rule goodman_book_necessitation[OF rich quantified])
  have condition: "goodman_book_proves \<Sigma> G T (book_MF_condition G (G n) \<tau> n F H)"
    by (rule goodman_book_proves.Base, rule book_full_C_MF_instance[OF rich refl fl hl nf nh])
  show ?thesis using condition unfolding book_MF_condition_def
    by (rule goodman_book_proves.MP[OF necessary _ book_leibniz_language[OF rich fl hl]])
qed

section \<open>Native vector Equivalence remains admissible in C+[T]\<close>

text \<open>
  This proof adapts the core's book_full_C_vector_equivalence induction:
  zero arguments use PE, and each further argument uses MF after
  generalization and necessitation. The additional stock T remains fixed.
  No validity or consistency assumption about T is introduced.
\<close>

theorem gi_goodman_vector_equivalence:
  assumes rich: "sg_rich G" and instance_ok: "book_equivalence_rule_instance \<Sigma> G ns R S"
    and premise: "goodman_book_proves \<Sigma> G T (book_iff G (book_vector_application R ns) (book_vector_application S ns))"
  shows "goodman_book_proves \<Sigma> G T (book_leibniz G (foldr Arr (map G ns) Prop) R S)"
  using instance_ok premise
proof (induction ns arbitrary: R S)
  case Nil
  have rl: "book_theory_formula \<Sigma> G R" and sl: "book_theory_formula \<Sigma> G S"
    using Nil.prems(1) unfolding book_equivalence_rule_instance_def by simp_all
  have equivalent: "goodman_book_proves \<Sigma> G T (book_iff G R S)"
    using Nil.prems(2) by (simp only: book_vector_application_def list.map foldl.simps)
  have identity: "goodman_book_proves \<Sigma> G T (book_leibniz G Prop R S)"
    by (rule goodman_book_proves.PE[OF equivalent rl sl])
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
  have tail_premise: "goodman_book_proves \<Sigma> G T (book_iff G (book_vector_application ?R ns) (book_vector_application ?S ns))"
    using Cons.prems(2) by (simp only: book_vector_application_def list.map foldl.simps)
  have pointwise: "goodman_book_proves \<Sigma> G T (book_leibniz G ?\<tau> ?R ?S)"
    by (rule Cons.IH[OF tail_instance tail_premise])
  have nr: "n \<notin> named_fv R" and ns: "n \<notin> named_fv S" using fresh by auto
  have identity: "goodman_book_proves \<Sigma> G T (book_leibniz G (Arr (G n) ?\<tau>) R S)"
    by (rule gi_goodman_function_identity_rule[OF rich rl sl nr ns pointwise])
  show ?case using identity by simp
qed


text \<open>
  This is the book's native vector rule for the axiom extension. The
  separate translation of the old ascending de Bruijn application order
  and zeta_body is still required. Native admissibility alone is not a
  whole-proof CEV+ correspondence or a T6 transfer.
\<close>

end
