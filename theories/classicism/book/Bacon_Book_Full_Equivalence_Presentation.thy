theory Bacon_Book_Full_Equivalence_Presentation
  imports Bacon_Book_Full_Vector_Equivalence
begin

section \<open>MF plus vector Equivalence is the same full theory\<close>

inductive book_full_C_vector_proves :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  H: "book_H \<Sigma> G A \<Longrightarrow> book_full_C_vector_proves \<Sigma> G A"
| MF: "book_full_C_vector_proves \<Sigma> G (book_MF_axiom G \<sigma> \<tau>)"
| MP: "book_full_C_vector_proves \<Sigma> G A \<Longrightarrow> book_full_C_vector_proves \<Sigma> G (book_imp A B) \<Longrightarrow>
    book_theory_formula \<Sigma> G B \<Longrightarrow> book_full_C_vector_proves \<Sigma> G B"
| Gen: "book_full_C_vector_proves \<Sigma> G (book_imp A B) \<Longrightarrow>
    book_theory_formula \<Sigma> G A \<Longrightarrow> book_theory_formula \<Sigma> G B \<Longrightarrow>
    n \<notin> named_fv A \<Longrightarrow> book_full_C_vector_proves \<Sigma> G (book_imp A (book_all G n B))"
| Equivalence: "book_full_C_vector_proves \<Sigma> G (book_iff G (book_vector_application R ns) (book_vector_application S ns)) \<Longrightarrow>
    book_equivalence_rule_instance \<Sigma> G ns R S \<Longrightarrow>
    book_full_C_vector_proves \<Sigma> G (book_leibniz G (foldr Arr (map G ns) Prop) R S)"

lemma book_full_C_vector_to_PE:
  assumes rich: "sg_rich G" and derivation: "book_full_C_vector_proves \<Sigma> G A"
  shows "book_full_C_proves \<Sigma> G A"
  using derivation
proof (induction rule: book_full_C_vector_proves.induct)
  case H
  show ?case by (rule book_full_C_proves.H[OF H.hyps])
next
  case MF
  show ?case by (rule book_full_C_proves.MF)
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

lemma book_full_C_PE_to_vector:
  assumes derivation: "book_full_C_proves \<Sigma> G A"
  shows "book_full_C_vector_proves \<Sigma> G A"
  using derivation
proof (induction rule: book_full_C_proves.induct)
  case H
  show ?case by (rule book_full_C_vector_proves.H[OF H.hyps])
next
  case MF
  show ?case by (rule book_full_C_vector_proves.MF)
next
  case MP
  show ?case by (rule book_full_C_vector_proves.MP[OF MP.IH MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_full_C_vector_proves.Gen[OF Gen.IH Gen.hyps(2,3,4)])
next
  case (PE P Q)
  have instance_ok: "book_equivalence_rule_instance \<Sigma> G [] P Q"
    using PE.hyps(2,3) by (simp add: book_equivalence_rule_instance_def)
  have premise: "book_full_C_vector_proves \<Sigma> G (book_iff G (book_vector_application P []) (book_vector_application Q []))"
    using PE.IH by (simp add: book_vector_application_def)
  have result: "book_full_C_vector_proves \<Sigma> G (book_leibniz G (foldr Arr (map G []) Prop) P Q)"
    by (rule book_full_C_vector_proves.Equivalence[OF premise instance_ok])
  show ?case using result by simp
qed

theorem book_full_C_presentations_iff:
  assumes rich: "sg_rich G"
  shows "book_full_C_vector_proves \<Sigma> G A \<longleftrightarrow> book_full_C_proves \<Sigma> G A"
  by (rule iffI; (rule book_full_C_vector_to_PE[OF rich] | rule book_full_C_PE_to_vector); assumption)

text \<open>
  The source MF+PE presentation and the independently declared
  MF+vector-Equivalence presentation have exactly the same proofs.
  One direction uses the proved recovery of vector Equivalence; the
  reverse uses its empty-vector instance. This does not identify the
  older Equivalence-only base with the full theory: MF remains an
  explicit axiom family in both presentations here.
\<close>

end
