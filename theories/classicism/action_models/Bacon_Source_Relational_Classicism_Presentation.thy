theory Bacon_Source_Relational_Classicism_Presentation
  imports Bacon_Source_Relational_Equivalence_Presentation
begin

section \<open>Classicism from the source Logical Equivalence axiom schema\<close>

text \<open>
  Logical Equivalence: (λv⃗.P)=(λv⃗.Q) whenever ⊢H P↔Q.
  Bacon–Dorr §1.3, p.12, DEFINES Classicism C as the smallest
  H-theory containing these instances. H-theories also retain MP,
  Gen and Inst (p.7); these rules must apply to formulas newly
  obtained with the extra axioms, not only to original H theorems.

  The inductive judgment below therefore has H inclusion, the
  H-certified Logical Equivalence axiom, MP, Gen and Inst. The axiom
  certificate is paper_R_named_H, NEVER the recursive C judgment.
  Both bodies are R formulas and every prefix type belongs to R.
  The literal named λ prefix is outermost-first; it may be empty
  and need not bind all free variables. Repeated raw binders retain
  shadowing. No duplicate-variable ζ rule is included.

  This is the native default-R source-definition presentation, not
  an alias for semantic validity, the F development, or the Boolean
  and Classicist identities of Figures 3–4. We prove only its
  embedding into H closed under the general Equivalence rule (p.14).
  The reverse inclusion is proved in Classicism_Equivalence_Iff using
  the independent native A.2–A.3 derivation. The Figures 3–4
  presentation theorem remains a separate correspondence obligation.
  No category existence or semantic completeness follows here.
\<close>

inductive paper_R_classicism_proves ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  H: "paper_R_named_H \<Sigma> G A \<Longrightarrow> paper_R_classicism_proves \<Sigma> G A"
| Logical_Equivalence: "paper_R_named_H \<Sigma> G (named_paper_iff G P Q) \<Longrightarrow>
    paper_R_in_language \<Sigma> G P Prop \<Longrightarrow> paper_R_in_language \<Sigma> G Q Prop \<Longrightarrow>
    list_all paper_R_type (map G ns) \<Longrightarrow>
    paper_R_classicism_proves \<Sigma> G
      (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q))"
| MP: "paper_R_classicism_proves \<Sigma> G A \<Longrightarrow>
    paper_R_classicism_proves \<Sigma> G (named_paper_imp G A B) \<Longrightarrow>
    paper_R_in_language \<Sigma> G B Prop \<Longrightarrow> paper_R_classicism_proves \<Sigma> G B"
| Gen: "paper_R_classicism_proves \<Sigma> G (named_paper_imp G P Q) \<Longrightarrow>
    G n = \<sigma> \<Longrightarrow> n \<notin> named_fv P \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))) Prop \<Longrightarrow>
    paper_R_classicism_proves \<Sigma> G (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)))"
| Inst: "paper_R_classicism_proves \<Sigma> G (named_paper_imp G P Q) \<Longrightarrow>
    G n = \<sigma> \<Longrightarrow> n \<notin> named_fv Q \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop \<Longrightarrow>
    paper_R_classicism_proves \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q)"

theorem paper_R_classicism_proves_language:
  assumes derivation: "paper_R_classicism_proves \<Sigma> G A"
  shows "paper_R_in_language \<Sigma> G A Prop"
  using derivation
proof (induction rule: paper_R_classicism_proves.induct)
  case H
  show ?case by (rule paper_R_named_H_language[OF H.hyps])
next
  case Logical_Equivalence
  show ?case by (rule paper_R_equivalence_vector_language[OF Logical_Equivalence.hyps(2,3,4)])
next
  case MP
  show ?case by (rule MP.hyps(3))
next
  case Gen
  show ?case by (rule Gen.hyps(4))
next
  case Inst
  show ?case by (rule Inst.hyps(4))
qed

theorem paper_R_classicism_into_equivalence:
  assumes derivation: "paper_R_classicism_proves \<Sigma> G A"
  shows "paper_R_equivalence_proves \<Sigma> G A"
  using derivation
proof (induction rule: paper_R_classicism_proves.induct)
  case H
  show ?case by (rule paper_R_equivalence_proves.H[OF H.hyps])
next
  case Logical_Equivalence
  show ?case by (rule paper_R_equivalence_proves.Equivalence[
    OF paper_R_equivalence_proves.H[OF Logical_Equivalence.hyps(1)]
      Logical_Equivalence.hyps(2,3,4)])
next
  case MP
  show ?case by (rule paper_R_equivalence_proves.MP[OF MP.IH MP.hyps(3)])
next
  case Gen
  show ?case by (rule paper_R_equivalence_proves.Gen[OF Gen.IH Gen.hyps(2,3,4)])
next
  case Inst
  show ?case by (rule paper_R_equivalence_proves.Inst[OF Inst.IH Inst.hyps(2,3,4)])
qed

end
