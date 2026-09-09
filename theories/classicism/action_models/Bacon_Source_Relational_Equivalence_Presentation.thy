theory Bacon_Source_Relational_Equivalence_Presentation
  imports Bacon_Source_Relational_H Bacon_Source_Relational_Binder_Vectors
begin

section \<open>An independent R presentation closed under Equivalence\<close>

text \<open>
  Equivalence: from ⊢P↔Q infer ⊢(λv⃗.P)=(λv⃗.Q).
  Source: Bacon–Dorr p.14, with λv⃗=λv₁.…λvₙ and n≥0
  from p.9. The empty vector is Propositional Equivalence (p.15).
  Bodies may be open, and the prefix need not include all their free
  variables. We retain ordinary shadowing for repeated raw binders;
  no corresponding duplicate-variable ζ rule is asserted.

  The independent judgment contains Hᴿ and is closed under MP, Gen,
  Inst and Equivalence. Gen and Inst apply also to newly obtained
  formulas: merely adding H inclusion and MP would not supply the
  source's H-theory closure. Every body and intermediate formula is
  R-typed in the unchanged signature and stock. Defined implication
  and biconditional remain literal named λ terms.

  This is a proof-rule presentation, not semantic validity and not
  an alias for the existing F or axiom-based C judgment. No α,
  Existence or Classicist-identity constructor is added. Equality
  with the printed identity-axiom presentation remains to be proved.
\<close>

lemma paper_R_equivalence_identity_language:
  assumes left: "paper_R_in_language \<Sigma> G A \<tau>"
    and right: "paper_R_in_language \<Sigma> G B \<tau>"
  shows "paper_R_in_language \<Sigma> G (named_paper_eq \<tau> A B) Prop"
proof -
  have rt: "paper_R_type \<tau>" by (rule paper_R_language_result_type[OF left])
  have er: "paper_R_type (paper_logical_type (SEq \<tau>))" using rt by simp
  have et: "paper_R_has_type G (NLogical (SEq \<tau>)) (Arr \<tau> (Arr \<tau> Prop))"
    using paper_R_has_type.Logical[where G=G and l="SEq \<tau>", OF er] by simp
  have el: "paper_R_in_language \<Sigma> G (NLogical (SEq \<tau>)) (Arr \<tau> (Arr \<tau> Prop))"
    unfolding paper_R_in_language_def by (rule conjI[OF et]; simp)
  show ?thesis unfolding named_paper_eq_def
    by (rule paper_R_language_App[OF paper_R_language_App[OF el left] right])
qed

lemma paper_R_equivalence_vector_language:
  assumes left: "paper_R_in_language \<Sigma> G P Prop"
    and right: "paper_R_in_language \<Sigma> G Q Prop"
    and binders: "list_all paper_R_type (map G ns)"
  shows "paper_R_in_language \<Sigma> G
    (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q)) Prop"
  by (rule paper_R_equivalence_identity_language[
    OF paper_R_named_lam_vec_prop_language[OF left binders]
      paper_R_named_lam_vec_prop_language[OF right binders]])

inductive paper_R_equivalence_proves ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  H: "paper_R_named_H \<Sigma> G A \<Longrightarrow> paper_R_equivalence_proves \<Sigma> G A"
| MP: "paper_R_equivalence_proves \<Sigma> G A \<Longrightarrow>
    paper_R_equivalence_proves \<Sigma> G (named_paper_imp G A B) \<Longrightarrow>
    paper_R_in_language \<Sigma> G B Prop \<Longrightarrow> paper_R_equivalence_proves \<Sigma> G B"
| Gen: "paper_R_equivalence_proves \<Sigma> G (named_paper_imp G P Q) \<Longrightarrow>
    G n = \<sigma> \<Longrightarrow> n \<notin> named_fv P \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q))) Prop \<Longrightarrow>
    paper_R_equivalence_proves \<Sigma> G (named_paper_imp G P (named_paper_all \<sigma> (NLam n Q)))"
| Inst: "paper_R_equivalence_proves \<Sigma> G (named_paper_imp G P Q) \<Longrightarrow>
    G n = \<sigma> \<Longrightarrow> n \<notin> named_fv Q \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q) Prop \<Longrightarrow>
    paper_R_equivalence_proves \<Sigma> G (named_paper_imp G (named_paper_ex \<sigma> (NLam n P)) Q)"
| Equivalence: "paper_R_equivalence_proves \<Sigma> G (named_paper_iff G P Q) \<Longrightarrow>
    paper_R_in_language \<Sigma> G P Prop \<Longrightarrow> paper_R_in_language \<Sigma> G Q Prop \<Longrightarrow>
    list_all paper_R_type (map G ns) \<Longrightarrow>
    paper_R_equivalence_proves \<Sigma> G
      (named_paper_eq (paper_type_vector (map G ns) Prop) (named_lam_vec ns P) (named_lam_vec ns Q))"

theorem paper_R_equivalence_proves_language:
  assumes derivation: "paper_R_equivalence_proves \<Sigma> G A"
  shows "paper_R_in_language \<Sigma> G A Prop"
  using derivation
proof (induction rule: paper_R_equivalence_proves.induct)
  case H
  show ?case by (rule paper_R_named_H_language[OF H.hyps])
next
  case MP
  show ?case by (rule MP.hyps(3))
next
  case Gen
  show ?case by (rule Gen.hyps(4))
next
  case Inst
  show ?case by (rule Inst.hyps(4))
next
  case Equivalence
  show ?case by (rule paper_R_equivalence_vector_language[OF Equivalence.hyps(2,3,4)])
qed

lemma paper_R_equivalence_propositional:
  assumes derivation: "paper_R_equivalence_proves \<Sigma> G (named_paper_iff G P Q)"
    and left: "paper_R_in_language \<Sigma> G P Prop" and right: "paper_R_in_language \<Sigma> G Q Prop"
  shows "paper_R_equivalence_proves \<Sigma> G (named_paper_eq Prop P Q)"
proof -
  have binders: "list_all paper_R_type (map G [])" by simp
  have result: "paper_R_equivalence_proves \<Sigma> G
      (named_paper_eq (paper_type_vector (map G []) Prop) (named_lam_vec [] P) (named_lam_vec [] Q))"
    by (rule paper_R_equivalence_proves.Equivalence[OF derivation left right binders])
  show ?thesis using result by simp
qed

end
