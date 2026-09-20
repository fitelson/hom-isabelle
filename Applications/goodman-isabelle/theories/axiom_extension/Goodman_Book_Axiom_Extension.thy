theory Goodman_Book_Axiom_Extension
  imports
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Classicism_Theory_Rules
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Classicism_Necessitation
begin

section \<open>An axiom extension in the book's source language\<close>

text \<open>
  Write C+[T] ⊢ A for the candidate extension below. Unlike ordinary
  consequence from premises T, PE may use theorems that depend on the
  added axioms. The definition extends the core's full-F minimal C
  (Bacon §8.1 and endnote 5), not the earlier constructor syntax.
  The identification with Goodman's old CEV+ is a separate open task.
\<close>

inductive goodman_book_proves ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext and T :: "'c book_named_term set" where
  Axiom: "A \<in> T \<Longrightarrow> book_theory_formula \<Sigma> G A \<Longrightarrow> goodman_book_proves \<Sigma> G T A"
| Base: "book_full_C_proves \<Sigma> G A \<Longrightarrow> goodman_book_proves \<Sigma> G T A"
| MP: "goodman_book_proves \<Sigma> G T A \<Longrightarrow>
    goodman_book_proves \<Sigma> G T (book_imp A B) \<Longrightarrow>
    book_theory_formula \<Sigma> G B \<Longrightarrow> goodman_book_proves \<Sigma> G T B"
| Gen: "goodman_book_proves \<Sigma> G T (book_imp A B) \<Longrightarrow>
    book_theory_formula \<Sigma> G A \<Longrightarrow> book_theory_formula \<Sigma> G B \<Longrightarrow>
    n \<notin> named_fv A \<Longrightarrow> goodman_book_proves \<Sigma> G T (book_imp A (book_all G n B))"
| PE: "goodman_book_proves \<Sigma> G T (book_iff G P Q) \<Longrightarrow>
    book_theory_formula \<Sigma> G P \<Longrightarrow> book_theory_formula \<Sigma> G Q \<Longrightarrow>
    goodman_book_proves \<Sigma> G T (book_leibniz G Prop P Q)"

lemma goodman_book_proves_language:
  assumes rich: "sg_rich G" and derivation: "goodman_book_proves \<Sigma> G T A"
  shows "book_theory_formula \<Sigma> G A"
  using derivation
proof (induction rule: goodman_book_proves.induct)
  case Axiom
  show ?case by (rule Axiom.hyps(2))
next
  case Base
  show ?case by (rule book_full_C_proves_language[OF rich Base.hyps])
next
  case MP
  show ?case by (rule MP.hyps(3))
next
  case Gen
  show ?case by (rule book_imp_language[OF Gen.hyps(2) book_all_language[OF Gen.hyps(3)]])
next
  case PE
  show ?case by (rule book_leibniz_language[OF rich PE.hyps(2,3)])
qed

theorem goodman_book_empty_iff:
  "goodman_book_proves \<Sigma> G {} A \<longleftrightarrow> book_full_C_proves \<Sigma> G A"
proof
  assume derivation: "goodman_book_proves \<Sigma> G {} A"
  then show "book_full_C_proves \<Sigma> G A"
    by (induction rule: goodman_book_proves.induct)
      (auto intro: book_full_C_proves.MP book_full_C_proves.Gen book_full_C_proves.PE)
next
  assume "book_full_C_proves \<Sigma> G A"
  then show "goodman_book_proves \<Sigma> G {} A" by (rule goodman_book_proves.Base)
qed

lemma goodman_book_cut:
  assumes derivation: "goodman_book_proves \<Sigma> G T A"
    and support: "\<And>B. B \<in> T \<Longrightarrow> goodman_book_proves \<Sigma> G U B"
  shows "goodman_book_proves \<Sigma> G U A"
  using derivation
  by (induction rule: goodman_book_proves.induct)
    (auto intro: support goodman_book_proves.intros)

lemma goodman_book_mono:
  assumes derivation: "goodman_book_proves \<Sigma> G T A" and subset: "T \<subseteq> U"
  shows "goodman_book_proves \<Sigma> G U A"
  using derivation
  by (induction rule: goodman_book_proves.induct)
    (auto intro: goodman_book_proves.intros dest: subsetD[OF subset])

theorem goodman_book_necessitation:
  assumes rich: "sg_rich G" and derivation: "goodman_book_proves \<Sigma> G T P"
  shows "goodman_book_proves \<Sigma> G T (book_box G P)"
proof -
  have pl: "book_theory_formula \<Sigma> G P" by (rule goodman_book_proves_language[OF rich derivation])
  have tl: "book_theory_formula \<Sigma> G (book_top G)" by (rule book_top_language[OF rich])
  have il: "book_theory_formula \<Sigma> G (book_iff G P (book_top G))"
    by (rule book_iff_language[OF rich pl tl])
  have implication: "goodman_book_proves \<Sigma> G T (book_imp P (book_iff G P (book_top G)))"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H, rule book_H_imp_iff_top[OF rich pl])
  have equivalent: "goodman_book_proves \<Sigma> G T (book_iff G P (book_top G))"
    by (rule goodman_book_proves.MP[OF derivation implication il])
  have identity: "goodman_book_proves \<Sigma> G T (book_leibniz G Prop P (book_top G))"
    by (rule goodman_book_proves.PE[OF equivalent pl tl])
  have fold: "goodman_book_proves \<Sigma> G T
      (book_imp (book_leibniz G Prop P (book_top G)) (book_box G P))"
    by (rule goodman_book_proves.Base, rule book_full_C_proves.H,
      rule book_H_box_fold_unfold(1)[OF rich pl])
  show ?thesis by (rule goodman_book_proves.MP[OF identity fold book_box_language[OF rich pl]])
qed

corollary goodman_book_added_axiom_necessitation:
  "sg_rich G \<Longrightarrow> A \<in> T \<Longrightarrow> book_theory_formula \<Sigma> G A \<Longrightarrow>
    goodman_book_proves \<Sigma> G T (book_box G A)"
  by (rule goodman_book_necessitation; (assumption | rule goodman_book_proves.Axiom); assumption)

end
