theory Bacon_Book_Classicism_Signature_Conservativity
  imports Bacon_Book_Classicism_Retraction
    Bacon_Book_Environment_Development.Bacon_Book_Theory_Signature_Monotonicity
begin

section \<open>Changing the declared signature without changing an old theorem\<close>

theorem book_C_foreign_constants_eliminate:
  assumes rich: "sg_rich G" and derivation: "book_C_proves \<Sigma> G A"
    and old_names: "named_in_signature \<Omega> A"
  shows "book_C_proves \<Omega> G A"
proof -
  obtain N where support: "book_C_retraction_support \<Omega> G A N"
    using book_C_retraction_support_exists[where \<Omega>=\<Omega>, OF rich derivation] by blast
  have finite: "finite N" using support unfolding book_C_retraction_support_def by blast
  let ?v = "\<lambda>\<tau>. SOME n. G n = \<tau> \<and> n \<notin> N"
  have chosen: "G (?v \<tau>) = \<tau> \<and> ?v \<tau> \<notin> N" for \<tau>
    by (rule someI_ex, rule sg_rich_fresh[OF rich finite])
  have stock: "\<And>\<tau>. G (?v \<tau>) = \<tau>" and avoids: "\<And>\<tau>. ?v \<tau> \<notin> N"
    using chosen by blast+
  have retracted: "book_C_proves \<Omega> G (named_retract \<Omega> ?v A)"
    by (rule book_C_retraction_apply[OF support stock avoids])
  show ?thesis using retracted by (simp only: named_retract_fixed[OF old_names])
qed

lemma book_C_equivalence_instance_signature_mono:
  assumes original: "book_equivalence_rule_instance \<Sigma> G ns R S"
    and inclusion: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> \<Omega> \<tau>"
  shows "book_equivalence_rule_instance \<Omega> G ns R S"
proof -
  have distinct: "distinct ns" and fresh: "set ns \<inter> (named_fv R \<union> named_fv S) = {}"
    and rl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G R (foldr Arr (map G ns) Prop)"
    and sl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G S (foldr Arr (map G ns) Prop)"
    using original unfolding book_equivalence_rule_instance_def by blast+
  show ?thesis unfolding book_equivalence_rule_instance_def
    by (rule conjI[OF distinct], rule conjI[OF fresh],
      rule conjI[OF book_language_signature_mono[OF rl inclusion] book_language_signature_mono[OF sl inclusion]])
qed

theorem book_C_signature_mono:
  assumes rich: "sg_rich G" and derivation: "book_C_proves \<Sigma> G A"
    and inclusion: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> \<Omega> \<tau>"
  shows "book_C_proves \<Omega> G A"
  using derivation
proof (induction rule: book_C_proves.induct)
  case (H A)
  have base: "book_theory_derivable \<Sigma> G {} A" using H.hyps by (simp only: book_H_iff_theory[OF rich])
  have enlarged: "book_theory_derivable \<Omega> G {} A" by (rule book_theory_signature_mono[OF base inclusion])
  show ?case by (rule book_C_from_empty_theory[OF rich enlarged])
next
  case MP
  show ?case by (rule book_C_proves.MP[OF MP.IH book_language_signature_mono[OF MP.hyps(3) inclusion]])
next
  case Gen
  show ?case by (rule book_C_proves.Gen[OF Gen.IH book_language_signature_mono[OF Gen.hyps(2) inclusion]
    book_language_signature_mono[OF Gen.hyps(3) inclusion] Gen.hyps(4)])
next
  case Equivalence
  show ?case by (rule book_C_proves.Equivalence[OF Equivalence.IH
    book_C_equivalence_instance_signature_mono[OF Equivalence.hyps(2) inclusion]])
qed

theorem book_C_signature_conservativity:
  assumes rich: "sg_rich G" and inclusion: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> \<Omega> \<tau>"
    and old_names: "named_in_signature \<Sigma> A"
  shows "book_C_proves \<Omega> G A \<longleftrightarrow> book_C_proves \<Sigma> G A"
proof
  assume enlarged: "book_C_proves \<Omega> G A"
  show "book_C_proves \<Sigma> G A"
    by (rule book_C_foreign_constants_eliminate[where \<Sigma>=\<Omega> and \<Omega>=\<Sigma>, OF rich enlarged old_names])
next
  assume original: "book_C_proves \<Sigma> G A"
  show "book_C_proves \<Omega> G A"
    by (rule book_C_signature_mono[where \<Sigma>=\<Sigma> and \<Omega>=\<Omega>, OF rich original inclusion])
qed

text \<open>
  This is theoremhood conservativity, not yet conservativity of an
  entire C-plus-assumptions proof under one common retraction. Such
  a proof uses only finitely many C theorems, but their separate fresh
  supports must be combined before choosing the retraction variables.
  Nor does this alone preserve a fresh-witness axiom when its witness
  constant is replaced. Those remain the next extension obligations.
\<close>

end
