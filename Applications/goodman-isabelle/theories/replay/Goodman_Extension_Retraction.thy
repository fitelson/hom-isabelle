theory Goodman_Extension_Retraction
  imports Goodman_Modal_Package_Preservation
    Bacon_Book_Classicism_Development.Bacon_Book_Full_Classicism_Signature_Conservativity
begin

section \<open>Finite fresh-variable support for a C+[T] proof\<close>

text \<open>
  A retraction leaves the target signature Ω fixed and replaces every
  foreign constant by a variable of its declared type. One finite set N
  protects the names used by the particular proof. We do not choose one
  set for all proofs or all axioms. The stock T remains fixed because
  every added axiom already belongs to the target language.
\<close>

definition gi_extension_retraction_support where
  "gi_extension_retraction_support \<Omega> G T A N \<longleftrightarrow>
    finite N \<and> named_vars A \<subseteq> N \<and>
    (\<forall>v. (\<forall>\<tau>. G (v \<tau>) = \<tau>) \<longrightarrow> (\<forall>\<tau>. v \<tau> \<notin> N) \<longrightarrow>
      goodman_book_proves \<Omega> G T (named_retract \<Omega> v A))"

lemma gi_extension_retraction_supportI:
  assumes finite: "finite N" and names: "named_vars A \<subseteq> N"
    and transform: "\<And>v. (\<And>\<tau>. G (v \<tau>) = \<tau>) \<Longrightarrow> (\<And>\<tau>. v \<tau> \<notin> N) \<Longrightarrow>
      goodman_book_proves \<Omega> G T (named_retract \<Omega> v A)"
  shows "gi_extension_retraction_support \<Omega> G T A N"
  using assms unfolding gi_extension_retraction_support_def by blast

lemma gi_extension_retraction_apply:
  assumes support: "gi_extension_retraction_support \<Omega> G T A N"
    and stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> N"
  shows "goodman_book_proves \<Omega> G T (named_retract \<Omega> v A)"
  using assms unfolding gi_extension_retraction_support_def by blast

theorem gi_extension_retraction_support_exists:
  assumes rich: "sg_rich G" and derivation: "goodman_book_proves \<Sigma> G T A"
    and old_axioms: "\<And>B. B \<in> T \<Longrightarrow> book_theory_formula \<Omega> G B"
  shows "\<exists>N. gi_extension_retraction_support \<Omega> G T A N"
  using derivation
proof (induction rule: goodman_book_proves.induct)
  case (Axiom A)
  have language: "book_theory_formula \<Omega> G A" by (rule old_axioms[OF Axiom.hyps(1)])
  show ?case
  proof (rule exI[where x="named_vars A"], rule gi_extension_retraction_supportI[OF named_vars_finite subset_refl])
    fix v assume "\<And>\<tau>. G (v \<tau>) = \<tau>" "\<And>\<tau>. v \<tau> \<notin> named_vars A"
    show "goodman_book_proves \<Omega> G T (named_retract \<Omega> v A)"
      by (simp only: named_retract_fixed[OF book_language_signature[OF language]];
        rule goodman_book_proves.Axiom[OF Axiom.hyps(1) language])
  qed
next
  case (Base A)
  obtain N where support: "book_full_C_retraction_support \<Omega> G A N"
    using book_full_C_retraction_support_exists[where \<Omega>=\<Omega>, OF rich Base.hyps] by blast
  have finite: "finite N" and names: "named_vars A \<subseteq> N"
    using support unfolding book_full_C_retraction_support_def by blast+
  show ?case
  proof (rule exI[where x=N], rule gi_extension_retraction_supportI[OF finite names])
    fix v assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> N"
    show "goodman_book_proves \<Omega> G T (named_retract \<Omega> v A)"
      by (rule goodman_book_proves.Base, rule book_full_C_retraction_apply[OF support stock fresh])
  qed
next
  case (MP A B)
  obtain N where first: "gi_extension_retraction_support \<Omega> G T A N" using MP.IH(1) by blast
  obtain K where second: "gi_extension_retraction_support \<Omega> G T (book_imp A B) K" using MP.IH(2) by blast
  let ?U = "N \<union> K \<union> named_vars B"
  have finite: "finite ?U" using first second unfolding gi_extension_retraction_support_def
    by (auto intro: named_vars_finite)
  show ?case
  proof (rule exI[where x="?U"], rule gi_extension_retraction_supportI[OF finite Un_upper2])
    fix v assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> ?U"
    have fn: "\<And>\<tau>. v \<tau> \<notin> N" and fk: "\<And>\<tau>. v \<tau> \<notin> K" using fresh by blast+
    have pa: "goodman_book_proves \<Omega> G T (named_retract \<Omega> v A)"
      by (rule gi_extension_retraction_apply[OF first stock fn])
    have pi: "goodman_book_proves \<Omega> G T (book_imp (named_retract \<Omega> v A) (named_retract \<Omega> v B))"
      using gi_extension_retraction_apply[OF second stock fk] by (simp only: book_retract_imp)
    show "goodman_book_proves \<Omega> G T (named_retract \<Omega> v B)"
      by (rule goodman_book_proves.MP[OF pa pi book_retract_language[OF MP.hyps(3) stock]])
  qed
next
  case (Gen A B n)
  obtain N where support: "gi_extension_retraction_support \<Omega> G T (book_imp A B) N" using Gen.IH by blast
  let ?C = "book_imp A (book_all G n B)"
  let ?U = "insert n (N \<union> named_vars ?C)"
  have finite: "finite ?U" using support unfolding gi_extension_retraction_support_def
    by (auto intro: named_vars_finite)
  have names: "named_vars ?C \<subseteq> ?U" by blast
  show ?case
  proof (rule exI[where x="?U"], rule gi_extension_retraction_supportI[OF finite names])
    fix v assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> ?U"
    have fn: "\<And>\<tau>. v \<tau> \<notin> N" and avoid: "\<And>\<tau>. v \<tau> \<noteq> n" using fresh by blast+
    have antecedent: "n \<notin> named_fv (named_retract \<Omega> v A)"
      by (rule named_retract_fresh[OF Gen.hyps(4) avoid])
    have premise: "goodman_book_proves \<Omega> G T (book_imp (named_retract \<Omega> v A) (named_retract \<Omega> v B))"
      using gi_extension_retraction_apply[OF support stock fn] by (simp only: book_retract_imp)
    show "goodman_book_proves \<Omega> G T (named_retract \<Omega> v ?C)"
      by (simp only: book_retract_imp book_retract_all; rule goodman_book_proves.Gen[OF premise
        book_retract_language[OF Gen.hyps(2) stock] book_retract_language[OF Gen.hyps(3) stock] antecedent])
  qed
next
  case (PE P Q)
  let ?C = "book_leibniz G Prop P Q"
  obtain N where support: "gi_extension_retraction_support \<Omega> G T (book_iff G P Q) N" using PE.IH by blast
  let ?U = "N \<union> named_vars ?C"
  have finite: "finite ?U" using support unfolding gi_extension_retraction_support_def
    by (auto intro: named_vars_finite)
  show ?case
  proof (rule exI[where x="?U"], rule gi_extension_retraction_supportI[OF finite Un_upper2])
    fix v assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> ?U"
    have fn: "\<And>\<tau>. v \<tau> \<notin> N" using fresh by blast
    have premise: "goodman_book_proves \<Omega> G T
      (book_iff G (named_retract \<Omega> v P) (named_retract \<Omega> v Q))"
      using gi_extension_retraction_apply[OF support stock fn] by (simp only: book_C_retract_iff)
    show "goodman_book_proves \<Omega> G T (named_retract \<Omega> v ?C)"
      by (simp only: book_C_retract_leibniz; rule goodman_book_proves.PE[OF premise
        book_retract_language[OF PE.hyps(2) stock] book_retract_language[OF PE.hyps(3) stock]])
  qed
qed

theorem gi_goodman_foreign_constants_eliminate:
  assumes rich: "sg_rich G" and derivation: "goodman_book_proves \<Sigma> G T A"
    and old_axioms: "\<And>B. B \<in> T \<Longrightarrow> book_theory_formula \<Omega> G B"
    and old_conclusion: "named_in_signature \<Omega> A"
  shows "goodman_book_proves \<Omega> G T A"
proof -
  obtain N where support: "gi_extension_retraction_support \<Omega> G T A N"
    using gi_extension_retraction_support_exists[OF rich derivation old_axioms] by blast
  have finite: "finite N" using support unfolding gi_extension_retraction_support_def by blast
  let ?v = "\<lambda>\<tau>. SOME n. G n = \<tau> \<and> n \<notin> N"
  have chosen: "G (?v \<tau>) = \<tau> \<and> ?v \<tau> \<notin> N" for \<tau>
    by (rule someI_ex, rule sg_rich_fresh[OF rich finite])
  have stock: "\<And>\<tau>. G (?v \<tau>) = \<tau>" and avoids: "\<And>\<tau>. ?v \<tau> \<notin> N" using chosen by blast+
  have retracted: "goodman_book_proves \<Omega> G T (named_retract \<Omega> ?v A)"
    by (rule gi_extension_retraction_apply[OF support stock avoids])
  show ?thesis using retracted by (simp only: named_retract_fixed[OF old_conclusion])
qed

theorem gi_goodman_signature_mono:
  assumes rich: "sg_rich G" and derivation: "goodman_book_proves \<Sigma> G T A"
    and inclusion: "\<And>\<tau>. \<Sigma> \<tau> \<subseteq> \<Omega> \<tau>"
  shows "goodman_book_proves \<Omega> G T A"
  using derivation
  by (induction rule: goodman_book_proves.induct)
    (auto intro: goodman_book_proves.intros book_full_C_signature_mono[OF rich _ inclusion]
      book_language_signature_mono[OF _ inclusion])

theorem gi_goodman_signature_conservativity:
  assumes rich: "sg_rich G" and inclusion: "\<And>\<tau>. \<Omega> \<tau> \<subseteq> \<Sigma> \<tau>"
    and old_axioms: "\<And>B. B \<in> T \<Longrightarrow> book_theory_formula \<Omega> G B"
    and old_conclusion: "named_in_signature \<Omega> A"
  shows "goodman_book_proves \<Sigma> G T A \<longleftrightarrow> goodman_book_proves \<Omega> G T A"
proof
  assume derivation: "goodman_book_proves \<Sigma> G T A"
  show "goodman_book_proves \<Omega> G T A"
    by (rule gi_goodman_foreign_constants_eliminate[OF rich derivation old_axioms old_conclusion])
next
  assume derivation: "goodman_book_proves \<Omega> G T A"
  show "goodman_book_proves \<Sigma> G T A"
    by (rule gi_goodman_signature_mono[OF rich derivation inclusion])
qed

corollary gi_goodman_consistency_universal_iff:
  assumes rich: "sg_rich G"
    and old_axioms: "\<And>B. B \<in> T \<Longrightarrow> book_theory_formula \<Omega> G B"
  shows "goodman_book_consistent (\<lambda>_. UNIV) G T \<longleftrightarrow> goodman_book_consistent \<Omega> G T"
proof -
  have names: "named_in_signature \<Omega> (book_bottom G)"
    by (rule book_language_signature[OF book_bottom_language[OF rich]])
  have equivalent: "goodman_book_proves (\<lambda>_. UNIV) G T (book_bottom G) \<longleftrightarrow>
    goodman_book_proves \<Omega> G T (book_bottom G)"
    by (rule gi_goodman_signature_conservativity[OF rich _ old_axioms names]; simp)
  show ?thesis unfolding goodman_book_consistent_def using equivalent by blast
qed

text \<open>
  The stock may be infinite and its axioms need not be closed for this
  signature theorem. They must already be formulas in Ω. Only finitely
  many fresh-name exclusions are needed for a given proof. This is a
  syntactic conservativity theorem for the actual axiom extension, not
  an appeal to ordinary-theory conservativity or an assumed model.
\<close>

end
