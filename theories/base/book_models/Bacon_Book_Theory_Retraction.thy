theory Bacon_Book_Theory_Retraction
  imports Bacon_Book_Theory_Derivation Bacon_Book_Retraction_Syntax
begin

section \<open>Finite forbidden-name support for a retracted theory derivation\<close>

text \<open>
  A proof S ⊢Σ A has a finite set N containing Vars(A) such that
  replacing foreign constants by typed variables outside N gives
  retΩ(S) ⊢Ω retΩ(A). Source role: the signature-relative proof
  substitution argument in Bacon, pp.99–102.

  Representation. N follows the proof, not the whole premise set.
  MP unions both supports and the conclusion's names. Gen additionally
  records its eigenvariable, so retraction cannot introduce that name
  into the antecedent. Immediate β/η use both endpoint-name sets.
  There is no inclusion requirement between the old and new signatures.

  Status. Fresh-proof retraction only, not arbitrary payload substitution
  or the identification of the smallest theory with H. No rich stock,
  model, extra rule, or uniform finite support for all of S is assumed.
\<close>

definition book_theory_retraction_support where
  "book_theory_retraction_support \<Omega> G S A N \<longleftrightarrow>
    finite N \<and> named_vars A \<subseteq> N \<and>
    (\<forall>v. (\<forall>\<tau>. G (v \<tau>) = \<tau>) \<longrightarrow> (\<forall>\<tau>. v \<tau> \<notin> N) \<longrightarrow>
      book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v A))"

lemma book_theory_retraction_supportI:
  assumes finite: "finite N" and names: "named_vars A \<subseteq> N"
    and transform: "\<And>v. (\<And>\<tau>. G (v \<tau>) = \<tau>) \<Longrightarrow> (\<And>\<tau>. v \<tau> \<notin> N) \<Longrightarrow>
      book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v A)"
  shows "book_theory_retraction_support \<Omega> G S A N"
proof (unfold book_theory_retraction_support_def, rule conjI[OF finite], rule conjI[OF names], intro allI impI)
  fix v
  assume stock: "\<forall>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<forall>\<tau>. v \<tau> \<notin> N"
  have types: "\<And>\<tau>. G (v \<tau>) = \<tau>" by (rule spec[OF stock])
  have avoids: "\<And>\<tau>. v \<tau> \<notin> N" by (rule spec[OF fresh])
  show "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v A)"
    by (rule transform[OF types avoids])
qed

lemma book_theory_retraction_support_finite:
  "book_theory_retraction_support \<Omega> G S A N \<Longrightarrow> finite N"
  unfolding book_theory_retraction_support_def by (rule conjunct1)

lemma book_theory_retraction_support_apply:
  assumes support: "book_theory_retraction_support \<Omega> G S A N"
    and stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> N"
  shows "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v A)"
proof -
  note choices = conjunct2[OF conjunct2[OF support[unfolded book_theory_retraction_support_def]]]
  have types: "\<forall>\<tau>. G (v \<tau>) = \<tau>" by (rule allI, rule stock)
  have avoids: "\<forall>\<tau>. v \<tau> \<notin> N" by (rule allI, rule fresh)
  show ?thesis by (rule mp[OF mp[OF spec[where x=v, OF choices] types] avoids])
qed

lemma book_theory_retraction_at_names:
  assumes transform: "\<And>v. (\<And>\<tau>. G (v \<tau>) = \<tau>) \<Longrightarrow>
    (\<And>\<tau>. v \<tau> \<notin> named_vars A) \<Longrightarrow>
    book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v A)"
  shows "\<exists>N. book_theory_retraction_support \<Omega> G S A N"
  by (rule exI[where x="named_vars A"],
    rule book_theory_retraction_supportI[OF named_vars_finite subset_refl transform])

theorem book_theory_derivable_retraction_support:
  assumes derivation: "book_theory_derivable \<Sigma> G S A"
  shows "\<exists>N. book_theory_retraction_support \<Omega> G S A N"
  using derivation
proof (induction rule: book_theory_derivable.induct)
  case (Assumption A S)
  show ?case
  proof (rule book_theory_retraction_at_names)
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> named_vars A"
    have member: "named_retract \<Omega> v A \<in> image (named_retract \<Omega> v) S"
      by (rule imageI[OF Assumption.hyps(1)])
    show "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v A)"
      by (rule book_theory_derivable.Assumption[OF member book_retract_language[OF Assumption.hyps(2) stock]])
  qed
next
  case (PC1 A B S)
  show ?case
  proof (rule book_theory_retraction_at_names)
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>"
      and fresh: "\<And>\<tau>. v \<tau> \<notin> named_vars (book_imp A (book_imp B A))"
    show "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S)
      (named_retract \<Omega> v (book_imp A (book_imp B A)))"
      by (simp only: book_retract_imp; rule book_theory_derivable.PC1[OF
        book_retract_language[OF PC1.hyps(1) stock] book_retract_language[OF PC1.hyps(2) stock]])
  qed
next
  case (PC2 A B C S)
  show ?case
  proof (rule book_theory_retraction_at_names)
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>"
      and fresh: "\<And>\<tau>. v \<tau> \<notin> named_vars
        (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)))"
    show "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v
      (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C))))"
      by (simp only: book_retract_imp; rule book_theory_derivable.PC2[OF
        book_retract_language[OF PC2.hyps(1) stock] book_retract_language[OF PC2.hyps(2) stock]
        book_retract_language[OF PC2.hyps(3) stock]])
  qed
next
  case (PC3 A B S)
  show ?case
  proof (rule book_theory_retraction_at_names)
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>"
      and fresh: "\<And>\<tau>. v \<tau> \<notin> named_vars
        (book_imp (book_imp (book_not G A) (book_not G B)) (book_imp B A))"
    show "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v
      (book_imp (book_imp (book_not G A) (book_not G B)) (book_imp B A)))"
      by (simp only: book_retract_imp book_retract_not; rule book_theory_derivable.PC3[OF
        book_retract_language[OF PC3.hyps(1) stock] book_retract_language[OF PC3.hyps(2) stock]])
  qed
next
  case (UI F \<sigma> a S)
  show ?case
  proof (rule book_theory_retraction_at_names)
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>"
      and fresh: "\<And>\<tau>. v \<tau> \<notin> named_vars (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
    show "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S)
      (named_retract \<Omega> v (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a)))"
      by (simp only: book_retract_imp named_retract.simps; rule book_theory_derivable.UI[OF
        book_retract_language[OF UI.hyps(1) stock] book_retract_language[OF UI.hyps(2) stock]])
  qed
next
  case (Beta A B S)
  show ?case
  proof (rule book_theory_retraction_at_names)
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> named_vars (book_imp A B)"
    have endpoints: "\<And>\<tau>. v \<tau> \<notin> named_vars A \<union> named_vars B" using fresh by (simp add: book_imp_def)
    have step: "named_compatible_step named_beta_contract (named_retract \<Omega> v A) (named_retract \<Omega> v B) \<or>
      named_compatible_step named_beta_contract (named_retract \<Omega> v B) (named_retract \<Omega> v A)"
      by (rule book_retract_beta_equivalent[OF Beta.hyps(3) endpoints])
    show "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v (book_imp A B))"
      by (simp only: book_retract_imp; rule book_theory_derivable.Beta[OF
        book_retract_language[OF Beta.hyps(1) stock] book_retract_language[OF Beta.hyps(2) stock] step])
  qed
next
  case (Eta A B S)
  show ?case
  proof (rule book_theory_retraction_at_names)
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> named_vars (book_imp A B)"
    have endpoints: "\<And>\<tau>. v \<tau> \<notin> named_vars A \<union> named_vars B" using fresh by (simp add: book_imp_def)
    have step: "named_compatible_step named_eta_contract (named_retract \<Omega> v A) (named_retract \<Omega> v B) \<or>
      named_compatible_step named_eta_contract (named_retract \<Omega> v B) (named_retract \<Omega> v A)"
      by (rule book_retract_eta_equivalent[OF Eta.hyps(3) endpoints])
    show "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v (book_imp A B))"
      by (simp only: book_retract_imp; rule book_theory_derivable.Eta[OF
        book_retract_language[OF Eta.hyps(1) stock] book_retract_language[OF Eta.hyps(2) stock] step])
  qed
next
  case (MP S A B)
  obtain N where first: "book_theory_retraction_support \<Omega> G S A N" using MP.IH(1) by (elim exE)
  obtain K where second: "book_theory_retraction_support \<Omega> G S (book_imp A B) K" using MP.IH(2) by (elim exE)
  let ?U = "N \<union> K \<union> named_vars B"
  have finite: "finite ?U"
    using book_theory_retraction_support_finite[OF first] book_theory_retraction_support_finite[OF second]
    by (simp add: named_vars_finite)
  have names: "named_vars B \<subseteq> ?U" by simp
  show ?case
  proof (rule exI[where x="?U"], rule book_theory_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> ?U"
    have fn: "\<And>\<tau>. v \<tau> \<notin> N" using fresh by blast
    have fk: "\<And>\<tau>. v \<tau> \<notin> K" using fresh by blast
    have left: "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v A)"
      by (rule book_theory_retraction_support_apply[OF first stock fn])
    have right: "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S)
      (book_imp (named_retract \<Omega> v A) (named_retract \<Omega> v B))"
      using book_theory_retraction_support_apply[OF second stock fk] by (simp only: book_retract_imp)
    show "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v B)"
      by (rule book_theory_derivable.MP[OF left right book_retract_language[OF MP.hyps(3) stock]])
  qed
next
  case (Gen S A B n)
  obtain N where support: "book_theory_retraction_support \<Omega> G S (book_imp A B) N"
    using Gen.IH by (elim exE)
  let ?C = "book_imp A (book_all G n B)"
  let ?U = "insert n (N \<union> named_vars ?C)"
  have finite: "finite ?U" using book_theory_retraction_support_finite[OF support] by (simp add: named_vars_finite)
  have names: "named_vars ?C \<subseteq> ?U" by blast
  show ?case
  proof (rule exI[where x="?U"], rule book_theory_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<tau>. G (v \<tau>) = \<tau>" and fresh: "\<And>\<tau>. v \<tau> \<notin> ?U"
    have fn: "\<And>\<tau>. v \<tau> \<notin> N" using fresh by blast
    have not_n: "\<And>\<tau>. v \<tau> \<noteq> n" using fresh by blast
    have antecedent_fresh: "n \<notin> named_fv (named_retract \<Omega> v A)"
      by (rule named_retract_fresh[OF Gen.hyps(4) not_n])
    have premise: "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S)
      (book_imp (named_retract \<Omega> v A) (named_retract \<Omega> v B))"
      using book_theory_retraction_support_apply[OF support stock fn] by (simp only: book_retract_imp)
    show "book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v ?C)"
      by (simp only: book_retract_imp book_retract_all; rule book_theory_derivable.Gen[OF premise
        book_retract_language[OF Gen.hyps(2) stock] book_retract_language[OF Gen.hyps(3) stock] antecedent_fresh])
  qed
qed

theorem book_theory_retraction:
  assumes derivation: "book_theory_derivable \<Sigma> G S A"
  shows "\<exists>N. finite N \<and> named_vars A \<subseteq> N \<and>
    (\<forall>v. (\<forall>\<tau>. G (v \<tau>) = \<tau>) \<longrightarrow> (\<forall>\<tau>. v \<tau> \<notin> N) \<longrightarrow>
      book_theory_derivable \<Omega> G (image (named_retract \<Omega> v) S) (named_retract \<Omega> v A))"
  using book_theory_derivable_retraction_support[OF derivation]
  by (simp only: book_theory_retraction_support_def)

end
