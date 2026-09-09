theory Bacon_Book_Theory_Derivation
  imports Bacon_Book_Minimal_Formula_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Conversion_Steps
begin

section \<open>Theory derivability in the book's minimal logical signature\<close>

text \<open>
  A higher-order theory contains PC1, PC2, PC3, UI, β and η and
  is closed under MP and Gen (Bacon, Definition 5.1, pp.97–98).
  PC3 is ((¬A) → (¬B)) → (B → A), in that order. Both β and η
  schemas use immediate contextual equivalence in either direction,
  not a whole conversion chain as an additional primitive axiom.

  Representation: book_theory_derivable closes a set S under exactly
  those schemas and rules. The fixed stock G does not shrink during Gen.
  This is theory closure, not the paper's different local consequence
  relation with only Assumption/Theorem/MP.

  Status: no arbitrary-PC, Ref, LL, Inst, Existence, α, or uniform
  substitution constructor is added. In particular this relation is not
  named H: the later Bacon_Book_Logic leaf derives the identification
  with the smallest logic after proving substitution admissibility
  as required by Definition 5.2, p.99.
  No semantic interpretation is imported.
\<close>

abbreviation book_theory_formula :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> bool" where
  "book_theory_formula \<Sigma> G A \<equiv> book_in_language book_minimal_logical_type UNIV \<Sigma> G A Prop"

inductive book_theory_derivable ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Assumption: "A \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G A \<Longrightarrow> book_theory_derivable \<Sigma> G S A"
| PC1: "book_theory_formula \<Sigma> G A \<Longrightarrow> book_theory_formula \<Sigma> G B \<Longrightarrow>
    book_theory_derivable \<Sigma> G S (book_imp A (book_imp B A))"
| PC2: "book_theory_formula \<Sigma> G A \<Longrightarrow> book_theory_formula \<Sigma> G B \<Longrightarrow>
    book_theory_formula \<Sigma> G C \<Longrightarrow> book_theory_derivable \<Sigma> G S
      (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)))"
| PC3: "book_theory_formula \<Sigma> G A \<Longrightarrow> book_theory_formula \<Sigma> G B \<Longrightarrow>
    book_theory_derivable \<Sigma> G S (book_imp (book_imp (book_not G A) (book_not G B)) (book_imp B A))"
| UI: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop) \<Longrightarrow>
    book_in_language book_minimal_logical_type UNIV \<Sigma> G a \<sigma> \<Longrightarrow>
    book_theory_derivable \<Sigma> G S (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
| Beta: "book_theory_formula \<Sigma> G A \<Longrightarrow> book_theory_formula \<Sigma> G B \<Longrightarrow>
    (named_compatible_step named_beta_contract A B \<or> named_compatible_step named_beta_contract B A) \<Longrightarrow>
    book_theory_derivable \<Sigma> G S (book_imp A B)"
| Eta: "book_theory_formula \<Sigma> G A \<Longrightarrow> book_theory_formula \<Sigma> G B \<Longrightarrow>
    (named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A) \<Longrightarrow>
    book_theory_derivable \<Sigma> G S (book_imp A B)"
| MP: "book_theory_derivable \<Sigma> G S A \<Longrightarrow> book_theory_derivable \<Sigma> G S (book_imp A B) \<Longrightarrow>
    book_theory_formula \<Sigma> G B \<Longrightarrow> book_theory_derivable \<Sigma> G S B"
| Gen: "book_theory_derivable \<Sigma> G S (book_imp A B) \<Longrightarrow>
    book_theory_formula \<Sigma> G A \<Longrightarrow> book_theory_formula \<Sigma> G B \<Longrightarrow>
    n \<notin> named_fv A \<Longrightarrow> book_theory_derivable \<Sigma> G S (book_imp A (book_all G n B))"

lemma book_theory_UI_language:
  assumes predicate: "book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop)"
    and argument: "book_in_language book_minimal_logical_type UNIV \<Sigma> G a \<sigma>"
  shows "book_theory_formula \<Sigma> G (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
proof -
  have quantifier: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NLogical (SBAll \<sigma>)) (Arr (Arr \<sigma> Prop) Prop)"
    by (rule book_all_operator_language)
  show ?thesis by (rule book_imp_language[OF book_language_App[OF quantifier predicate]
    book_language_App[OF predicate argument]])
qed

theorem book_theory_derivable_language:
  assumes derivation: "book_theory_derivable \<Sigma> G S A" and rich: "sg_rich G"
  shows "book_theory_formula \<Sigma> G A"
  using derivation
proof (induction rule: book_theory_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.hyps(2))
next
  case PC1
  show ?case by (intro book_imp_language; rule PC1.hyps)
next
  case PC2
  show ?case by (intro book_imp_language; rule PC2.hyps)
next
  case PC3
  show ?case by (intro book_imp_language)
    (rule book_not_language[OF rich PC3.hyps(1)], rule book_not_language[OF rich PC3.hyps(2)],
      rule PC3.hyps(2), rule PC3.hyps(1))
next
  case UI
  show ?case by (rule book_theory_UI_language[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_imp_language[OF Beta.hyps(1,2)])
next
  case Eta
  show ?case by (rule book_imp_language[OF Eta.hyps(1,2)])
next
  case MP
  show ?case by (rule MP.hyps(3))
next
  case Gen
  show ?case by (rule book_imp_language[OF Gen.hyps(2) book_all_language[OF Gen.hyps(3)]])
qed

section \<open>Monotonicity and replacement of derivable assumptions\<close>

lemma book_theory_derivable_mono:
  assumes derivation: "book_theory_derivable \<Sigma> G S A" and inclusion: "S \<subseteq> T"
  shows "book_theory_derivable \<Sigma> G T A"
  using derivation inclusion
proof (induction rule: book_theory_derivable.induct)
  case Assumption
  show ?case by (rule book_theory_derivable.Assumption[OF subsetD[OF Assumption.prems Assumption.hyps(1)]
    Assumption.hyps(2)])
next
  case PC1
  show ?case by (rule book_theory_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_theory_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_theory_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_theory_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_theory_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_theory_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_theory_derivable.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_theory_derivable.Gen[OF Gen.IH[OF Gen.prems] Gen.hyps(2,3,4)])
qed

lemma book_theory_derivable_cut:
  assumes derivation: "book_theory_derivable \<Sigma> G T A"
    and replacements: "\<And>B. B \<in> T \<Longrightarrow> book_theory_derivable \<Sigma> G S B"
  shows "book_theory_derivable \<Sigma> G S A"
  using derivation replacements
proof (induction rule: book_theory_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case PC1
  show ?case by (rule book_theory_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_theory_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_theory_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_theory_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_theory_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_theory_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_theory_derivable.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_theory_derivable.Gen[OF Gen.IH[OF Gen.prems] Gen.hyps(2,3,4)])
qed

section \<open>Higher-order theories and the smallest theory containing S\<close>

text \<open>
  A theory is a set of formulas closed under the displayed derivations.
  This contains precisely the six axiom schemas and is closed under MP
  and Gen. The minimality theorem below is proved using the set of all
  derivable consequences and cut; it is not taken as the definition of
  derivability. Requiring S to consist of formulas prevents a vacuous
  universal claim about typed theories containing malformed assumptions.
\<close>

definition book_higher_order_theory ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_higher_order_theory \<Sigma> G T \<longleftrightarrow>
    (\<forall>A \<in> T. book_theory_formula \<Sigma> G A) \<and>
    (\<forall>A. book_theory_derivable \<Sigma> G T A \<longrightarrow> A \<in> T)"

lemma book_theory_contains_derivation:
  assumes theory_ok: "book_higher_order_theory \<Sigma> G T"
    and derivation: "book_theory_derivable \<Sigma> G S A" and inclusion: "S \<subseteq> T"
  shows "A \<in> T"
proof -
  have lifted: "book_theory_derivable \<Sigma> G T A" by (rule book_theory_derivable_mono[OF derivation inclusion])
  show ?thesis using theory_ok lifted unfolding book_higher_order_theory_def by blast
qed

theorem book_derivable_consequences_form_theory:
  assumes rich: "sg_rich G"
  shows "book_higher_order_theory \<Sigma> G {A. book_theory_derivable \<Sigma> G S A}"
proof (unfold book_higher_order_theory_def, rule conjI)
  show "\<forall>A \<in> {A. book_theory_derivable \<Sigma> G S A}. book_theory_formula \<Sigma> G A"
    by (intro ballI, rule book_theory_derivable_language[OF _ rich]) simp
next
  show "\<forall>A. book_theory_derivable \<Sigma> G {B. book_theory_derivable \<Sigma> G S B} A \<longrightarrow>
    A \<in> {A. book_theory_derivable \<Sigma> G S A}"
  proof (intro allI impI)
    fix A
    assume derivation: "book_theory_derivable \<Sigma> G {B. book_theory_derivable \<Sigma> G S B} A"
    have reduced: "book_theory_derivable \<Sigma> G S A"
      by (rule book_theory_derivable_cut[OF derivation]) simp
    show "A \<in> {A. book_theory_derivable \<Sigma> G S A}" using reduced by simp
  qed
qed

theorem book_theory_derivable_iff_all_theories:
  assumes rich: "sg_rich G" and assumptions_typed: "\<And>B. B \<in> S \<Longrightarrow> book_theory_formula \<Sigma> G B"
  shows "book_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    (\<forall>T. book_higher_order_theory \<Sigma> G T \<longrightarrow> S \<subseteq> T \<longrightarrow> A \<in> T)"
proof
  assume derivation: "book_theory_derivable \<Sigma> G S A"
  show "\<forall>T. book_higher_order_theory \<Sigma> G T \<longrightarrow> S \<subseteq> T \<longrightarrow> A \<in> T"
    by (intro allI impI, rule book_theory_contains_derivation[OF _ derivation]; assumption)
next
  assume all_theories: "\<forall>T. book_higher_order_theory \<Sigma> G T \<longrightarrow> S \<subseteq> T \<longrightarrow> A \<in> T"
  have theory_ok: "book_higher_order_theory \<Sigma> G {B. book_theory_derivable \<Sigma> G S B}"
    by (rule book_derivable_consequences_form_theory[OF rich])
  have inclusion: "S \<subseteq> {B. book_theory_derivable \<Sigma> G S B}"
  proof
    fix B
    assume member: "B \<in> S"
    have derivation: "book_theory_derivable \<Sigma> G S B"
      by (rule book_theory_derivable.Assumption[OF member assumptions_typed[OF member]])
    show "B \<in> {B. book_theory_derivable \<Sigma> G S B}" using derivation by simp
  qed
  show "book_theory_derivable \<Sigma> G S A" using all_theories theory_ok inclusion by blast
qed

section \<open>Each derivation uses finitely many assumptions\<close>

lemma book_theory_empty_finite_support:
  assumes derivation: "book_theory_derivable \<Sigma> G {} A"
  shows "\<exists>U. finite U \<and> U \<subseteq> S \<and> book_theory_derivable \<Sigma> G U A"
  by (rule exI[where x="{}"], rule conjI[OF finite.emptyI],
    rule conjI[OF empty_subsetI derivation])

theorem book_theory_derivable_finite_support:
  assumes derivation: "book_theory_derivable \<Sigma> G S A"
  shows "\<exists>U. finite U \<and> U \<subseteq> S \<and> book_theory_derivable \<Sigma> G U A"
  using derivation
proof (induction rule: book_theory_derivable.induct)
  case (Assumption A S)
  have finite: "finite {A}" by simp
  have subset: "{A} \<subseteq> S" using Assumption.hyps(1) by simp
  have native: "book_theory_derivable \<Sigma> G {A} A"
    by (rule book_theory_derivable.Assumption[OF insertI1 Assumption.hyps(2)])
  show ?case by (rule exI[where x="{A}"], rule conjI[OF finite conjI[OF subset native]])
next
  case PC1
  show ?case by (rule book_theory_empty_finite_support, rule book_theory_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_theory_empty_finite_support, rule book_theory_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_theory_empty_finite_support, rule book_theory_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_theory_empty_finite_support, rule book_theory_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_theory_empty_finite_support, rule book_theory_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_theory_empty_finite_support, rule book_theory_derivable.Eta[OF Eta.hyps])
next
  case (MP S A B)
  obtain U where uf: "finite U" and us: "U \<subseteq> S" and left: "book_theory_derivable \<Sigma> G U A"
    using MP.IH(1) by (elim exE conjE)
  obtain W where wf: "finite W" and ws: "W \<subseteq> S"
    and right: "book_theory_derivable \<Sigma> G W (book_imp A B)"
    using MP.IH(2) by (elim exE conjE)
  have finite: "finite (U \<union> W)" by (rule finite_UnI[OF uf wf])
  have subset: "U \<union> W \<subseteq> S" by (rule Un_least[OF us ws])
  have left': "book_theory_derivable \<Sigma> G (U \<union> W) A"
    by (rule book_theory_derivable_mono[OF left Un_upper1])
  have right': "book_theory_derivable \<Sigma> G (U \<union> W) (book_imp A B)"
    by (rule book_theory_derivable_mono[OF right Un_upper2])
  have native: "book_theory_derivable \<Sigma> G (U \<union> W) B"
    by (rule book_theory_derivable.MP[OF left' right' MP.hyps(3)])
  show ?case by (rule exI[where x="U \<union> W"], rule conjI[OF finite conjI[OF subset native]])
next
  case (Gen S A B n)
  obtain U where uf: "finite U" and us: "U \<subseteq> S"
    and premise: "book_theory_derivable \<Sigma> G U (book_imp A B)"
    using Gen.IH by (elim exE conjE)
  have native: "book_theory_derivable \<Sigma> G U (book_imp A (book_all G n B))"
    by (rule book_theory_derivable.Gen[OF premise Gen.hyps(2,3,4)])
  show ?case by (rule exI[where x=U], rule conjI[OF uf conjI[OF us native]])
qed

end
