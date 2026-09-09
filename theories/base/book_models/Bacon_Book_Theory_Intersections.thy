theory Bacon_Book_Theory_Intersections
  imports Bacon_Book_Theory_Derivation
begin

section \<open>Common formulas of a family of higher-order theories\<close>

text \<open>
  The common theory consists of the formulas belonging to every member
  of a family of theories. The formula guard matters for the empty
  family: its common theory is the full set of well-formed formulas,
  not the entire raw term type. Source role: Definition 5.1, pp.97–98,
  and the theory-of-a-class form of Theorem 15.1.
  Status: purely syntactic closure, with no model or substitution rule.
\<close>

definition book_common_theory ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set set \<Rightarrow> 'c book_named_term set" where
  "book_common_theory \<Sigma> G Ts = {A. book_theory_formula \<Sigma> G A \<and> (\<forall>T \<in> Ts. A \<in> T)}"

lemma book_common_theory_empty:
  "book_common_theory \<Sigma> G {} = {A. book_theory_formula \<Sigma> G A}"
  by (simp add: book_common_theory_def)

lemma book_common_theory_subset:
  assumes member: "T \<in> Ts"
  shows "book_common_theory \<Sigma> G Ts \<subseteq> T"
  using member unfolding book_common_theory_def by blast

theorem book_common_theory_is_theory:
  assumes rich: "sg_rich G"
    and theories: "\<forall>T \<in> Ts. book_higher_order_theory \<Sigma> G T"
  shows "book_higher_order_theory \<Sigma> G (book_common_theory \<Sigma> G Ts)"
proof (unfold book_higher_order_theory_def, rule conjI)
  show "\<forall>A \<in> book_common_theory \<Sigma> G Ts. book_theory_formula \<Sigma> G A"
    unfolding book_common_theory_def by blast
next
  show "\<forall>A. book_theory_derivable \<Sigma> G (book_common_theory \<Sigma> G Ts) A \<longrightarrow>
    A \<in> book_common_theory \<Sigma> G Ts"
  proof (intro allI impI)
    fix A
    assume derivation: "book_theory_derivable \<Sigma> G (book_common_theory \<Sigma> G Ts) A"
    have language: "book_theory_formula \<Sigma> G A"
      by (rule book_theory_derivable_language[OF derivation rich])
    have common: "\<forall>T \<in> Ts. A \<in> T"
    proof (rule ballI)
      fix T
      assume member: "T \<in> Ts"
      have theory_ok: "book_higher_order_theory \<Sigma> G T" by (rule bspec[OF theories member])
      show "A \<in> T" by (rule book_theory_contains_derivation[OF theory_ok derivation
        book_common_theory_subset[OF member]])
    qed
    show "A \<in> book_common_theory \<Sigma> G Ts"
      unfolding book_common_theory_def by (rule CollectI, rule conjI[OF language common])
  qed
qed

section \<open>Equivalent closure under the six axiom schemas and two rules\<close>

lemma book_theory_imp_operands:
  assumes formula: "book_theory_formula \<Sigma> G (book_imp A B)"
  shows "book_theory_formula \<Sigma> G A \<and> book_theory_formula \<Sigma> G B"
proof -
  have whole: "book_theory_formula \<Sigma> G (NApp (NApp (NLogical SImp) A) B)"
    using formula by (simp only: book_imp_def)
  obtain \<upsilon> where partial: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NApp (NLogical SImp) A) (Arr \<upsilon> Prop)"
    and bt: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<upsilon>"
    by (rule book_language_App_obtain[OF whole]; rule that; assumption)
  obtain \<sigma> where head: "book_in_language book_minimal_logical_type UNIV \<Sigma> G
    (NLogical SImp) (Arr \<sigma> (Arr \<upsilon> Prop))"
    and at: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<sigma>"
    by (rule book_language_App_obtain[OF partial]; rule that; assumption)
  have types: "\<sigma> = Prop \<and> \<upsilon> = Prop" using head by (simp add: book_language_logical_iff)
  show ?thesis using at bt types by simp
qed

definition book_theory_rules :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_theory_rules \<Sigma> G T \<longleftrightarrow>
    (\<forall>A B. book_theory_formula \<Sigma> G A \<longrightarrow> book_theory_formula \<Sigma> G B \<longrightarrow>
      book_imp A (book_imp B A) \<in> T) \<and>
    (\<forall>A B C. book_theory_formula \<Sigma> G A \<longrightarrow> book_theory_formula \<Sigma> G B \<longrightarrow>
      book_theory_formula \<Sigma> G C \<longrightarrow>
      book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)) \<in> T) \<and>
    (\<forall>A B. book_theory_formula \<Sigma> G A \<longrightarrow> book_theory_formula \<Sigma> G B \<longrightarrow>
      book_imp (book_imp (book_not G A) (book_not G B)) (book_imp B A) \<in> T) \<and>
    (\<forall>\<sigma> F a. book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop) \<longrightarrow>
      book_in_language book_minimal_logical_type UNIV \<Sigma> G a \<sigma> \<longrightarrow>
      book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a) \<in> T) \<and>
    (\<forall>A B. book_theory_formula \<Sigma> G A \<longrightarrow> book_theory_formula \<Sigma> G B \<longrightarrow>
      (named_compatible_step named_beta_contract A B \<or> named_compatible_step named_beta_contract B A) \<longrightarrow>
      book_imp A B \<in> T) \<and>
    (\<forall>A B. book_theory_formula \<Sigma> G A \<longrightarrow> book_theory_formula \<Sigma> G B \<longrightarrow>
      (named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A) \<longrightarrow>
      book_imp A B \<in> T) \<and>
    (\<forall>A B. A \<in> T \<longrightarrow> book_imp A B \<in> T \<longrightarrow> B \<in> T) \<and>
    (\<forall>A B n. book_imp A B \<in> T \<longrightarrow> n \<notin> named_fv A \<longrightarrow>
      book_imp A (book_all G n B) \<in> T)"

text \<open>
  The last two clauses are the literal MP and Gen closures. Their
  operand typings follow from T being a set of formulas, using the
  preceding implication inversion lemma. No additional guard weakens
  those closures. PC3 keeps ((¬A) → (¬B)) → (B → A); β/η remain
  single contextual steps in either direction.
\<close>

theorem book_higher_order_theory_iff_rules:
  "book_higher_order_theory \<Sigma> G T \<longleftrightarrow>
    (\<forall>A \<in> T. book_theory_formula \<Sigma> G A) \<and> book_theory_rules \<Sigma> G T"
proof
  assume theory_ok: "book_higher_order_theory \<Sigma> G T"
  have typed: "\<forall>A \<in> T. book_theory_formula \<Sigma> G A"
    using theory_ok unfolding book_higher_order_theory_def by (rule conjunct1)
  have close: "A \<in> T" if "book_theory_derivable \<Sigma> G T A" for A
    by (rule book_theory_contains_derivation[OF theory_ok that subset_refl])
  have assume_rule: "book_theory_derivable \<Sigma> G T A" if "A \<in> T" for A
    by (rule book_theory_derivable.Assumption[OF that bspec[OF typed that]])
  have mp_rule: "B \<in> T" if am: "A \<in> T" and im: "book_imp A B \<in> T" for A B
  proof -
    have bl: "book_theory_formula \<Sigma> G B"
      by (rule conjunct2[OF book_theory_imp_operands[OF bspec[OF typed im]]])
    show ?thesis by (rule close, rule book_theory_derivable.MP[OF assume_rule[OF am] assume_rule[OF im] bl])
  qed
  have gen_rule: "book_imp A (book_all G n B) \<in> T"
    if im: "book_imp A B \<in> T" and fresh: "n \<notin> named_fv A" for A B n
  proof -
    have operands: "book_theory_formula \<Sigma> G A \<and> book_theory_formula \<Sigma> G B"
      by (rule book_theory_imp_operands[OF bspec[OF typed im]])
    show ?thesis by (rule close, rule book_theory_derivable.Gen[OF assume_rule[OF im]
      conjunct1[OF operands] conjunct2[OF operands] fresh])
  qed
  have rules: "book_theory_rules \<Sigma> G T"
    unfolding book_theory_rules_def
  proof (intro conjI)
    show "\<forall>A B. book_theory_formula \<Sigma> G A \<longrightarrow> book_theory_formula \<Sigma> G B \<longrightarrow>
      book_imp A (book_imp B A) \<in> T"
      by (intro allI impI, rule close, rule book_theory_derivable.PC1; assumption)
  next
    show "\<forall>A B C. book_theory_formula \<Sigma> G A \<longrightarrow> book_theory_formula \<Sigma> G B \<longrightarrow>
      book_theory_formula \<Sigma> G C \<longrightarrow>
      book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)) \<in> T"
      by (intro allI impI, rule close, rule book_theory_derivable.PC2; assumption)
  next
    show "\<forall>A B. book_theory_formula \<Sigma> G A \<longrightarrow> book_theory_formula \<Sigma> G B \<longrightarrow>
      book_imp (book_imp (book_not G A) (book_not G B)) (book_imp B A) \<in> T"
      by (intro allI impI, rule close, rule book_theory_derivable.PC3; assumption)
  next
    show "\<forall>\<sigma> F a. book_in_language book_minimal_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop) \<longrightarrow>
      book_in_language book_minimal_logical_type UNIV \<Sigma> G a \<sigma> \<longrightarrow>
      book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a) \<in> T"
      by (intro allI impI, rule close, rule book_theory_derivable.UI; assumption)
  next
    show "\<forall>A B. book_theory_formula \<Sigma> G A \<longrightarrow> book_theory_formula \<Sigma> G B \<longrightarrow>
      (named_compatible_step named_beta_contract A B \<or> named_compatible_step named_beta_contract B A) \<longrightarrow>
      book_imp A B \<in> T"
      by (intro allI impI, rule close, rule book_theory_derivable.Beta; assumption)
  next
    show "\<forall>A B. book_theory_formula \<Sigma> G A \<longrightarrow> book_theory_formula \<Sigma> G B \<longrightarrow>
      (named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A) \<longrightarrow>
      book_imp A B \<in> T"
      by (intro allI impI, rule close, rule book_theory_derivable.Eta; assumption)
  next
    show "\<forall>A B. A \<in> T \<longrightarrow> book_imp A B \<in> T \<longrightarrow> B \<in> T"
      by (intro allI impI, rule mp_rule; assumption)
  next
    show "\<forall>A B n. book_imp A B \<in> T \<longrightarrow> n \<notin> named_fv A \<longrightarrow>
      book_imp A (book_all G n B) \<in> T"
      by (intro allI impI, rule gen_rule; assumption)
  qed
  show "(\<forall>A \<in> T. book_theory_formula \<Sigma> G A) \<and> book_theory_rules \<Sigma> G T"
    by (rule conjI[OF typed rules])
next
  assume conditions: "(\<forall>A \<in> T. book_theory_formula \<Sigma> G A) \<and> book_theory_rules \<Sigma> G T"
  have typed: "\<forall>A \<in> T. book_theory_formula \<Sigma> G A" by (rule conjunct1[OF conditions])
  have rules: "book_theory_rules \<Sigma> G T" by (rule conjunct2[OF conditions])
  note rule_PC1 = conjunct1[OF rules[unfolded book_theory_rules_def]]
  note tail1 = conjunct2[OF rules[unfolded book_theory_rules_def]]
  note rule_PC2 = conjunct1[OF tail1]
  note tail2 = conjunct2[OF tail1]
  note rule_PC3 = conjunct1[OF tail2]
  note tail3 = conjunct2[OF tail2]
  note rule_UI = conjunct1[OF tail3]
  note tail4 = conjunct2[OF tail3]
  note rule_Beta = conjunct1[OF tail4]
  note tail5 = conjunct2[OF tail4]
  note rule_Eta = conjunct1[OF tail5]
  note tail6 = conjunct2[OF tail5]
  note rule_MP = conjunct1[OF tail6]
  note rule_Gen = conjunct2[OF tail6]
  have derived_member: "A \<in> T" if derivation: "book_theory_derivable \<Sigma> G S A" and subset: "S \<subseteq> T" for S A
    using derivation subset
  proof (induction rule: book_theory_derivable.induct)
    case Assumption
    show ?case by (rule subsetD[OF Assumption.prems Assumption.hyps(1)])
  next
    case PC1
    show ?case using rule_PC1 PC1.hyps by blast
  next
    case PC2
    show ?case using rule_PC2 PC2.hyps by blast
  next
    case PC3
    show ?case using rule_PC3 PC3.hyps by blast
  next
    case UI
    show ?case using rule_UI UI.hyps by blast
  next
    case Beta
    show ?case using rule_Beta Beta.hyps by blast
  next
    case Eta
    show ?case using rule_Eta Eta.hyps by blast
  next
    case MP
    show ?case using rule_MP MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] by blast
  next
    case Gen
    show ?case using rule_Gen Gen.IH[OF Gen.prems] Gen.hyps(4) by blast
  qed
  show "book_higher_order_theory \<Sigma> G T"
    unfolding book_higher_order_theory_def
    by (rule conjI[OF typed], intro allI impI, rule derived_member[OF _ subset_refl], assumption)
qed

end
