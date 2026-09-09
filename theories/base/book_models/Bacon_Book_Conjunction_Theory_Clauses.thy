theory Bacon_Book_Conjunction_Theory_Clauses
  imports Bacon_Book_Conjunction_Theory
begin

section \<open>The native theory class has exactly the printed closure conditions\<close>

text \<open>
  A native conjunction theory contains the nine axiom schemas PC1,
  PC2, PC3, UI, printed β, η, AndI, AndE1 and AndE2, and is closed
  under MP and Gen. Together with typed assumption membership these
  account for all twelve native derivation constructors.
  Source: Bacon's Chapter 5 theory discussion, pp.99–104, with the
  primitive-conjunction schemas of §5.2, p.104.

  The equivalence below spells out the fields rather than defining
  them through an encoding or semantic validity. Primitive ∧ stays
  book_conj_apply. MP and Gen have their literal membership and
  freshness conditions; their missing typing guards are recovered from
  the requirement that every member of T is a formula. There is no
  new side condition on the free variables of all premises.
  No richness, old-calculus proof, model, or additional rule is assumed.
\<close>

lemma book_conj_imp_operands:
  assumes formula: "book_conj_formula \<Sigma> G (book_conj_imp A B)"
  shows "book_conj_formula \<Sigma> G A \<and> book_conj_formula \<Sigma> G B"
proof -
  have whole: "book_conj_formula \<Sigma> G (NApp (NApp (NLogical (BCMinimal SImp)) A) B)"
    using formula by (simp only: book_conj_imp_def)
  obtain \<upsilon> where partial: "book_in_language book_conj_logical_type UNIV \<Sigma> G
    (NApp (NLogical (BCMinimal SImp)) A) (Arr \<upsilon> Prop)"
    and bt: "book_in_language book_conj_logical_type UNIV \<Sigma> G B \<upsilon>"
    by (rule book_language_App_obtain[OF whole]; rule that; assumption)
  obtain \<sigma> where head: "book_in_language book_conj_logical_type UNIV \<Sigma> G
    (NLogical (BCMinimal SImp)) (Arr \<sigma> (Arr \<upsilon> Prop))"
    and at: "book_in_language book_conj_logical_type UNIV \<Sigma> G A \<sigma>"
    by (rule book_language_App_obtain[OF partial]; rule that; assumption)
  have types: "\<sigma> = Prop \<and> \<upsilon> = Prop" using head by (simp add: book_language_logical_iff)
  show ?thesis using at bt types by simp
qed

definition book_conj_theory_rules :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_conj_term set \<Rightarrow> bool" where
  "book_conj_theory_rules \<Sigma> G T \<longleftrightarrow>
    (\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      book_conj_imp A (book_conj_imp B A) \<in> T) \<and>
    (\<forall>A B C. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      book_conj_formula \<Sigma> G C \<longrightarrow>
      book_conj_imp (book_conj_imp A (book_conj_imp B C)) (book_conj_imp (book_conj_imp A B) (book_conj_imp A C)) \<in> T) \<and>
    (\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      book_conj_imp (book_conj_imp (book_conj_not G A) (book_conj_not G B)) (book_conj_imp B A) \<in> T) \<and>
    (\<forall>\<sigma> F a. book_in_language book_conj_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop) \<longrightarrow>
      book_in_language book_conj_logical_type UNIV \<Sigma> G a \<sigma> \<longrightarrow>
      book_conj_imp (NApp (NLogical (BCMinimal (SBAll \<sigma>))) F) (NApp F a) \<in> T) \<and>
    (\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      (named_compatible_step book_printed_beta_contract A B \<or> named_compatible_step book_printed_beta_contract B A) \<longrightarrow>
      book_conj_imp A B \<in> T) \<and>
    (\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      (named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A) \<longrightarrow>
      book_conj_imp A B \<in> T) \<and>
    (\<forall>A B. A \<in> T \<longrightarrow> book_conj_imp A B \<in> T \<longrightarrow> B \<in> T) \<and>
    (\<forall>A B n. book_conj_imp A B \<in> T \<longrightarrow> n \<notin> named_fv A \<longrightarrow>
      book_conj_imp A (book_conj_all G n B) \<in> T) \<and>
    (\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      book_conj_imp A (book_conj_imp B (book_conj_apply A B)) \<in> T) \<and>
    (\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      book_conj_imp (book_conj_apply A B) A \<in> T) \<and>
    (\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      book_conj_imp (book_conj_apply A B) B \<in> T)"

text \<open>
  The MP and Gen clauses are the literal inference closures. Their
  operand typings follow from T being a set of formulas, using the
  preceding implication inversion lemma. No additional guard weakens
  those closures. PC3 keeps ((¬A) → (¬B)) → (B → A); β/η remain
  single contextual steps in either direction.
\<close>

theorem book_conj_higher_order_theory_iff_rules:
  "book_conj_higher_order_theory \<Sigma> G T \<longleftrightarrow>
    (\<forall>A \<in> T. book_conj_formula \<Sigma> G A) \<and> book_conj_theory_rules \<Sigma> G T"
proof
  assume theory_ok: "book_conj_higher_order_theory \<Sigma> G T"
  have typed: "\<forall>A \<in> T. book_conj_formula \<Sigma> G A"
    using theory_ok unfolding book_conj_higher_order_theory_def by (rule conjunct1)
  have close: "A \<in> T" if "book_conj_theory_derivable \<Sigma> G T A" for A
    by (rule book_conj_theory_contains_derivation[OF theory_ok that subset_refl])
  have assume_rule: "book_conj_theory_derivable \<Sigma> G T A" if "A \<in> T" for A
    by (rule book_conj_theory_derivable.Assumption[OF that bspec[OF typed that]])
  have mp_rule: "B \<in> T" if am: "A \<in> T" and im: "book_conj_imp A B \<in> T" for A B
  proof -
    have bl: "book_conj_formula \<Sigma> G B"
      by (rule conjunct2[OF book_conj_imp_operands[OF bspec[OF typed im]]])
    show ?thesis by (rule close, rule book_conj_theory_derivable.MP[OF assume_rule[OF am] assume_rule[OF im] bl])
  qed
  have gen_rule: "book_conj_imp A (book_conj_all G n B) \<in> T"
    if im: "book_conj_imp A B \<in> T" and fresh: "n \<notin> named_fv A" for A B n
  proof -
    have operands: "book_conj_formula \<Sigma> G A \<and> book_conj_formula \<Sigma> G B"
      by (rule book_conj_imp_operands[OF bspec[OF typed im]])
    show ?thesis by (rule close, rule book_conj_theory_derivable.Gen[OF assume_rule[OF im]
      conjunct1[OF operands] conjunct2[OF operands] fresh])
  qed
  have rules: "book_conj_theory_rules \<Sigma> G T"
    unfolding book_conj_theory_rules_def
  proof (intro conjI)
    show "\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      book_conj_imp A (book_conj_imp B A) \<in> T"
      by (intro allI impI, rule close, rule book_conj_theory_derivable.PC1; assumption)
  next
    show "\<forall>A B C. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      book_conj_formula \<Sigma> G C \<longrightarrow>
      book_conj_imp (book_conj_imp A (book_conj_imp B C)) (book_conj_imp (book_conj_imp A B) (book_conj_imp A C)) \<in> T"
      by (intro allI impI, rule close, rule book_conj_theory_derivable.PC2; assumption)
  next
    show "\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      book_conj_imp (book_conj_imp (book_conj_not G A) (book_conj_not G B)) (book_conj_imp B A) \<in> T"
      by (intro allI impI, rule close, rule book_conj_theory_derivable.PC3; assumption)
  next
    show "\<forall>\<sigma> F a. book_in_language book_conj_logical_type UNIV \<Sigma> G F (Arr \<sigma> Prop) \<longrightarrow>
      book_in_language book_conj_logical_type UNIV \<Sigma> G a \<sigma> \<longrightarrow>
      book_conj_imp (NApp (NLogical (BCMinimal (SBAll \<sigma>))) F) (NApp F a) \<in> T"
      by (intro allI impI, rule close, rule book_conj_theory_derivable.UI; assumption)
  next
    show "\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      (named_compatible_step book_printed_beta_contract A B \<or> named_compatible_step book_printed_beta_contract B A) \<longrightarrow>
      book_conj_imp A B \<in> T"
      by (intro allI impI, rule close, rule book_conj_theory_derivable.Beta; assumption)
  next
    show "\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      (named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A) \<longrightarrow>
      book_conj_imp A B \<in> T"
      by (intro allI impI, rule close, rule book_conj_theory_derivable.Eta; assumption)
  next
    show "\<forall>A B. A \<in> T \<longrightarrow> book_conj_imp A B \<in> T \<longrightarrow> B \<in> T"
      by (intro allI impI, rule mp_rule; assumption)
  next
    show "\<forall>A B n. book_conj_imp A B \<in> T \<longrightarrow> n \<notin> named_fv A \<longrightarrow>
      book_conj_imp A (book_conj_all G n B) \<in> T"
      by (intro allI impI, rule gen_rule; assumption)
  next
    show "\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      book_conj_imp A (book_conj_imp B (book_conj_apply A B)) \<in> T"
      by (intro allI impI, rule close, rule book_conj_theory_derivable.AndI; assumption)
  next
    show "\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      book_conj_imp (book_conj_apply A B) A \<in> T"
      by (intro allI impI, rule close, rule book_conj_theory_derivable.AndE1; assumption)
  next
    show "\<forall>A B. book_conj_formula \<Sigma> G A \<longrightarrow> book_conj_formula \<Sigma> G B \<longrightarrow>
      book_conj_imp (book_conj_apply A B) B \<in> T"
      by (intro allI impI, rule close, rule book_conj_theory_derivable.AndE2; assumption)
  qed
  show "(\<forall>A \<in> T. book_conj_formula \<Sigma> G A) \<and> book_conj_theory_rules \<Sigma> G T"
    by (rule conjI[OF typed rules])
next
  assume conditions: "(\<forall>A \<in> T. book_conj_formula \<Sigma> G A) \<and> book_conj_theory_rules \<Sigma> G T"
  have typed: "\<forall>A \<in> T. book_conj_formula \<Sigma> G A" by (rule conjunct1[OF conditions])
  have rules: "book_conj_theory_rules \<Sigma> G T" by (rule conjunct2[OF conditions])
  note rule_PC1 = conjunct1[OF rules[unfolded book_conj_theory_rules_def]]
  note tail1 = conjunct2[OF rules[unfolded book_conj_theory_rules_def]]
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
  note tail7 = conjunct2[OF tail6]
  note rule_Gen = conjunct1[OF tail7]
  note tail8 = conjunct2[OF tail7]
  note rule_AndI = conjunct1[OF tail8]
  note tail9 = conjunct2[OF tail8]
  note rule_AndE1 = conjunct1[OF tail9]
  note rule_AndE2 = conjunct2[OF tail9]
  have derived_member: "A \<in> T" if derivation: "book_conj_theory_derivable \<Sigma> G S A" and subset: "S \<subseteq> T" for S A
    using derivation subset
  proof (induction rule: book_conj_theory_derivable.induct)
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
  next
    case AndI
    show ?case using rule_AndI AndI.hyps by blast
  next
    case AndE1
    show ?case using rule_AndE1 AndE1.hyps by blast
  next
    case AndE2
    show ?case using rule_AndE2 AndE2.hyps by blast
  qed
  show "book_conj_higher_order_theory \<Sigma> G T"
    unfolding book_conj_higher_order_theory_def
    by (rule conjI[OF typed], intro allI impI, rule derived_member[OF _ subset_refl], assumption)
qed

end
