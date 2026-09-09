theory Bacon_Book_Conjunction_Theory
  imports Bacon_Book_Primitive_Conjunction_Theory_Derivation
begin

section \<open>Replacing native derivable assumptions\<close>

text \<open>
  If every premise in T follows natively from S, every native consequence
  of T follows natively from S. The proof is an induction over all twelve
  constructors, preserving the printed β guard and the actual Gen rule.
  No encoding into another calculus is used.
\<close>

theorem book_conj_theory_derivable_cut:
  assumes derivation: "book_conj_theory_derivable \<Sigma> G T A"
    and replacements: "\<And>B. B \<in> T \<Longrightarrow> book_conj_theory_derivable \<Sigma> G S B"
  shows "book_conj_theory_derivable \<Sigma> G S A"
  using derivation replacements
proof (induction rule: book_conj_theory_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case PC1
  show ?case by (rule book_conj_theory_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_conj_theory_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_conj_theory_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_conj_theory_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_conj_theory_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_conj_theory_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_conj_theory_derivable.MP[
    OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_conj_theory_derivable.Gen[OF Gen.IH[OF Gen.prems] Gen.hyps(2,3,4)])
next
  case AndI
  show ?case by (rule book_conj_theory_derivable.AndI[OF AndI.hyps])
next
  case AndE1
  show ?case by (rule book_conj_theory_derivable.AndE1[OF AndE1.hyps])
next
  case AndE2
  show ?case by (rule book_conj_theory_derivable.AndE2[OF AndE2.hyps])
qed

section \<open>The independent native theory class and its least extensions\<close>

text \<open>
  A conjunction theory is a set of native formulas closed under native
  derivability. The judgment already has exactly the Chapter 5 printed
  rules and the three primitive-conjunction schemas of §5.2, p.104.
  Neither the definition nor the following minimality proof uses a fixed
  background encoding, semantic validity, or a model.

  Consequences of each S form a theory under rich G. To characterize
  derivability by EVERY theory containing S, require each member of S
  to be a formula: malformed premises could otherwise leave no containing
  theory and make that universal condition vacuous.
\<close>

definition book_conj_higher_order_theory ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_conj_term set \<Rightarrow> bool" where
  "book_conj_higher_order_theory \<Sigma> G T \<longleftrightarrow>
    (\<forall>A\<in>T. book_conj_formula \<Sigma> G A) \<and>
    (\<forall>A. book_conj_theory_derivable \<Sigma> G T A \<longrightarrow> A \<in> T)"

lemma book_conj_theory_contains_derivation:
  assumes theory_ok: "book_conj_higher_order_theory \<Sigma> G T"
    and derivation: "book_conj_theory_derivable \<Sigma> G S A" and inclusion: "S \<subseteq> T"
  shows "A \<in> T"
proof -
  have lifted: "book_conj_theory_derivable \<Sigma> G T A"
    by (rule book_conj_theory_derivable_mono[OF derivation inclusion])
  show ?thesis using theory_ok lifted unfolding book_conj_higher_order_theory_def by blast
qed

theorem book_conj_derivable_consequences_form_theory:
  assumes rich: "sg_rich G"
  shows "book_conj_higher_order_theory \<Sigma> G {A. book_conj_theory_derivable \<Sigma> G S A}"
proof (unfold book_conj_higher_order_theory_def, rule conjI)
  show "\<forall>A\<in>{A. book_conj_theory_derivable \<Sigma> G S A}. book_conj_formula \<Sigma> G A"
  proof (rule ballI)
    fix A
    assume member: "A \<in> {A. book_conj_theory_derivable \<Sigma> G S A}"
    have derivation: "book_conj_theory_derivable \<Sigma> G S A" using member by simp
    show "book_conj_formula \<Sigma> G A" by (rule book_conj_theory_derivable_language[OF derivation rich])
  qed
next
  show "\<forall>A. book_conj_theory_derivable \<Sigma> G {B. book_conj_theory_derivable \<Sigma> G S B} A \<longrightarrow>
    A \<in> {A. book_conj_theory_derivable \<Sigma> G S A}"
  proof (intro allI impI)
    fix A
    assume derivation: "book_conj_theory_derivable \<Sigma> G {B. book_conj_theory_derivable \<Sigma> G S B} A"
    have reduced: "book_conj_theory_derivable \<Sigma> G S A"
      by (rule book_conj_theory_derivable_cut[OF derivation]) simp
    show "A \<in> {A. book_conj_theory_derivable \<Sigma> G S A}" using reduced by simp
  qed
qed

theorem book_conj_theory_derivable_iff_all_theories:
  assumes rich: "sg_rich G"
    and language: "\<And>B. B \<in> S \<Longrightarrow> book_conj_formula \<Sigma> G B"
  shows "book_conj_theory_derivable \<Sigma> G S A \<longleftrightarrow>
    (\<forall>T. book_conj_higher_order_theory \<Sigma> G T \<longrightarrow> S \<subseteq> T \<longrightarrow> A \<in> T)"
proof
  assume derivation: "book_conj_theory_derivable \<Sigma> G S A"
  show "\<forall>T. book_conj_higher_order_theory \<Sigma> G T \<longrightarrow> S \<subseteq> T \<longrightarrow> A \<in> T"
    by (intro allI impI, rule book_conj_theory_contains_derivation[OF _ derivation]; assumption)
next
  assume all_theories: "\<forall>T. book_conj_higher_order_theory \<Sigma> G T \<longrightarrow> S \<subseteq> T \<longrightarrow> A \<in> T"
  have theory_ok: "book_conj_higher_order_theory \<Sigma> G {B. book_conj_theory_derivable \<Sigma> G S B}"
    by (rule book_conj_derivable_consequences_form_theory[OF rich])
  have inclusion: "S \<subseteq> {B. book_conj_theory_derivable \<Sigma> G S B}"
  proof
    fix B
    assume member: "B \<in> S"
    have derivation: "book_conj_theory_derivable \<Sigma> G S B"
      by (rule book_conj_theory_derivable.Assumption[OF member language[OF member]])
    show "B \<in> {B. book_conj_theory_derivable \<Sigma> G S B}" using derivation by simp
  qed
  show "book_conj_theory_derivable \<Sigma> G S A" using all_theories theory_ok inclusion by blast
qed

corollary book_conj_least_theory_is_theory:
  assumes rich: "sg_rich G"
  shows "book_conj_higher_order_theory \<Sigma> G {A. book_conj_theory_derivable \<Sigma> G {} A}"
  by (rule book_conj_derivable_consequences_form_theory[OF rich])

end
