theory Bacon_Book_Lambda_I_Calculus
  imports Bacon_Book_Lambda_I_Syntax
    Bacon_Book_Environment_Development.Bacon_Book_Theory_Consistency
begin

section \<open>H in the λI fragment: theory derivability over relevant formulas\<close>

text \<open>
  Definition 9.8 (p.197) restricted to the relevant language of
  Definition 9.2, with the minimal logical signature {→, ∀σ}: a theory
  contains every instance of PC1, PC2, PC3, UI, β and η whose displayed
  formulas are relevant (λI) formulas, and is closed under MP and Gen.
  Negation is the core's literal λp.(p→⊥) applied, which is λI; ⊥ is
  ∀(λp.p), also λI. Gen is stated in the binder form of the full
  calculus, A → ∀x.B from A → B with x ∉ FV(A), together with the extra
  condition x ∈ FV(B) that makes λx.B a λI term; Definition 9.8's
  constant-quantifier form is derived separately. Definition 9.8 reuses
  the rule schemas of Definition 5.1 (pp.97–98) over a general language;
  the ported leaves of this session that cite Definition 5.1 refer to
  those same schemas, here restricted to λI formulas. Every rule instance is
  also an instance of the full calculus book_theory_derivable, so the
  embedding into H is immediate; conservativity of H over this calculus
  on λI formulas is not claimed.
\<close>

abbreviation book_lambda_I_formula :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> bool" where
  "book_lambda_I_formula \<Sigma> G A \<equiv> book_theory_formula \<Sigma> G A \<and> book_lambda_I A"

lemma book_lambda_I_formula_terms:
  "book_lambda_I_formula \<Sigma> G A \<longleftrightarrow> A \<in> book_lambda_I_terms book_minimal_logical_type UNIV \<Sigma> G Prop"
  unfolding book_lambda_I_terms_def by simp

subsection \<open>Relevance of the minimal formula constructors\<close>

lemma book_lambda_I_imp:
  "book_lambda_I (book_imp A B) \<longleftrightarrow> book_lambda_I A \<and> book_lambda_I B"
  unfolding book_imp_def by simp

lemma book_lambda_I_bottom: "book_lambda_I (book_bottom G)"
  unfolding book_bottom_def by simp

lemma book_lambda_I_not_const: "book_lambda_I (book_not_const G)"
  unfolding book_not_const_def book_imp_def book_bottom_def by simp

lemma book_lambda_I_not:
  "book_lambda_I (book_not G A) \<longleftrightarrow> book_lambda_I A"
  unfolding book_not_def by (simp add: book_lambda_I_not_const)

lemma book_lambda_I_all:
  "book_lambda_I (book_all G n A) \<longleftrightarrow> book_lambda_I A \<and> n \<in> named_fv A"
  unfolding book_all_def by simp

subsection \<open>The calculus\<close>

inductive book_lambda_I_derivable ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> 'c book_named_term \<Rightarrow> bool"
  for \<Sigma> :: "'c ssignature" and G :: sgcontext where
  Assumption: "A \<in> S \<Longrightarrow> book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_derivable \<Sigma> G S A"
| PC1: "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G B \<Longrightarrow>
    book_lambda_I_derivable \<Sigma> G S (book_imp A (book_imp B A))"
| PC2: "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G B \<Longrightarrow>
    book_lambda_I_formula \<Sigma> G C \<Longrightarrow> book_lambda_I_derivable \<Sigma> G S
      (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)))"
| PC3: "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G B \<Longrightarrow>
    book_lambda_I_derivable \<Sigma> G S (book_imp (book_imp (book_not G A) (book_not G B)) (book_imp B A))"
| UI: "F \<in> book_lambda_I_terms book_minimal_logical_type UNIV \<Sigma> G (Arr \<sigma> Prop) \<Longrightarrow>
    a \<in> book_lambda_I_terms book_minimal_logical_type UNIV \<Sigma> G \<sigma> \<Longrightarrow>
    book_lambda_I_derivable \<Sigma> G S (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
| Beta: "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G B \<Longrightarrow>
    (named_compatible_step named_beta_contract A B \<or> named_compatible_step named_beta_contract B A) \<Longrightarrow>
    book_lambda_I_derivable \<Sigma> G S (book_imp A B)"
| Eta: "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G B \<Longrightarrow>
    (named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A) \<Longrightarrow>
    book_lambda_I_derivable \<Sigma> G S (book_imp A B)"
| MP: "book_lambda_I_derivable \<Sigma> G S A \<Longrightarrow> book_lambda_I_derivable \<Sigma> G S (book_imp A B) \<Longrightarrow>
    book_lambda_I_formula \<Sigma> G B \<Longrightarrow> book_lambda_I_derivable \<Sigma> G S B"
| Gen: "book_lambda_I_derivable \<Sigma> G S (book_imp A B) \<Longrightarrow>
    book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G B \<Longrightarrow>
    n \<notin> named_fv A \<Longrightarrow> n \<in> named_fv B \<Longrightarrow>
    book_lambda_I_derivable \<Sigma> G S (book_imp A (book_all G n B))"

subsection \<open>Derivations stay inside the λI language\<close>

lemma book_lambda_I_UI_formula:
  assumes predicate: "F \<in> book_lambda_I_terms book_minimal_logical_type UNIV \<Sigma> G (Arr \<sigma> Prop)"
    and argument: "a \<in> book_lambda_I_terms book_minimal_logical_type UNIV \<Sigma> G \<sigma>"
  shows "book_lambda_I_formula \<Sigma> G (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
proof -
  have language: "book_theory_formula \<Sigma> G (book_imp (NApp (NLogical (SBAll \<sigma>)) F) (NApp F a))"
    by (rule book_theory_UI_language[OF book_lambda_I_terms_language[OF predicate]
      book_lambda_I_terms_language[OF argument]])
  show ?thesis using language book_lambda_I_terms_relevant[OF predicate] book_lambda_I_terms_relevant[OF argument]
    by (simp add: book_lambda_I_imp)
qed

theorem book_lambda_I_derivable_formula:
  assumes derivation: "book_lambda_I_derivable \<Sigma> G S A" and rich: "sg_rich G"
  shows "book_lambda_I_formula \<Sigma> G A"
  using derivation
proof (induction rule: book_lambda_I_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.hyps(2))
next
  case PC1
  show ?case using PC1.hyps by (simp add: book_lambda_I_imp book_imp_language)
next
  case PC2
  show ?case using PC2.hyps by (simp add: book_lambda_I_imp book_imp_language)
next
  case PC3
  show ?case using PC3.hyps by (simp add: book_lambda_I_imp book_lambda_I_not book_imp_language book_not_language[OF rich])
next
  case UI
  show ?case by (rule book_lambda_I_UI_formula[OF UI.hyps])
next
  case Beta
  show ?case using Beta.hyps(1,2) by (simp add: book_lambda_I_imp book_imp_language)
next
  case Eta
  show ?case using Eta.hyps(1,2) by (simp add: book_lambda_I_imp book_imp_language)
next
  case MP
  show ?case by (rule MP.hyps(3))
next
  case Gen
  show ?case using Gen.hyps(2,3,5) by (simp add: book_lambda_I_imp book_lambda_I_all book_imp_language book_all_language)
qed


subsection \<open>Language helpers for the λI formula predicate\<close>

lemma book_lambda_I_imp_formula:
  "book_lambda_I_formula \<Sigma> G (book_imp A B) \<longleftrightarrow> book_lambda_I_formula \<Sigma> G A \<and> book_lambda_I_formula \<Sigma> G B"
proof
  assume whole: "book_lambda_I_formula \<Sigma> G (book_imp A B)"
  have relevant: "book_lambda_I A \<and> book_lambda_I B" using whole by (simp add: book_lambda_I_imp)
  have language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NApp (NApp (NLogical SImp) A) B) Prop"
    using whole unfolding book_imp_def by (rule conjunct1)
  obtain \<sigma> where partial: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NApp (NLogical SImp) A) (Arr \<sigma> Prop)"
    and bl: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<sigma>"
    by (rule book_language_App_obtain[OF language]; rule that; assumption)
  obtain \<rho> where op: "book_in_language book_minimal_logical_type UNIV \<Sigma> G (NLogical SImp) (Arr \<rho> (Arr \<sigma> Prop))"
    and al: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<rho>"
    by (rule book_language_App_obtain[OF partial]; rule that; assumption)
  have types: "\<rho> = Prop" "\<sigma> = Prop"
    using book_language_type[OF op] by (auto simp: named_logical_type_iff)
  show "book_lambda_I_formula \<Sigma> G A \<and> book_lambda_I_formula \<Sigma> G B"
    using al bl relevant unfolding types by simp
next
  assume parts: "book_lambda_I_formula \<Sigma> G A \<and> book_lambda_I_formula \<Sigma> G B"
  show "book_lambda_I_formula \<Sigma> G (book_imp A B)" using parts by (simp add: book_lambda_I_imp book_imp_language)
qed

lemma book_lambda_I_imp_language:
  "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G B \<Longrightarrow> book_lambda_I_formula \<Sigma> G (book_imp A B)"
  by (simp add: book_lambda_I_imp_formula)

lemma book_lambda_I_imp_operands:
  "book_lambda_I_formula \<Sigma> G (book_imp A B) \<Longrightarrow> book_lambda_I_formula \<Sigma> G A \<and> book_lambda_I_formula \<Sigma> G B"
  by (simp add: book_lambda_I_imp_formula)

lemma book_lambda_I_not_language:
  "sg_rich G \<Longrightarrow> book_lambda_I_formula \<Sigma> G A \<Longrightarrow> book_lambda_I_formula \<Sigma> G (book_not G A)"
  by (simp add: book_lambda_I_not book_not_language)

lemma book_lambda_I_bottom_language:
  "sg_rich G \<Longrightarrow> book_lambda_I_formula \<Sigma> G (book_bottom G)"
  by (simp add: book_lambda_I_bottom book_bottom_language)

lemma book_lambda_I_all_language:
  "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> n \<in> named_fv A \<Longrightarrow> book_lambda_I_formula \<Sigma> G (book_all G n A)"
  by (simp add: book_lambda_I_all book_all_language)

lemmas book_lambda_I_derivable_language = book_lambda_I_derivable_formula

lemma book_lambda_I_formula_signature:
  "book_lambda_I_formula \<Sigma> G A \<Longrightarrow> named_in_signature \<Sigma> A"
  by (rule book_language_signature[OF conjunct1])

lemma book_lambda_I_imp_weaken:
  assumes derivation: "book_lambda_I_derivable \<Sigma> G S B"
    and al: "book_lambda_I_formula \<Sigma> G A" and bl: "book_lambda_I_formula \<Sigma> G B"
  shows "book_lambda_I_derivable \<Sigma> G S (book_imp A B)"
proof -
  have schema: "book_lambda_I_derivable \<Sigma> G S (book_imp B (book_imp A B))"
    by (rule book_lambda_I_derivable.PC1[OF bl al])
  show ?thesis by (rule book_lambda_I_derivable.MP[OF derivation schema book_lambda_I_imp_language[OF al bl]])
qed

subsection \<open>Monotonicity and embedding into the full calculus\<close>

lemma book_lambda_I_derivable_mono:
  assumes derivation: "book_lambda_I_derivable \<Sigma> G S A" and inclusion: "S \<subseteq> T"
  shows "book_lambda_I_derivable \<Sigma> G T A"
  using derivation inclusion
proof (induction rule: book_lambda_I_derivable.induct)
  case Assumption
  show ?case by (rule book_lambda_I_derivable.Assumption[OF subsetD[OF Assumption.prems Assumption.hyps(1)] Assumption.hyps(2)])
next
  case PC1
  show ?case by (rule book_lambda_I_derivable.PC1[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_lambda_I_derivable.PC2[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_lambda_I_derivable.PC3[OF PC3.hyps])
next
  case UI
  show ?case by (rule book_lambda_I_derivable.UI[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_lambda_I_derivable.Beta[OF Beta.hyps])
next
  case Eta
  show ?case by (rule book_lambda_I_derivable.Eta[OF Eta.hyps])
next
  case MP
  show ?case by (rule book_lambda_I_derivable.MP[OF MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems] MP.hyps(3)])
next
  case Gen
  show ?case by (rule book_lambda_I_derivable.Gen[OF Gen.IH[OF Gen.prems] Gen.hyps(2-5)])
qed

theorem book_lambda_I_derivable_embeds:
  assumes derivation: "book_lambda_I_derivable \<Sigma> G S A"
  shows "book_theory_derivable \<Sigma> G S A"
  using derivation
proof (induction rule: book_lambda_I_derivable.induct)
  case Assumption
  show ?case by (rule book_theory_derivable.Assumption[OF Assumption.hyps(1) conjunct1[OF Assumption.hyps(2)]])
next
  case PC1
  show ?case by (rule book_theory_derivable.PC1[OF conjunct1[OF PC1.hyps(1)] conjunct1[OF PC1.hyps(2)]])
next
  case PC2
  show ?case by (rule book_theory_derivable.PC2[OF conjunct1[OF PC2.hyps(1)] conjunct1[OF PC2.hyps(2)] conjunct1[OF PC2.hyps(3)]])
next
  case PC3
  show ?case by (rule book_theory_derivable.PC3[OF conjunct1[OF PC3.hyps(1)] conjunct1[OF PC3.hyps(2)]])
next
  case UI
  show ?case by (rule book_theory_derivable.UI[OF book_lambda_I_terms_language[OF UI.hyps(1)] book_lambda_I_terms_language[OF UI.hyps(2)]])
next
  case Beta
  show ?case by (rule book_theory_derivable.Beta[OF conjunct1[OF Beta.hyps(1)] conjunct1[OF Beta.hyps(2)] Beta.hyps(3)])
next
  case Eta
  show ?case by (rule book_theory_derivable.Eta[OF conjunct1[OF Eta.hyps(1)] conjunct1[OF Eta.hyps(2)] Eta.hyps(3)])
next
  case MP
  show ?case by (rule book_theory_derivable.MP[OF MP.IH conjunct1[OF MP.hyps(3)]])
next
  case Gen
  show ?case by (rule book_theory_derivable.Gen[OF Gen.IH conjunct1[OF Gen.hyps(2)] conjunct1[OF Gen.hyps(3)] Gen.hyps(4)])
qed

definition book_lambda_I_consistent :: "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c book_named_term set \<Rightarrow> bool" where
  "book_lambda_I_consistent \<Sigma> G S \<longleftrightarrow> \<not> book_lambda_I_derivable \<Sigma> G S (book_bottom G)"

lemma book_lambda_I_consistent_of_theory:
  assumes consistent: "book_theory_consistent \<Sigma> G S"
  shows "book_lambda_I_consistent \<Sigma> G S"
  using consistent book_lambda_I_derivable_embeds unfolding book_lambda_I_consistent_def book_theory_consistent_def by blast

text \<open>
  Every λI derivation is a full-H derivation, so λI consistency follows
  from full consistency. The converse embedding (conservativity of H over
  the λI calculus on λI formulas) is not asserted: a full derivation may
  pass through vacuous abstractions. Semantic results for the λI calculus
  are therefore proved directly in the later theories.
\<close>

end
