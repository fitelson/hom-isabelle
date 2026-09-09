theory Bacon_Book_Theory_Soundness
  imports Bacon_Book_Theory_Derivation Bacon_Book_Theory_Axiom_Soundness
begin

section \<open>The immediate conversion schemas have the required semantics\<close>

lemma book_beta_immediate_raw:
  assumes al: "book_theory_formula \<Sigma> G A" and bl: "book_theory_formula \<Sigma> G B"
    and step: "named_compatible_step named_beta_contract A B \<or> named_compatible_step named_beta_contract B A"
  shows "named_raw_beta_eta book_minimal_logical_type G Prop A B"
  using step
proof
  assume forward: "named_compatible_step named_beta_contract A B"
  show ?thesis by (rule named_conversion_to_raw, rule named_beta_eta_in_language.Beta[
    OF book_language_named[OF al] book_language_named[OF bl] forward])
next
  assume backward: "named_compatible_step named_beta_contract B A"
  show ?thesis by (rule named_conversion_to_raw, rule named_beta_eta_in_language.Sym,
    rule named_beta_eta_in_language.Beta[OF book_language_named[OF bl] book_language_named[OF al] backward])
qed

lemma book_eta_immediate_raw:
  assumes al: "book_theory_formula \<Sigma> G A" and bl: "book_theory_formula \<Sigma> G B"
    and step: "named_compatible_step named_eta_contract A B \<or> named_compatible_step named_eta_contract B A"
  shows "named_raw_beta_eta book_minimal_logical_type G Prop A B"
  using step
proof
  assume forward: "named_compatible_step named_eta_contract A B"
  show ?thesis by (rule named_conversion_to_raw, rule named_beta_eta_in_language.Eta[
    OF book_language_named[OF al] book_language_named[OF bl] forward])
next
  assume backward: "named_compatible_step named_eta_contract B A"
  show ?thesis by (rule named_conversion_to_raw, rule named_beta_eta_in_language.Sym,
    rule named_beta_eta_in_language.Eta[OF book_language_named[OF bl] book_language_named[OF al] backward])
qed

section \<open>Soundness of the book's independent theory derivations\<close>

text \<open>
  If every member of S is true in a model, every formula obtained from
  S by the book's theory rules is true there. The proof has exactly
  the Assumption, PC1, PC2, PC3, UI, β, η, MP and Gen cases.
  Source: Definition 5.1, pp.97–98, and Theorem 15.1, p.318.

  Model scope: full F/full λ, the minimal basis, and witnessed logical
  values. The separate Bacon_Book_Logic leaf uses proved substitution
  admissibility to identify the least theory with the least logic H
  (Comprehension Check 5.1, p.102). This soundness theorem alone does not
  make that identification or assert unrestricted open-assumption deduction.
  No paper-H, C, CE, CEV or alternative semantic interface is used.
\<close>

context book_full_minimal_model
begin

theorem book_theory_soundness:
  assumes rich: "sg_rich stock"
    and derivation: "book_theory_derivable signature stock S A"
    and assumptions_valid: "\<And>B. B \<in> S \<Longrightarrow> book_formula_valid domain stock denote V B"
  shows "book_formula_valid domain stock denote V A"
  using derivation assumptions_valid
proof (induction rule: book_theory_derivable.induct)
  case Assumption
  show ?case by (rule Assumption.prems[OF Assumption.hyps(1)])
next
  case PC1
  show ?case by (rule book_PC1_valid[OF PC1.hyps])
next
  case PC2
  show ?case by (rule book_PC2_valid[OF PC2.hyps])
next
  case PC3
  show ?case by (rule book_PC3_valid[OF rich PC3.hyps])
next
  case UI
  show ?case by (rule book_UI_valid[OF UI.hyps])
next
  case Beta
  show ?case by (rule book_conversion_valid[OF Beta.hyps(1,2) book_beta_immediate_raw[OF Beta.hyps]])
next
  case Eta
  show ?case by (rule book_conversion_valid[OF Eta.hyps(1,2) book_eta_immediate_raw[OF Eta.hyps]])
next
  case MP
  show ?case by (rule book_MP_valid[OF book_theory_derivable_language[OF MP.hyps(1) rich] MP.hyps(3)
    MP.IH(1)[OF MP.prems] MP.IH(2)[OF MP.prems]])
next
  case Gen
  show ?case by (rule book_Gen_valid[OF Gen.hyps(2,3,4) Gen.IH[OF Gen.prems]])
qed

corollary book_axiom_generated_soundness:
  assumes rich: "sg_rich stock" and derivation: "book_theory_derivable signature stock {} A"
  shows "book_formula_valid domain stock denote V A"
  by (rule book_theory_soundness[OF rich derivation]) simp

definition book_model_truths where
  "book_model_truths = {A. book_theory_formula signature stock A \<and> book_formula_valid domain stock denote V A}"

theorem book_model_truths_form_theory:
  assumes rich: "sg_rich stock"
  shows "book_higher_order_theory signature stock book_model_truths"
proof (unfold book_higher_order_theory_def, rule conjI)
  show "\<forall>A \<in> book_model_truths. book_theory_formula signature stock A"
    by (simp add: book_model_truths_def)
next
  show "\<forall>A. book_theory_derivable signature stock book_model_truths A \<longrightarrow> A \<in> book_model_truths"
  proof (intro allI impI)
    fix A
    assume derivation: "book_theory_derivable signature stock book_model_truths A"
    have language: "book_theory_formula signature stock A"
      by (rule book_theory_derivable_language[OF derivation rich])
    have valid: "book_formula_valid domain stock denote V A"
    proof (rule book_theory_soundness[OF rich derivation])
      fix B
      assume member: "B \<in> book_model_truths"
      show "book_formula_valid domain stock denote V B" using member by (simp add: book_model_truths_def)
    qed
    show "A \<in> book_model_truths" by (simp only: book_model_truths_def mem_Collect_eq; rule conjI[OF language valid])
  qed
qed

end

end
