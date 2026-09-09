theory Bacon_Book_Theory_Conversion
  imports Bacon_Book_Theory_Propositional_Basics
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Alpha_Conversion
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Raw_Conversion
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Signature_Conservativity
begin

section \<open>Chaining implications with the printed propositional rules\<close>

lemma book_theory_imp_trans:
  assumes al: "book_theory_formula \<Sigma> G A" and bl: "book_theory_formula \<Sigma> G B"
    and cl: "book_theory_formula \<Sigma> G C"
    and ab: "book_theory_derivable \<Sigma> G S (book_imp A B)"
    and bc: "book_theory_derivable \<Sigma> G S (book_imp B C)"
  shows "book_theory_derivable \<Sigma> G S (book_imp A C)"
proof -
  have bcl: "book_theory_formula \<Sigma> G (book_imp B C)" by (rule book_imp_language[OF bl cl])
  have abl: "book_theory_formula \<Sigma> G (book_imp A B)" by (rule book_imp_language[OF al bl])
  have acl: "book_theory_formula \<Sigma> G (book_imp A C)" by (rule book_imp_language[OF al cl])
  have tail: "book_theory_formula \<Sigma> G (book_imp (book_imp A B) (book_imp A C))"
    by (rule book_imp_language[OF abl acl])
  have lifted: "book_theory_derivable \<Sigma> G S (book_imp A (book_imp B C))"
    by (rule book_theory_imp_weaken[OF bc al bcl])
  have schema: "book_theory_derivable \<Sigma> G S
    (book_imp (book_imp A (book_imp B C)) (book_imp (book_imp A B) (book_imp A C)))"
    by (rule book_theory_derivable.PC2[OF al bl cl])
  have implication: "book_theory_derivable \<Sigma> G S (book_imp (book_imp A B) (book_imp A C))"
    by (rule book_theory_derivable.MP[OF lifted schema tail])
  show ?thesis by (rule book_theory_derivable.MP[OF ab implication acl])
qed

section \<open>Conversion chains yield implications in both directions\<close>

text \<open>
  βη-equivalent formulas imply one another. The proof chains the
  printed immediate β/η implications using PC1, PC2 and MP; it adds
  no transitive-conversion or α inference rule. Source: Bacon's
  consequence of the conversion schemas discussed on p.103.

  The paired induction is necessary: symmetry exchanges two already
  proved implications, rather than illegitimately reversing just one.
  All chain nodes remain in the declared language. Raw conversion
  with only guarded endpoints is handled separately by signature
  retraction under the rich-stock assumption.
\<close>

theorem book_theory_conversion_pair:
  assumes conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G \<tau> A B"
    and proposition_type: "\<tau> = Prop"
  shows "book_theory_derivable \<Sigma> G S (book_imp A B) \<and>
    book_theory_derivable \<Sigma> G S (book_imp B A)"
  using conversion proposition_type
proof (induction rule: named_beta_eta_in_language.induct)
  case (Refl A \<tau>)
  have al: "book_theory_formula \<Sigma> G A" using Refl.hyps by (simp only: book_language_UNIV Refl.prems)
  show ?case by (rule conjI; rule book_theory_imp_refl[OF al])
next
  case (Beta A \<tau> B)
  have al: "book_theory_formula \<Sigma> G A" using Beta.hyps(1) by (simp only: book_language_UNIV Beta.prems)
  have bl: "book_theory_formula \<Sigma> G B" using Beta.hyps(2) by (simp only: book_language_UNIV Beta.prems)
  have forward: "book_theory_derivable \<Sigma> G S (book_imp A B)"
    by (rule book_theory_derivable.Beta[OF al bl], rule disjI1, rule Beta.hyps(3))
  have backward: "book_theory_derivable \<Sigma> G S (book_imp B A)"
    by (rule book_theory_derivable.Beta[OF bl al], rule disjI2, rule Beta.hyps(3))
  show ?case by (rule conjI[OF forward backward])
next
  case (Eta A \<tau> B)
  have al: "book_theory_formula \<Sigma> G A" using Eta.hyps(1) by (simp only: book_language_UNIV Eta.prems)
  have bl: "book_theory_formula \<Sigma> G B" using Eta.hyps(2) by (simp only: book_language_UNIV Eta.prems)
  have forward: "book_theory_derivable \<Sigma> G S (book_imp A B)"
    by (rule book_theory_derivable.Eta[OF al bl], rule disjI1, rule Eta.hyps(3))
  have backward: "book_theory_derivable \<Sigma> G S (book_imp B A)"
    by (rule book_theory_derivable.Eta[OF bl al], rule disjI2, rule Eta.hyps(3))
  show ?case by (rule conjI[OF forward backward])
next
  case (Sym \<tau> A B)
  show ?case using Sym.IH[OF Sym.prems] by blast
next
  case (Trans \<tau> A B C)
  have first: "book_theory_derivable \<Sigma> G S (book_imp A B) \<and>
    book_theory_derivable \<Sigma> G S (book_imp B A)" by (rule Trans.IH(1)[OF Trans.prems])
  have second: "book_theory_derivable \<Sigma> G S (book_imp B C) \<and>
    book_theory_derivable \<Sigma> G S (book_imp C B)" by (rule Trans.IH(2)[OF Trans.prems])
  have al: "book_theory_formula \<Sigma> G A" and bl: "book_theory_formula \<Sigma> G B"
    using named_beta_eta_languages[OF Trans.hyps(1)] by (auto simp: book_language_UNIV Trans.prems)
  have cl: "book_theory_formula \<Sigma> G C"
    using named_beta_eta_languages[OF Trans.hyps(2)] by (auto simp: book_language_UNIV Trans.prems)
  show ?case by (rule conjI,
    rule book_theory_imp_trans[OF al bl cl conjunct1[OF first] conjunct1[OF second]],
    rule book_theory_imp_trans[OF cl bl al conjunct2[OF second] conjunct2[OF first]])
qed

theorem book_theory_conversion_transport:
  assumes conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop A B"
    and derivation: "book_theory_derivable \<Sigma> G S A"
  shows "book_theory_derivable \<Sigma> G S B"
proof -
  have bl: "book_theory_formula \<Sigma> G B"
    using named_beta_eta_languages[OF conversion] by (auto simp: book_language_UNIV)
  have implication: "book_theory_derivable \<Sigma> G S (book_imp A B)"
    by (rule conjunct1[OF book_theory_conversion_pair[OF conversion refl]])
  show ?thesis by (rule book_theory_derivable.MP[OF derivation implication bl])
qed

theorem book_theory_conversion_iff:
  assumes conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G Prop A B"
  shows "book_theory_derivable \<Sigma> G S A \<longleftrightarrow> book_theory_derivable \<Sigma> G S B"
  by (rule iffI, rule book_theory_conversion_transport[OF conversion], assumption,
    rule book_theory_conversion_transport[OF named_beta_eta_in_language.Sym[OF conversion]], assumption)

theorem book_theory_raw_conversion_iff:
  assumes rich: "sg_rich G" and al: "book_theory_formula \<Sigma> G A" and bl: "book_theory_formula \<Sigma> G B"
    and conversion: "named_raw_beta_eta book_minimal_logical_type G Prop A B"
  shows "book_theory_derivable \<Sigma> G S A \<longleftrightarrow> book_theory_derivable \<Sigma> G S B"
  by (rule book_theory_conversion_iff, rule named_raw_to_signature[
    OF rich conversion book_language_named[OF al] book_language_named[OF bl]])

theorem book_theory_alpha_iff:
  assumes alpha: "named_alpha G A B" and al: "book_theory_formula \<Sigma> G A"
  shows "book_theory_derivable \<Sigma> G S A \<longleftrightarrow> book_theory_derivable \<Sigma> G S B"
  by (rule book_theory_conversion_iff, rule named_alpha_implies_beta_eta[OF alpha book_language_named[OF al]])

end
