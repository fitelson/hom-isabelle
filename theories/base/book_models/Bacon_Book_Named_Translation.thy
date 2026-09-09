theory Bacon_Book_Named_Translation
  imports Bacon_Book_Minimal_Formula_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Logical_Applications
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Raw_Conversion
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Prefix_Roundtrip
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Signature_Conservativity
begin

section \<open>Composing named binding with the book's minimal logical translation\<close>

text \<open>
  Translate the book's named A by encoding its binding at the empty
  stack, then applying the already defined minimal-basis translation.
  In particular → maps to λp.λq.PImp p q, not to an identification
  with the paper's material λ-defined connective.
  Source role: the full minimal language of Chapters 4–5 and its
  intended interpretation clauses in Definition 15.1, pp.314–315.

  Representation: book_named_to_pterm preserves the nonlogical signature
  and exact free names. A language term is typed in every sufficiently
  large finite prefix of G. A raw typed conversion with Σ endpoints is
  first retracted into Σ using rich G, then translated in every prefix
  beyond the conversion proof's support bound.
  Status: syntax, typing and conversion only. No model, H judgment,
  closed Σ-inhabitant or bound on the cardinality of Σ is assumed.
\<close>

definition book_named_to_pterm :: "sgcontext \<Rightarrow> 'c book_named_term \<Rightarrow> 'c pterm" where
  "book_named_to_pterm G A = book_minimal_to_pterm (named_to_source G [] A)"

lemma book_named_translation_Var:
  "book_named_to_pterm G (NVar n) = PVar n"
  by (simp only: book_named_to_pterm_def named_to_source.simps named_index.simps sterm_translation.simps)

lemma book_named_translation_Const:
  "book_named_to_pterm G (NConst c \<sigma>) = PConst c \<sigma>"
  by (simp only: book_named_to_pterm_def named_to_source.simps sterm_translation.simps)

lemma book_named_translation_Logical:
  "book_named_to_pterm G (NLogical l) = book_minimal_logical_translation l"
  by (simp only: book_named_to_pterm_def named_to_source.simps sterm_translation.simps)

lemma book_named_translation_App:
  "book_named_to_pterm G (NApp F A) = PApp (book_named_to_pterm G F) (book_named_to_pterm G A)"
  by (simp only: book_named_to_pterm_def named_to_source.simps sterm_translation.simps)

lemma book_named_translation_Lam:
  "book_named_to_pterm G (NLam n A) =
    PLam (G n) (book_minimal_to_pterm (sclose n (named_to_source G [] A)))"
  by (simp only: book_named_to_pterm_def named_to_source.simps named_to_source_close sterm_translation.simps)

lemma book_named_translation_signature:
  "pterm_in_signature \<Sigma> (book_named_to_pterm G A) = named_in_signature \<Sigma> A"
  by (simp only: book_named_to_pterm_def book_minimal_to_pterm_signature_iff named_to_source_signature)

theorem book_named_translation_fv:
  "pbbk_fv (book_named_to_pterm G A) = named_fv A"
  by (simp only: book_named_to_pterm_def book_minimal_to_pterm_fv named_to_source_empty_fv)

lemma book_named_translation_in_signature:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
  shows "pterm_in_signature \<Sigma> (book_named_to_pterm G A)"
  by (simp only: book_named_translation_signature; rule book_language_signature[OF language])

theorem book_named_translation_language_prefix:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and bound: "source_free_bound (named_to_source G [] A) \<le> m"
  shows "pterm_in_language \<Sigma> (source_prefix G m) (book_named_to_pterm G A) \<tau>"
proof -
  have named_language: "named_in_language book_minimal_logical_type \<Sigma> G A \<tau>"
    by (rule book_language_named[OF language])
  have source_language: "sterm_in_language book_minimal_logical_type \<Sigma>
    (source_prefix G m) (named_to_source G [] A) \<tau>"
    by (rule named_encoding_prefix_language[OF named_language bound])
  show ?thesis unfolding book_named_to_pterm_def
    by (rule iffD2[OF book_minimal_to_pterm_language_iff source_language])
qed

theorem book_named_translation_language_eventual:
  assumes language: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
  shows "\<exists>N. \<forall>m\<ge>N. pterm_in_language \<Sigma> (source_prefix G m) (book_named_to_pterm G A) \<tau>"
proof (rule exI[where x="source_free_bound (named_to_source G [] A)"], intro allI impI)
  fix m
  assume bound: "source_free_bound (named_to_source G [] A) \<le> m"
  show "pterm_in_language \<Sigma> (source_prefix G m) (book_named_to_pterm G A) \<tau>"
    by (rule book_named_translation_language_prefix[OF language bound])
qed

theorem book_named_translation_conversion_eventual:
  assumes rich: "sg_rich G"
    and conversion: "named_raw_beta_eta book_minimal_logical_type G \<tau> A B"
    and left: "book_in_language book_minimal_logical_type UNIV \<Sigma> G A \<tau>"
    and right: "book_in_language book_minimal_logical_type UNIV \<Sigma> G B \<tau>"
  shows "\<exists>N. \<forall>m\<ge>N. pbeta_eta_equiv_in_signature \<Sigma> (source_prefix G m) \<tau>
    (book_named_to_pterm G A) (book_named_to_pterm G B)"
proof -
  have named_left: "named_in_language book_minimal_logical_type \<Sigma> G A \<tau>"
    by (rule book_language_named[OF left])
  have named_right: "named_in_language book_minimal_logical_type \<Sigma> G B \<tau>"
    by (rule book_language_named[OF right])
  have local_conversion: "named_beta_eta_in_language book_minimal_logical_type \<Sigma> G \<tau> A B"
    by (rule named_raw_to_signature[OF rich conversion named_left named_right])
  obtain N where prefixes: "\<forall>m\<ge>N. sbeta_eta_equiv_in_signature book_minimal_logical_type \<Sigma>
    (source_prefix G m) \<tau> (named_to_source G [] A) (named_to_source G [] B)"
    using named_conversion_prefix_eventual[OF local_conversion] by (elim exE)
  show ?thesis
  proof (rule exI[where x=N], intro allI impI)
    fix m
    assume bound: "N \<le> m"
    have source_conversion: "sbeta_eta_equiv_in_signature book_minimal_logical_type \<Sigma>
      (source_prefix G m) \<tau> (named_to_source G [] A) (named_to_source G [] B)"
      using prefixes bound by blast
    show "pbeta_eta_equiv_in_signature \<Sigma> (source_prefix G m) \<tau>
      (book_named_to_pterm G A) (book_named_to_pterm G B)"
      unfolding book_named_to_pterm_def by (rule book_minimal_to_pterm_conversion[OF source_conversion])
  qed
qed

end
