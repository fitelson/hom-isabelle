theory Bacon_Source_Named_Sentence_Sets
  imports Bacon_Source_Named_Closed_Roundtrip Bacon_Source_Sentence_Sets
begin

section \<open>Sentence sets in a fixed named variable stock\<close>

text \<open>
  S is a set of formulas of ℒ(Σ) with no free named variables.
  Source: the sentence-set formulation of Bacon–Dorr Theorem 3.2,
  pp.44–45, and the sentence definition in §1.1, p.5.

  Isabelle representation. The predicate keeps G explicit in every
  member's typing guard. Encoding each member with that same G yields
  a sentence set in the empty source frame. Neither richness nor any
  finiteness/countability condition on S or Σ is needed here. These are
  language and closure conditions only, not consistency, theoremhood,
  deductive closure, or existence of a model.
\<close>

definition paper_named_sentence_set ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> bool" where
  "paper_named_sentence_set \<Sigma> G S \<longleftrightarrow>
    (\<forall>A \<in> S. named_in_language paper_logical_type \<Sigma> G A Prop \<and> named_fv A = {})"

lemma paper_named_sentence_set_member:
  assumes sentences: "paper_named_sentence_set \<Sigma> G S" and member: "A \<in> S"
  shows "named_in_language paper_logical_type \<Sigma> G A Prop \<and> named_fv A = {}"
  by (rule bspec[OF sentences[unfolded paper_named_sentence_set_def] member])

lemma paper_named_sentence_member_language:
  "paper_named_sentence_set \<Sigma> G S \<Longrightarrow> A \<in> S \<Longrightarrow>
    named_in_language paper_logical_type \<Sigma> G A Prop"
  by (rule conjunct1, rule paper_named_sentence_set_member; assumption)

lemma paper_named_sentence_member_closed:
  "paper_named_sentence_set \<Sigma> G S \<Longrightarrow> A \<in> S \<Longrightarrow> named_fv A = {}"
  by (rule conjunct2, rule paper_named_sentence_set_member; assumption)

lemma paper_named_sentence_encoding:
  assumes language: "named_in_language paper_logical_type \<Sigma> G A Prop" and closed: "named_fv A = {}"
  shows "sterm_in_language paper_logical_type \<Sigma> [] (named_to_source G [] A) Prop \<and>
    sfv (named_to_source G [] A) = {}"
  by (rule conjI[OF named_to_source_closed_language[OF language closed] named_to_source_closed[OF closed]])

theorem paper_named_sentence_set_encoding:
  assumes sentences: "paper_named_sentence_set \<Sigma> G S"
  shows "paper_sentence_set \<Sigma> (named_to_source G [] ` S)"
proof (unfold paper_sentence_set_def, rule ballI)
  fix B
  assume encoded_member: "B \<in> named_to_source G [] ` S"
  obtain A where encoded: "B = named_to_source G [] A" and member: "A \<in> S"
    using encoded_member by (elim imageE)
  have language: "named_in_language paper_logical_type \<Sigma> G A Prop"
    by (rule paper_named_sentence_member_language[OF sentences member])
  have closed: "named_fv A = {}" by (rule paper_named_sentence_member_closed[OF sentences member])
  show "sterm_in_language paper_logical_type \<Sigma> [] B Prop"
    by (simp only: encoded; rule named_to_source_closed_language[OF language closed])
qed

end
