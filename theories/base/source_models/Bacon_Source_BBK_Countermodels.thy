theory Bacon_Source_BBK_Countermodels
  imports Bacon_Source_BBK_Model_Existence
    Bacon_Parametric_Canonical_Development.Bacon_Parametric_BBK_Strong_Completeness
begin

section \<open>A source sentence not derivable from S has a countermodel\<close>

text \<open>
  If S ⊬H A, for sentences S,A of ℒ(Σ), there is a model satisfying
  every member of S and falsifying A. Source role: the sentence-consequence
  countermodel direction of Bacon–Dorr Theorem 3.2, pp.44–45.

  Isabelle representation: closed-set proof correspondence gives target
  nonderivability. The target countermodel theorem supplies actual D,J,V
  on the enlarged canonical carrier; pulling J back along paper_to_pterm
  verifies the independent source finite-frame interface.

  Precise status: a countermodel in paper_db_bbk_model, including its
  explicit de Bruijn renaming coherence. The name carrier and sentence set
  have no cardinality restriction, but the displayed semantic carrier is
  the canonical one, not necessarily nat. Subsequent leaves prove soundness
  for every weak finite-frame structure and combine it with this theorem
  for carrier-explicit closed strong completeness. Equivalence with adequate
  named assignments, the book-basis theorem, and recovery of arbitrary
  original target interpretations are not asserted. Since S,A are closed,
  truth and falsity hold for every assignment g without a frame guard.
\<close>

theorem paper_db_BBK_closed_countermodel:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_term set" and A :: "'c paper_term"
  assumes sentences: "paper_sentence_set \<Sigma> S"
    and conclusion: "sterm_in_language paper_logical_type \<Sigma> [] A Prop"
    and rich: "sg_rich G"
    and not_derivable: "\<not> paper_global_derivable \<Sigma> G S A"
  shows "\<exists>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
    \<exists>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
      'c paper_term \<Rightarrow> ('c phenkin_full_name) pHc_value.
    \<exists>V :: ('c phenkin_full_name) pHc_value \<Rightarrow> bool.
      paper_db_bbk_model \<Sigma> D J V \<and>
      (\<forall>B \<in> S. \<forall>g. V (J g B)) \<and> (\<forall>g. \<not> V (J g A))"
proof -
  have typed: "pH_typed_theory \<Sigma> [] (image paper_to_pterm S)"
    by (rule paper_sentence_set_target[OF sentences])
  have target_language: "pterm_in_language \<Sigma> [] (paper_to_pterm A) Prop"
    by (rule iffD2[OF paper_to_pterm_language_iff conclusion])
  have target_not_derivable:
    "\<not> pH_set_derivable \<Sigma> [] (image paper_to_pterm S) (paper_to_pterm A)"
  proof (rule notI)
    assume target: "pH_set_derivable \<Sigma> [] (image paper_to_pterm S) (paper_to_pterm A)"
    have source: "paper_global_derivable \<Sigma> G S A"
      by (rule iffD2[OF paper_closed_set_derivable_iff[OF sentences conclusion rich] target])
    show False by (rule notE[OF not_derivable source])
  qed
  obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set"
    and J V where model: "pbbk_model \<Sigma> D J V"
    and realizes: "\<forall>B \<in> image paper_to_pterm S. \<forall>g. V (J g B)"
    and falsifies: "\<forall>g. \<not> V (J g (paper_to_pterm A))"
    using pH_BBK_closed_countermodel[OF typed target_language target_not_derivable]
    by (elim exE conjE)
  have source_model: "paper_db_bbk_model \<Sigma> D (\<lambda>g B. J g (paper_to_pterm B)) V"
    by (rule pbbk_to_paper_db_model[OF model])
  have source_realizes: "\<forall>B \<in> S. \<forall>g. V (J g (paper_to_pterm B))"
  proof (rule ballI)
    fix B
    assume member: "B \<in> S"
    have translated_member: "paper_to_pterm B \<in> image paper_to_pterm S"
      by (rule imageI[OF member])
    show "\<forall>g. V (J g (paper_to_pterm B))" by (rule bspec[OF realizes translated_member])
  qed
  show ?thesis
    by (rule exI[where x=D], rule exI[where x="\<lambda>g B. J g (paper_to_pterm B)"],
      rule exI[where x=V], rule conjI[OF source_model conjI[OF source_realizes falsifies]])
qed

end
