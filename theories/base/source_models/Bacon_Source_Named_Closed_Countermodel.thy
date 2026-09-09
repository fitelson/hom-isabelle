theory Bacon_Source_Named_Closed_Countermodel
  imports Bacon_Source_BBK_Countermodels Bacon_Source_Named_Tagged_Model
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Local_Correspondence
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Sentence_Sets
begin

section \<open>A nonderivable closed named conclusion has an independent named countermodel\<close>

text \<open>
  If S ⊬H A, where S and A are named sentences of ℒ(Σ), a named
  BBK model satisfies S and falsifies A. Its carrier is explicitly
  otype × ('c phenkin_full_name) pHc_value. Source: the sentence-consequence
  countermodel direction of Bacon–Dorr Theorem 3.2, pp.44–45.

  Representation: native local decoding transfers nonderivability to the
  source language. The existing source countermodel is then sent through
  the checked tagged named-model construction. Completion-truth transport
  recovers every premise and the falsified conclusion.

  Status: S and the constant-name carrier need not be countable, and no
  additional consistency premise is imposed. Truth is asserted for typed
  partial assignments only. Closedness discharges adequacy, not typing.
  The older calibration model is not used by this countermodel construction.
\<close>

theorem paper_named_closed_countermodel:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_named_term set" and A :: "'c paper_named_term"
  assumes sentences: "paper_named_sentence_set \<Sigma> G S"
    and language: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and closed: "named_fv A = {}" and rich: "sg_rich G"
    and not_derivable: "\<not> paper_named_derivable \<Sigma> G S A"
  shows "\<exists>D :: otype \<Rightarrow> (otype \<times> ('c phenkin_full_name) pHc_value) set.
    \<exists>J :: (otype \<times> ('c phenkin_full_name) pHc_value) named_assignment \<Rightarrow>
      'c paper_named_term \<Rightarrow> otype \<times> ('c phenkin_full_name) pHc_value.
    \<exists>V :: (otype \<times> ('c phenkin_full_name) pHc_value) \<Rightarrow> bool.
      paper_named_bbk_model \<Sigma> G D J V \<and>
      (\<forall>B \<in> S. \<forall>g. named_env_typed D G g \<longrightarrow> V (J g B)) \<and>
      (\<forall>g. named_env_typed D G g \<longrightarrow> \<not> V (J g A))"
proof -
  let ?enc = "named_to_source G []"
  have source_sentences: "paper_sentence_set \<Sigma> (image ?enc S)"
    by (rule paper_named_sentence_set_encoding[OF sentences])
  have source_conclusion: "sterm_in_language paper_logical_type \<Sigma> [] (?enc A) Prop"
    by (rule named_to_source_closed_language[OF language closed])
  have source_not_derivable: "\<not> paper_global_derivable \<Sigma> G (image ?enc S) (?enc A)"
  proof
    assume source_derivation: "paper_global_derivable \<Sigma> G (image ?enc S) (?enc A)"
    have native: "paper_named_derivable \<Sigma> G S A"
      by (rule paper_named_derivable_decoding[OF source_derivation rich])
    show False by (rule notE[OF not_derivable native])
  qed
  obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set" and J V
    where source_model: "paper_db_bbk_model \<Sigma> D J V"
    and source_realizes: "\<forall>B \<in> image ?enc S. \<forall>h. V (J h B)"
    and source_falsifies: "\<forall>h. \<not> V (J h (?enc A))"
    using paper_db_BBK_closed_countermodel[OF source_sentences source_conclusion rich source_not_derivable]
    by (elim exE conjE)
  have weak: "paper_db_bbk_structure \<Sigma> D J V"
    by (rule paper_db_bbk_model.axioms(1)[OF source_model])
  interpret Source: paper_db_bbk_structure \<Sigma> D J V by (rule weak)
  have named_model: "paper_named_bbk_model \<Sigma> G (named_tag_domain D)
    (Source.tagged_named_denote G) (\<lambda>v. V (snd v))"
    by (rule Source.paper_db_tagged_named_model[OF rich])
  have realizes: "\<forall>B \<in> S. \<forall>g. named_env_typed (named_tag_domain D) G g \<longrightarrow>
    V (snd (Source.tagged_named_denote G g B))"
  proof (intro ballI allI impI)
    fix B g
    assume member: "B \<in> S" and typed: "named_env_typed (named_tag_domain D) G g"
    have bl: "named_in_language paper_logical_type \<Sigma> G B Prop"
      by (rule paper_named_sentence_member_language[OF sentences member])
    have bc: "named_fv B = {}" by (rule paper_named_sentence_member_closed[OF sentences member])
    have adequate: "named_adequate g B" by (simp add: named_adequate_def bc)
    have untyped: "named_env_typed D G (named_untag_assignment g)"
      by (rule named_untag_assignment_typed[OF typed])
    obtain h where completion: "named_completion D G (named_untag_assignment g) h"
      using named_assignment_completion_exists[OF Source.domain_nonempty untyped] by (elim exE)
    have encoded_member: "?enc B \<in> image ?enc S" by (rule imageI[OF member])
    have every: "\<forall>h. V (J h (?enc B))" by (rule bspec[OF source_realizes encoded_member])
    have truth: "V (J h (?enc B))" by (rule spec[where x=h, OF every])
    have agreement: "V (snd (Source.tagged_named_denote G g B)) = V (J h (?enc B))"
      by (rule Source.paper_db_tagged_named_completion_truth[OF bl typed adequate completion])
    show "V (snd (Source.tagged_named_denote G g B))"
      by (simp only: agreement; rule truth)
  qed
  have falsifies: "\<forall>g. named_env_typed (named_tag_domain D) G g \<longrightarrow>
    \<not> V (snd (Source.tagged_named_denote G g A))"
  proof (intro allI impI)
    fix g
    assume typed: "named_env_typed (named_tag_domain D) G g"
    have adequate: "named_adequate g A" by (simp add: named_adequate_def closed)
    have untyped: "named_env_typed D G (named_untag_assignment g)"
      by (rule named_untag_assignment_typed[OF typed])
    obtain h where completion: "named_completion D G (named_untag_assignment g) h"
      using named_assignment_completion_exists[OF Source.domain_nonempty untyped] by (elim exE)
    have falsehood: "\<not> V (J h (?enc A))" by (rule spec[where x=h, OF source_falsifies])
    have agreement: "V (snd (Source.tagged_named_denote G g A)) = V (J h (?enc A))"
      by (rule Source.paper_db_tagged_named_completion_truth[OF language typed adequate completion])
    show "\<not> V (snd (Source.tagged_named_denote G g A))"
      by (simp only: agreement; rule falsehood)
  qed
  show ?thesis
    by (rule exI[where x="named_tag_domain D"], rule exI[where x="Source.tagged_named_denote G"],
      rule exI[where x="\<lambda>v. V (snd v)"], rule conjI[OF named_model conjI[OF realizes falsifies]])
qed

end
