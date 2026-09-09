theory Bacon_Source_BBK_Strong_Completeness
  imports Bacon_Source_BBK_Closed_Soundness Bacon_Source_BBK_Countermodels
begin

section \<open>Closed-sentence consequence in the first-class finite-frame semantics\<close>

text \<open>
  For sentences S,A in the declared paper language and a rich variable
  stock, S ⊢H A iff every finite-frame source structure satisfying S
  satisfies A. Soundness has already been proved on arbitrary semantic
  carriers; failure of derivability gives a countermodel on the displayed
  canonical carrier.

  Representation: the consequence predicate below quantifies over all
  independently specified domain families, interpretations, and valuations
  on that fixed carrier. It is not an alias for target consequence or a
  restriction to models produced by the canonical construction. HOL does
  not quantify over carrier types here. Source: the sentence-consequence
  form of Bacon–Dorr Theorem 3.2, within the finite-frame representation.

  Named syntax/α and adequate-assignment correspondence are still required
  before identifying this result with the published named-model statement.
  The book's different primitive basis and Leibniz-identity semantics are
  not covered by this theorem.
\<close>

definition paper_db_canonical_consequence ::
  "'c ssignature \<Rightarrow> 'c paper_term set \<Rightarrow> 'c paper_term \<Rightarrow> bool" where
  "paper_db_canonical_consequence \<Sigma> S A \<longleftrightarrow>
    (\<forall>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
     \<forall>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
       'c paper_term \<Rightarrow> ('c phenkin_full_name) pHc_value.
     \<forall>V :: ('c phenkin_full_name) pHc_value \<Rightarrow> bool.
       paper_db_bbk_structure \<Sigma> D J V \<longrightarrow>
       (\<forall>B \<in> S. \<forall>g. V (J g B)) \<longrightarrow> (\<forall>g. V (J g A)))"

theorem paper_db_closed_strong_completeness:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_term set" and A :: "'c paper_term"
  assumes sentences: "paper_sentence_set \<Sigma> S"
    and conclusion: "sterm_in_language paper_logical_type \<Sigma> [] A Prop"
    and rich: "sg_rich G"
  shows "paper_global_derivable \<Sigma> G S A \<longleftrightarrow> paper_db_canonical_consequence \<Sigma> S A"
proof
  assume derivation: "paper_global_derivable \<Sigma> G S A"
  show "paper_db_canonical_consequence \<Sigma> S A"
  proof (unfold paper_db_canonical_consequence_def, intro allI)
    fix D J V
    show "paper_db_bbk_structure \<Sigma> D J V \<longrightarrow>
      (\<forall>B \<in> S. \<forall>g. V (J g B)) \<longrightarrow> (\<forall>g. V (J g A))"
    proof (intro impI)
      assume model: "paper_db_bbk_structure \<Sigma> D J V"
        and realizes: "\<forall>B \<in> S. \<forall>g. V (J g B)"
      interpret Source: paper_db_bbk_structure \<Sigma> D J V by (rule model)
      show "\<forall>g. V (J g A)"
      proof (rule allI)
        fix g
        show "V (J g A)"
          by (rule Source.paper_db_closed_set_soundness[OF sentences conclusion derivation])
            (use realizes in blast)
      qed
    qed
  qed
next
  assume consequence: "paper_db_canonical_consequence \<Sigma> S A"
  show "paper_global_derivable \<Sigma> G S A"
  proof (rule ccontr)
    assume not_derivable: "\<not> paper_global_derivable \<Sigma> G S A"
    obtain D :: "otype \<Rightarrow> ('c phenkin_full_name) pHc_value set"
      and J V where model: "paper_db_bbk_model \<Sigma> D J V"
      and realizes: "\<forall>B \<in> S. \<forall>g. V (J g B)"
      and falsifies: "\<forall>g. \<not> V (J g A)"
      using paper_db_BBK_closed_countermodel[OF sentences conclusion rich not_derivable]
      by (elim exE conjE)
    have weak_model: "paper_db_bbk_structure \<Sigma> D J V"
      by (rule paper_db_bbk_model.axioms(1)[OF model])
    have all_models: "\<forall>D :: otype \<Rightarrow> ('c phenkin_full_name) pHc_value set.
      \<forall>J :: (nat \<Rightarrow> ('c phenkin_full_name) pHc_value) \<Rightarrow>
        'c paper_term \<Rightarrow> ('c phenkin_full_name) pHc_value.
      \<forall>V :: ('c phenkin_full_name) pHc_value \<Rightarrow> bool.
        paper_db_bbk_structure \<Sigma> D J V \<longrightarrow>
        (\<forall>B \<in> S. \<forall>g. V (J g B)) \<longrightarrow> (\<forall>g. V (J g A))"
      using consequence unfolding paper_db_canonical_consequence_def .
    have this_model: "paper_db_bbk_structure \<Sigma> D J V \<longrightarrow>
      (\<forall>B \<in> S. \<forall>g. V (J g B)) \<longrightarrow> (\<forall>g. V (J g A))"
      by (rule spec[where x=V, OF spec[where x=J, OF spec[where x=D, OF all_models]]])
    have all_true: "\<forall>g. V (J g A)" by (rule mp[OF mp[OF this_model weak_model] realizes])
    have yes: "V (J (\<lambda>_. undefined) A)" by (rule spec[OF all_true])
    have no: "\<not> V (J (\<lambda>_. undefined) A)" by (rule spec[OF falsifies])
    show False by (rule notE[OF no yes])
  qed
qed

end
