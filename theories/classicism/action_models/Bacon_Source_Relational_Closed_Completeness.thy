theory Bacon_Source_Relational_Closed_Completeness
  imports Bacon_Source_Relational_Closed_Countermodel
begin

section \<open>Closed strong completeness for the independent R-BBK semantics\<close>

text \<open>
  S ⊢H A exactly when every independent R-BBK model satisfying S
  also satisfies A, for closed R sentences. The universal quantifiers
  below range over ALL independent models on the displayed carrier,
  not merely the image of the canonical construction. Soundness holds
  on arbitrary value carriers; the constructed countermodel witnesses
  completeness on this one sufficiently large carrier.

  Source: the closed-consequence form of Bacon–Dorr Theorem 3.2.
  This does not assert unrestricted open-consequence completeness,
  the countable-domain refinement, or Classicism completeness.
\<close>

definition paper_R_closed_BBK_consequence ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow>
    'c paper_named_term \<Rightarrow> bool" where
  "paper_R_closed_BBK_consequence \<Sigma> G S A \<longleftrightarrow>
    (\<forall>D :: otype \<Rightarrow> (('c paper_R_henkin_name) paper_named_term set) set.
     \<forall>J :: (('c paper_R_henkin_name) paper_named_term set) named_assignment \<Rightarrow>
       'c paper_named_term \<Rightarrow> ('c paper_R_henkin_name) paper_named_term set.
     \<forall>V :: (('c paper_R_henkin_name) paper_named_term set) \<Rightarrow> bool.
       paper_R_bbk_model \<Sigma> G D J V \<longrightarrow>
       (\<forall>B\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V B) \<longrightarrow>
       paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A)"

theorem paper_R_closed_strong_completeness:
  fixes \<Sigma> :: "'c ssignature"
  assumes rich: "paper_R_rich G" and sentences: "paper_R_closed_theory \<Sigma> G S"
    and sentence: "paper_R_sentence \<Sigma> G A"
  shows "paper_R_named_derivable \<Sigma> G S A \<longleftrightarrow>
    paper_R_closed_BBK_consequence \<Sigma> G S A"
proof
  assume derivation: "paper_R_named_derivable \<Sigma> G S A"
  show "paper_R_closed_BBK_consequence \<Sigma> G S A"
    unfolding paper_R_closed_BBK_consequence_def
  proof (intro allI impI)
    fix D J V
    assume model: "paper_R_bbk_model \<Sigma> G D J V"
      and valid: "\<forall>B\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V B"
    interpret Model: paper_R_bbk_model \<Sigma> G D J V by (rule model)
    show "Model.paper_R_valid A"
      by (rule Model.paper_R_named_derivable_valid[OF derivation]; use valid in blast)
  qed
next
  assume consequence: "paper_R_closed_BBK_consequence \<Sigma> G S A"
  show "paper_R_named_derivable \<Sigma> G S A"
  proof (rule ccontr)
    assume underivable: "\<not> paper_R_named_derivable \<Sigma> G S A"
    have countermodel:
      "\<exists>D :: otype \<Rightarrow> (('c paper_R_henkin_name) paper_named_term set) set.
       \<exists>J V. paper_R_bbk_model \<Sigma> G D J V \<and>
        (\<forall>B\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V B) \<and>
        \<not> paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A"
      by (rule paper_R_closed_countermodel[OF rich sentences sentence underivable])
    show False using consequence countermodel unfolding paper_R_closed_BBK_consequence_def by blast
  qed
qed

end
