theory Bacon_Source_Relational_Nat_Completeness
  imports Bacon_Source_Relational_Nat_Countermodel
begin

section \<open>Closed strong completeness for the independent R-BBK semantics\<close>

text \<open>
  For a countable declared signature, S ⊢H A exactly when every
  independent R-BBK model with domains in ℕ satisfying S satisfies A.
  Both S and A consist of closed sentences. The semantic quantifiers
  range over ALL independent models on ℕ, not only recoded images.

  Source: the countable closed-consequence corollary of Bacon–Dorr
  Theorem 3.2, pp.44–45. Soundness uses arbitrary independent R models;
  completeness uses the separately constructed ℕ countermodel. No
  countability of the ambient constant-name type is assumed.
\<close>

definition paper_R_nat_BBK_consequence ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow>
    'c paper_named_term \<Rightarrow> bool" where
  "paper_R_nat_BBK_consequence \<Sigma> G S A \<longleftrightarrow>
    (\<forall>D :: otype \<Rightarrow> nat set.
     \<forall>J :: nat named_assignment \<Rightarrow>
       'c paper_named_term \<Rightarrow> nat.
     \<forall>V :: nat \<Rightarrow> bool.
       paper_R_bbk_model \<Sigma> G D J V \<longrightarrow>
       (\<forall>B\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V B) \<longrightarrow>
       paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A)"

theorem paper_R_nat_closed_strong_completeness:
  fixes \<Sigma> :: "'c ssignature"
  assumes names: "countable (\<Union>\<sigma>. \<Sigma> \<sigma>)" and rich: "paper_R_rich G" and sentences: "paper_R_closed_theory \<Sigma> G S"
    and sentence: "paper_R_sentence \<Sigma> G A"
  shows "paper_R_named_derivable \<Sigma> G S A \<longleftrightarrow>
    paper_R_nat_BBK_consequence \<Sigma> G S A"
proof
  assume derivation: "paper_R_named_derivable \<Sigma> G S A"
  show "paper_R_nat_BBK_consequence \<Sigma> G S A"
    unfolding paper_R_nat_BBK_consequence_def
  proof (intro allI impI)
    fix D J V
    assume model: "paper_R_bbk_model \<Sigma> G D J V"
      and valid: "\<forall>B\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V B"
    interpret Model: paper_R_bbk_model \<Sigma> G D J V by (rule model)
    show "Model.paper_R_valid A"
      by (rule Model.paper_R_named_derivable_valid[OF derivation]; use valid in blast)
  qed
next
  assume consequence: "paper_R_nat_BBK_consequence \<Sigma> G S A"
  show "paper_R_named_derivable \<Sigma> G S A"
  proof (rule ccontr)
    assume underivable: "\<not> paper_R_named_derivable \<Sigma> G S A"
    have countermodel:
      "\<exists>D :: otype \<Rightarrow> nat set.
       \<exists>J V. paper_R_bbk_model \<Sigma> G D J V \<and>
        (\<forall>B\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V B) \<and>
        \<not> paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A"
      by (rule paper_R_nat_closed_countermodel[OF names rich sentences sentence underivable])
    show False using consequence countermodel unfolding paper_R_nat_BBK_consequence_def by blast
  qed
qed

end
