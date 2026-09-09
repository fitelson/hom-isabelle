theory Bacon_Source_Relational_Nat_Countermodel
  imports Bacon_Source_Relational_Nat_Model_Existence Bacon_Source_Relational_Closed_Countermodel
begin

section \<open>A countermodel to each underivable R sentence\<close>

text \<open>
  If S consists of R sentences and S ⊬H A for an R sentence A,
  the consistent extension S∪{¬A} has an independent BBK model.
  The resulting model makes every member of S valid and A false.
  We use the empty partial assignment to witness nonvalidity; it is
  typed for every domain and adequate for a closed sentence.

  This is a closed-consequence corollary of Bacon–Dorr Theorem 3.2.
  This refinement assumes countably many declared names and has literal
  domains in ℕ. The ambient constant-name type remains unrestricted.
\<close>

theorem paper_R_nat_closed_countermodel:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_named_term set"
  assumes names: "countable (\<Union>\<sigma>. \<Sigma> \<sigma>)" and rich: "paper_R_rich G" and sentences: "paper_R_closed_theory \<Sigma> G S"
    and sentence: "paper_R_sentence \<Sigma> G A"
    and underivable: "\<not> paper_R_named_derivable \<Sigma> G S A"
  shows "\<exists>D :: otype \<Rightarrow> nat set.
    \<exists>J :: nat named_assignment \<Rightarrow>
      'c paper_named_term \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool.
      paper_R_bbk_model \<Sigma> G D J V \<and>
      (\<forall>B\<in>S. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V B) \<and>
      \<not> paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A"
proof -
  have al: "paper_R_in_language \<Sigma> G A Prop"
    by (rule paper_R_sentence_language[OF sentence])
  have ac: "named_fv A = {}" by (rule paper_R_sentence_closed[OF sentence])
  have extended_closed: "paper_R_closed_theory \<Sigma> G (insert (named_paper_not A) S)"
    by (simp only: paper_R_closed_theory_insert; rule conjI[OF paper_R_sentence_not[OF sentence] sentences])
  have extended_consistent: "paper_R_named_consistent \<Sigma> G (insert (named_paper_not A) S)"
    by (rule paper_R_named_consistent_insert_not[OF rich al underivable])
  obtain D :: "otype \<Rightarrow> nat set"
    and J and V where model: "paper_R_bbk_model \<Sigma> G D J V"
    and all_valid: "\<forall>B\<in>insert (named_paper_not A) S.
      paper_R_bbk_model.paper_R_valid \<Sigma> G D J V B"
    using paper_R_BBK_nat_model_existence[OF names rich extended_closed extended_consistent] by blast
  interpret Model: paper_R_bbk_model \<Sigma> G D J V by (rule model)
  have sv: "\<forall>B\<in>S. Model.paper_R_valid B" using all_valid by blast
  have nv: "Model.paper_R_valid (named_paper_not A)" using all_valid by blast
  have typed: "named_env_typed D G (\<lambda>n. None)"
    by (simp add: named_env_typed_def)
  have aa: "named_adequate (\<lambda>n. None) A" by (simp add: named_adequate_def ac)
  have na: "named_adequate (\<lambda>n. None) (named_paper_not A)"
    by (simp add: named_adequate_def named_paper_primitive_fv ac)
  have negative: "V (J (\<lambda>n. None) (named_paper_not A))"
    by (rule Model.paper_R_validE[OF nv typed na])
  have false_A: "\<not> V (J (\<lambda>n. None) A)"
    by (rule iffD1[OF Model.valuation_neg[OF al typed aa]];
      use negative in \<open>simp only: named_paper_not_def\<close>)
  have not_valid: "\<not> Model.paper_R_valid A"
  proof
    assume av: "Model.paper_R_valid A"
    have "V (J (\<lambda>n. None) A)" by (rule Model.paper_R_validE[OF av typed aa])
    with false_A show False by contradiction
  qed
  show ?thesis by (rule exI[where x=D], rule exI[where x=J], rule exI[where x=V],
    rule conjI[OF model conjI[OF sv not_valid]])
qed

end
