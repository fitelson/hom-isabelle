theory Bacon_Source_Named_Nat_Countermodel
  imports Bacon_Source_Named_Countable_Model_Existence
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Consistent_Negation
begin

section \<open>Closed named countermodels with domains contained in ℕ\<close>

text \<open>
  If S ⊬H A for named sentences in a countably declared signature,
  S ∪ {¬A} is consistent and has a named BBK model whose domains
  are subsets of ℕ. The named negation clause makes A false in that
  model. Source: Bacon–Dorr Theorem 3.2 and its countable-domain clause,
  pp.44–45, using the native Figure 2 consequence relation.

  Representation: the ambient constant-name type need not be countable.
  The conclusion keeps the typed-partial-assignment guard. Closedness
  supplies adequacy for A and each premise; it does not type arbitrary
  assignments. No independent consistency hypothesis is added.
  Status: actual nat-carrier countermodels, not minimal-model claims,
  open-formula completeness, or a stronger logical inference rule.
\<close>

theorem paper_named_nat_closed_countermodel:
  fixes \<Sigma> :: "'c ssignature" and S :: "'c paper_named_term set" and A :: "'c paper_named_term"
  assumes countable_signature: "countable (\<Union>\<sigma>. \<Sigma> \<sigma>)"
    and sentences: "paper_named_sentence_set \<Sigma> G S"
    and language: "named_in_language paper_logical_type \<Sigma> G A Prop"
    and closed: "named_fv A = {}" and rich: "sg_rich G"
    and not_derivable: "\<not> paper_named_derivable \<Sigma> G S A"
  shows "\<exists>D :: otype \<Rightarrow> nat set.
    \<exists>J :: nat named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> nat.
    \<exists>V :: nat \<Rightarrow> bool.
      paper_named_bbk_model \<Sigma> G D J V \<and>
      (\<forall>B \<in> S. \<forall>g. named_env_typed D G g \<longrightarrow> V (J g B)) \<and>
      (\<forall>g. named_env_typed D G g \<longrightarrow> \<not> V (J g A))"
proof -
  let ?T = "insert (named_paper_not A) S"
  have enlarged_sentences: "paper_named_sentence_set \<Sigma> G ?T"
    by (rule paper_named_sentence_set_insert_not[OF sentences language closed])
  have consistent: "paper_named_consistent \<Sigma> G ?T"
    by (rule paper_named_consistent_insert_not[OF sentences language closed rich not_derivable])
  obtain D :: "otype \<Rightarrow> nat set" and J V
    where model: "paper_named_bbk_model \<Sigma> G D J V"
    and all_valid: "\<forall>B \<in> ?T. paper_named_bbk_model.named_valid \<Sigma> G D J V B"
    using paper_named_BBK_countable_signature_model_existence[OF countable_signature
      enlarged_sentences rich consistent] by (elim exE conjE)
  interpret Nat: paper_named_bbk_model \<Sigma> G D J V by (rule model)
  have realizes: "\<forall>B \<in> S. \<forall>g. named_env_typed D G g \<longrightarrow> V (J g B)"
  proof (intro ballI allI impI)
    fix B g
    assume member: "B \<in> S" and typed: "named_env_typed D G g"
    have enlarged_member: "B \<in> ?T" by (rule insertI2[OF member])
    have valid_B: "Nat.named_valid B" by (rule bspec[OF all_valid enlarged_member])
    have closed_B: "named_fv B = {}"
      by (rule paper_named_sentence_member_closed[OF sentences member])
    have adequate: "named_adequate g B" by (simp add: named_adequate_def closed_B)
    show "V (J g B)"
      using valid_B typed adequate unfolding Nat.named_valid_def Nat.named_satisfies_def by blast
  qed
  have negative_valid: "Nat.named_valid (named_paper_not A)"
    by (rule bspec[OF all_valid insertI1])
  have falsifies: "\<forall>g. named_env_typed D G g \<longrightarrow> \<not> V (J g A)"
  proof (intro allI impI)
    fix g
    assume typed: "named_env_typed D G g"
    have adequate: "named_adequate g A" by (simp add: named_adequate_def closed)
    have negative_adequate: "named_adequate g (named_paper_not A)"
      by (simp add: named_adequate_def named_paper_not_def closed)
    have negative_truth: "V (J g (named_paper_not A))"
      using negative_valid typed negative_adequate
      unfolding Nat.named_valid_def Nat.named_satisfies_def by blast
    have negation: "V (J g (named_paper_not A)) = (\<not> V (J g A))"
      unfolding named_paper_not_def by (rule Nat.valuation_neg[OF language typed adequate])
    show "\<not> V (J g A)" by (rule iffD1[OF negation negative_truth])
  qed
  show ?thesis by (rule exI[where x=D], rule exI[where x=J], rule exI[where x=V],
    rule conjI[OF model conjI[OF realizes falsifies]])
qed

end
