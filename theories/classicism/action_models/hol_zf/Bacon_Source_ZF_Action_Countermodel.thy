theory Bacon_Source_ZF_Action_Countermodel
  imports Bacon_Source_ZF_Hull_Representation
    Bacon_Classicism_Action_Development.Bacon_Source_Relational_Classicism_Counterexample
begin

section \<open>An actual HOL-ZF action countermodel for each native C non-theorem\<close>

text \<open>
  From a typed R formula A not provable in C, first obtain the
  actual bounded C-model Root and its counterassignment. The
  separating-hull representation constructs an action model with
  this SAME root record and preserves its global root truth.
  Failure of global truth therefore supplies a typed adequate
  action assignment at which A fails at the root identity arrow.

  Source: the completeness construction for Theorem 3.23, using
  Theorem 3.12 and Proposition 3.22. This result is relative to
  HOL-ZF and the explicit infinite represented set B bounding
  the declared names. No root model, arrow encoder, representation
  hypothesis or action-model certificate is supplied as a premise.
\<close>

theorem paper_ZF_action_countermodel:
  fixes B :: ZF and \<Sigma> :: "'c ssignature" and A :: "'c paper_named_term"
  assumes infinite: "infinite (explode B)"
    and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of (explode B)"
    and rich: "paper_R_rich G"
    and language: "paper_R_in_language \<Sigma> G A Prop"
    and missing: "\<not> paper_R_classicism_proves \<Sigma> G A"
  shows "\<exists>Obj :: ('c,ZF) paper_bbk_model_data set. \<exists>Ar :: ZF.
    \<exists>s :: ZF \<Rightarrow> ('c,ZF) paper_bbk_model_data. \<exists>t :: ZF \<Rightarrow> ('c,ZF) paper_bbk_model_data.
    \<exists>c :: ZF \<Rightarrow> ZF \<Rightarrow> ZF. \<exists>i :: ('c,ZF) paper_bbk_model_data \<Rightarrow> ZF.
    \<exists>Root :: ('c,ZF) paper_bbk_model_data.
    \<exists>D :: otype \<Rightarrow> ('c,ZF) paper_bbk_model_data \<Rightarrow> ZF.
    \<exists>T :: otype \<Rightarrow> ZF \<Rightarrow> ZF \<Rightarrow> ZF. \<exists>I :: otype \<Rightarrow> 'c \<Rightarrow> ZF.
    \<exists>g :: ZF named_assignment.
      paper_ZF_action_model \<Sigma> G Obj Ar s t c i Root D T I \<and>
      paper_ZF_action_env_typed D G Root g \<and> named_adequate g A \<and>
      \<not> paper_ZF_action_holds Ar s t c i D T I G (i Root) g A"
proof -
  obtain Root :: "('c,ZF) paper_bbk_model_data" and old_g
    where root: "Root \<in> paper_R_bounded_classicism_models \<Sigma> G (explode B)"
    and old_typed: "named_env_typed (paper_bbk_domain Root) G old_g"
    and old_adequate: "named_adequate old_g A"
    and old_false: "\<not> paper_bbk_valuation Root (paper_bbk_denote Root old_g A)"
    by (rule paper_R_bounded_classicism_counterexample[
      where U="explode B" and \<Sigma>=\<Sigma> and G=G and A=A, OF infinite names rich language missing])
  obtain Obj :: "('c,ZF) paper_bbk_model_data set" and Ar s t c i D T I
    where model: "paper_ZF_action_model \<Sigma> G Obj Ar s t c i Root D T I"
    and truth: "\<forall>P. paper_R_in_language \<Sigma> G P Prop \<longrightarrow>
      ((\<forall>g. paper_ZF_action_env_typed D G Root g \<longrightarrow> named_adequate g P \<longrightarrow>
          paper_ZF_action_holds Ar s t c i D T I G (i Root) g P) =
       (\<forall>g. named_env_typed (paper_bbk_domain Root) G g \<longrightarrow> named_adequate g P \<longrightarrow>
          paper_bbk_valuation Root (paper_bbk_denote Root g P)))"
    using paper_ZF_classicism_hull_action_representation[OF infinite names root] by blast
  have old_failure: "\<not> (\<forall>g. named_env_typed (paper_bbk_domain Root) G g \<longrightarrow>
      named_adequate g A \<longrightarrow> paper_bbk_valuation Root (paper_bbk_denote Root g A))"
    using old_typed old_adequate old_false by blast
  have same: "(\<forall>g. paper_ZF_action_env_typed D G Root g \<longrightarrow> named_adequate g A \<longrightarrow>
      paper_ZF_action_holds Ar s t c i D T I G (i Root) g A) =
    (\<forall>g. named_env_typed (paper_bbk_domain Root) G g \<longrightarrow> named_adequate g A \<longrightarrow>
      paper_bbk_valuation Root (paper_bbk_denote Root g A))"
    by (rule mp[OF spec[OF truth] language])
  have action_failure: "\<not> (\<forall>g. paper_ZF_action_env_typed D G Root g \<longrightarrow>
      named_adequate g A \<longrightarrow> paper_ZF_action_holds Ar s t c i D T I G (i Root) g A)"
    by (simp only: same; rule old_failure)
  obtain g :: "ZF named_assignment"
    where typed: "paper_ZF_action_env_typed D G Root g"
    and adequate: "named_adequate g A"
    and false_at: "\<not> paper_ZF_action_holds Ar s t c i D T I G (i Root) g A"
    using action_failure by blast
  show ?thesis
    by (rule exI[where x=Obj], rule exI[where x=Ar], rule exI[where x=s], rule exI[where x=t],
      rule exI[where x=c], rule exI[where x=i], rule exI[where x=Root], rule exI[where x=D],
      rule exI[where x=T], rule exI[where x=I], rule exI[where x=g],
      rule conjI[OF model], rule conjI[OF typed], rule conjI[OF adequate false_at])
qed

text \<open>
  A may have residual free variables. The counterassignment is
  extracted from failure of global validity and is not replaced by
  the empty assignment. The world carrier is explicitly the HOL
  type of original-signature R model records with ZF values; the
  theorem makes no claim that all possible world carriers coincide.
\<close>

end
