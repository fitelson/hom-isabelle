theory Bacon_Source_Relational_Substitution_Syntax
  imports Bacon_Source_Relational_Syntax
    Bacon_Source_Vocabulary_Development.Bacon_Source_Named_Substitution
begin

section \<open>Native R typing of literal substitution\<close>

text \<open>
  This pure leaf keeps substitution typing independent of the HOL-ZF
  evaluator development. Capture-freedom is needed for the semantic
  equation, not for preservation of the fixed variable types.
\<close>

lemma paper_R_subst_type_pure:
  assumes body: "paper_R_has_type G A \<tau>" and payload: "paper_R_has_type G B (G n)"
  shows "paper_R_has_type G (named_subst n B A) \<tau>"
  using body by (induction rule: paper_R_has_type.induct)
    (auto intro: paper_R_has_type.intros payload)

lemma paper_R_subst_language_pure:
  assumes body: "paper_R_in_language \<Sigma> G A \<tau>"
    and payload: "paper_R_in_language \<Sigma> G B (G n)"
  shows "paper_R_in_language \<Sigma> G (named_subst n B A) \<tau>"
  using body payload unfolding paper_R_in_language_def
  by (blast intro: paper_R_subst_type_pure named_subst_signature)

section \<open>Individual-result R terms have no application or abstraction form\<close>

lemma paper_R_logical_type_not_Ind:
  "paper_logical_type l \<noteq> Ind"
  by (cases l) simp_all

lemma paper_R_individual_term_shape:
  assumes typed: "paper_R_has_type G A Ind"
  shows "(\<exists>m. A = NVar m \<and> G m = Ind) \<or> (\<exists>c. A = NConst c Ind)"
  using typed
proof (cases rule: paper_R_has_type.cases)
  case Var
  then show ?thesis by auto
next
  case Const
  then show ?thesis by auto
next
  case (Logical l)
  have different: "paper_logical_type l \<noteq> Ind" by (rule paper_R_logical_type_not_Ind)
  show ?thesis using Logical different by auto
next
  case App
  then show ?thesis by (auto dest: paper_R_result_type)
qed

end
