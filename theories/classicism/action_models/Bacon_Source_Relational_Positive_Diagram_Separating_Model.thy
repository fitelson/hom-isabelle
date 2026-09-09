theory Bacon_Source_Relational_Positive_Diagram_Separating_Model
  imports Bacon_Source_Relational_Positive_Diagram_Consistency
    Bacon_Source_Relational_H_Theory_Closed_Extension_Model
begin

section \<open>An actual target satisfying the positive diagram and a separating negation\<close>

text \<open>
  Let M validate an H-theory T closed under PE. For CLOSED formulas
  P,Q with different denotations in M, construct a target N validating
  T, the actual positive closed identity diagram Δ(M), and ¬(P↔Q).
  The added set Δ(M)∪{¬(P↔Q)} consists of closed sentences and
  its union with T is consistent by the proved separating argument.
  The closed-extension model theorem therefore supplies N.

  Source: Theorem 3.12, p.51–52 n.73. T itself may contain open
  formulas. We neither assume that the enlarged premise set is an
  H-theory nor ask M to validate the separating negation. N has the
  displayed native Henkin term-class carrier, at unchanged signature
  and variable stock. This leaf constructs the target, not yet the
  homomorphism from a naming expansion or a prescribed-carrier target.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_positive_diagram_separating_model:
  assumes theory_h: "paper_R_H_theory signature stock T"
    and pe: "paper_R_PE_closed signature stock T"
    and theory_valid: "\<And>A. A \<in> T \<Longrightarrow> paper_R_valid A"
    and pl: "paper_R_in_language signature stock P Prop"
    and ql: "paper_R_in_language signature stock Q Prop"
    and pc: "named_fv P = {}" and qc: "named_fv Q = {}"
    and different: "denote Map.empty P \<noteq> denote Map.empty Q"
  shows "\<exists>E :: otype \<Rightarrow> (('c paper_R_henkin_name) paper_named_term set) set.
    \<exists>K :: (('c paper_R_henkin_name) paper_named_term set) named_assignment \<Rightarrow>
      'c paper_named_term \<Rightarrow> ('c paper_R_henkin_name) paper_named_term set.
    \<exists>W :: (('c paper_R_henkin_name) paper_named_term set) \<Rightarrow> bool.
      paper_R_bbk_model signature stock E K W \<and>
      (\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid signature stock E K W A) \<and>
      (\<forall>A\<in>paper_R_positive_diagram signature stock denote.
        paper_R_bbk_model.paper_R_valid signature stock E K W A) \<and>
      paper_R_bbk_model.paper_R_valid signature stock E K W
        (named_paper_not (named_paper_iff stock P Q))"
proof -
  let ?D = "paper_R_positive_diagram signature stock denote"
  let ?I = "named_paper_iff stock P Q"
  let ?N = "named_paper_not ?I"
  let ?S = "insert ?N ?D"
  have il: "paper_R_in_language signature stock ?I Prop"
    by (rule paper_R_named_paper_iff_language[OF stock_rich pl ql])
  have nl: "paper_R_in_language signature stock ?N Prop"
    by (rule paper_R_named_not_language[OF il])
  have nc: "named_fv ?N = {}"
    by (simp only: named_paper_primitive_fv named_paper_defined_fv pc qc; simp)
  have negative_sentence: "paper_R_sentence signature stock ?N"
    by (rule paper_R_sentenceI[OF nl nc])
  have diagram_closed: "paper_R_closed_theory signature stock ?D"
    by (rule paper_R_positive_diagram_closed)
  have additions_closed: "paper_R_closed_theory signature stock ?S"
    by (simp only: paper_R_closed_theory_insert;
      rule conjI[OF negative_sentence diagram_closed])
  have empty_typed: "named_env_typed domain stock Map.empty"
    by (simp add: named_env_typed_def)
  have pa: "named_adequate Map.empty P" and qa: "named_adequate Map.empty Q"
    by (simp_all add: named_adequate_def pc qc)
  have separating: "paper_R_named_consistent signature stock (insert ?N (T \<union> ?D))"
    by (rule paper_R_positive_diagram_separating_consistent[
      OF theory_h pe theory_valid pl ql empty_typed pa qa different])
  have rearranged: "T \<union> ?S = insert ?N (T \<union> ?D)" by blast
  have consistent: "paper_R_named_consistent signature stock (T \<union> ?S)"
    by (simp only: rearranged; rule separating)
  obtain E :: "otype \<Rightarrow> (('c paper_R_henkin_name) paper_named_term set) set"
    and K and W where target_model: "paper_R_bbk_model signature stock E K W"
    and target_valid: "\<forall>A\<in>T \<union> ?S.
      paper_R_bbk_model.paper_R_valid signature stock E K W A"
    using paper_R_H_theory_closed_extension_model[
      OF stock_rich theory_h additions_closed consistent] by blast
  have theory_truth: "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid signature stock E K W A"
    using target_valid by blast
  have diagram_truth: "\<forall>A\<in>?D. paper_R_bbk_model.paper_R_valid signature stock E K W A"
    using target_valid by blast
  have negative_truth: "paper_R_bbk_model.paper_R_valid signature stock E K W ?N"
    using target_valid by blast
  show ?thesis
    by (rule exI[where x=E], rule exI[where x=K], rule exI[where x=W],
      rule conjI[OF target_model], rule conjI[OF theory_truth],
      rule conjI[OF diagram_truth negative_truth])
qed

end

end
