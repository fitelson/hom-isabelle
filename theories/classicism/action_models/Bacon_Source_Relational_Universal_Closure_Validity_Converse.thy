theory Bacon_Source_Relational_Universal_Closure_Validity_Converse
  imports Bacon_Source_Relational_Universal_Closure_Validity
begin

section \<open>Universal closure preserves validity in both directions\<close>

context paper_R_bbk_model
begin

lemma paper_R_valid_universal_generalization:
  assumes language: "paper_R_in_language signature stock P Prop"
    and rt: "paper_R_type (stock n)" and valid: "paper_R_valid P"
  shows "paper_R_valid (named_paper_all (stock n) (NLam n P))"
proof -
  have whole: "paper_R_in_language signature stock (named_paper_all (stock n) (NLam n P)) Prop"
    by (rule paper_R_named_all_binder_language[OF language refl rt])
  show ?thesis
  proof (rule paper_R_validI[OF whole])
    fix g
    assume typed: "named_env_typed domain stock g"
      and adequate: "named_adequate g (named_paper_all (stock n) (NLam n P))"
    have abstraction_adequate: "named_adequate g (NLam n P)"
      using adequate by (simp only: named_adequate_def named_paper_primitive_fv)
    have every: "\<forall>a\<in>domain (stock n). valuation (denote (g(n := Some a)) P)"
    proof (intro ballI)
      fix a
      assume member: "a \<in> domain (stock n)"
      have updated: "named_env_typed domain stock (g(n := Some a))"
        by (rule named_assignment_update_typed[where D=domain and G=stock and n=n, OF typed member])
      have covered: "named_adequate (g(n := Some a)) P"
        by (rule iffD2[OF named_binder_update_adequate_iff abstraction_adequate])
      show "valuation (denote (g(n := Some a)) P)" by (rule paper_R_validE[OF valid updated covered])
    qed
    show "valuation (denote g (named_paper_all (stock n) (NLam n P)))"
      by (rule iffD2[OF paper_R_forall_binder_truth[OF language refl rt typed abstraction_adequate] every])
  qed
qed

theorem paper_R_valid_all_vec:
  assumes language: "paper_R_in_language signature stock P Prop"
    and binders: "list_all paper_R_type (map stock ns)" and valid: "paper_R_valid P"
  shows "paper_R_valid (paper_R_all_vec stock ns P)"
  using binders
proof (induction ns)
  case Nil
  show ?case by (simp only: paper_R_all_vec.simps; rule valid)
next
  case (Cons n ns)
  have rt: "paper_R_type (stock n)" and tail: "list_all paper_R_type (map stock ns)"
    using Cons.prems by simp_all
  have inner: "paper_R_in_language signature stock (paper_R_all_vec stock ns P) Prop"
    by (rule paper_R_all_vec_language[OF language tail])
  show ?case by (simp only: paper_R_all_vec.simps;
    rule paper_R_valid_universal_generalization[OF inner rt Cons.IH[OF tail]])
qed

corollary paper_R_valid_all_vec_iff:
  assumes language: "paper_R_in_language signature stock P Prop"
    and binders: "list_all paper_R_type (map stock ns)"
  shows "paper_R_valid (paper_R_all_vec stock ns P) \<longleftrightarrow> paper_R_valid P"
  by (rule iffI; (rule paper_R_valid_all_vec_instance[OF language binders]
    | rule paper_R_valid_all_vec[OF language binders]); assumption)

end

text \<open>
  Global validity of P covers every updated assignment used in ∀n.P.
  This is semantic universal generalization, not a rule for a proof
  with open local assumptions. The finite prefix may repeat names
  and need not cover all free variables. Sources: Definition 3.1's
  quantifier clause and the sentence reduction in Theorem 3.2.
\<close>

end
