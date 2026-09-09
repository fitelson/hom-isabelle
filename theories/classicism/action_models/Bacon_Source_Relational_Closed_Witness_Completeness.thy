theory Bacon_Source_Relational_Closed_Witness_Completeness
  imports Bacon_Source_Relational_Maximal_Theory Bacon_Source_Relational_Witness_Syntax
begin

section \<open>Constant witnesses for closed R predicates\<close>

definition paper_R_closed_constant_witness_complete ::
  "'c ssignature \<Rightarrow> sgcontext \<Rightarrow> 'c paper_named_term set \<Rightarrow> bool" where
  "paper_R_closed_constant_witness_complete \<Omega> G M \<longleftrightarrow>
    (\<forall>\<sigma> F. paper_R_in_language \<Omega> G F (Arr \<sigma> Prop) \<longrightarrow> named_fv F = {} \<longrightarrow>
      named_paper_ex \<sigma> F \<in> M \<longrightarrow> (\<exists>c\<in>\<Omega> \<sigma>. NApp F (NConst c \<sigma>) \<in> M))"

lemma paper_R_closed_constant_witness_completeD:
  assumes complete: "paper_R_closed_constant_witness_complete \<Omega> G M"
    and predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)" and closed: "named_fv F = {}"
    and existential: "named_paper_ex \<sigma> F \<in> M"
  obtains c where "c \<in> \<Omega> \<sigma>" "NApp F (NConst c \<sigma>) \<in> M"
  using complete predicate closed existential that unfolding paper_R_closed_constant_witness_complete_def by blast

text \<open>
  A maximal closed extension containing (∃σF→Fc) contains Fc whenever
  it contains ∃σF: use actual local MP and then closed-consequence
  closure. Both F and Fc are closed. This is the constant-witness
  property of Theorem 3.2, p.45 n.64, restricted explicitly to closed
  predicates. No open negation decision, model or witness assumption
  is concealed in maximality; the conditional scheme is supplied below.
\<close>

theorem paper_R_closed_witness_complete_from_conditionals:
  assumes maximal: "paper_R_closed_maximal_extension \<Omega> G S M"
    and conditionals: "\<And>\<sigma> F. paper_R_in_language \<Omega> G F (Arr \<sigma> Prop) \<Longrightarrow>
      named_fv F = {} \<Longrightarrow> \<exists>c\<in>\<Omega> \<sigma>. paper_R_witness_axiom G \<sigma> F c \<in> M"
  shows "paper_R_closed_constant_witness_complete \<Omega> G M"
proof (unfold paper_R_closed_constant_witness_complete_def, intro allI impI)
  fix \<sigma> F
  assume predicate: "paper_R_in_language \<Omega> G F (Arr \<sigma> Prop)"
    and closed: "named_fv F = {}" and existential: "named_paper_ex \<sigma> F \<in> M"
  obtain c where declared: "c \<in> \<Omega> \<sigma>" and conditional: "paper_R_witness_axiom G \<sigma> F c \<in> M"
    using conditionals[OF predicate closed] by blast
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF predicate]])
  have ct: "paper_R_has_type G (NConst c \<sigma>) \<sigma>" by (rule paper_R_has_type.Const[OF rt])
  have cl: "paper_R_in_language \<Omega> G (NConst c \<sigma>) \<sigma>"
    unfolding paper_R_in_language_def by (rule conjI[OF ct]; simp only: named_in_signature.simps; rule declared)
  have instance_language: "paper_R_in_language \<Omega> G (NApp F (NConst c \<sigma>)) Prop"
    by (rule paper_R_language_App[OF predicate cl])
  have first: "paper_R_named_derivable \<Omega> G M (named_paper_ex \<sigma> F)"
    by (rule paper_R_closed_maximal_member_derivable[OF maximal existential])
  have second: "paper_R_named_derivable \<Omega> G M
      (named_paper_imp G (named_paper_ex \<sigma> F) (NApp F (NConst c \<sigma>)))"
    using paper_R_closed_maximal_member_derivable[OF maximal conditional] by (simp only: paper_R_witness_axiom_def)
  have instance_proof: "paper_R_named_derivable \<Omega> G M (NApp F (NConst c \<sigma>))"
    by (rule paper_R_named_derivable.MP[OF first second instance_language])
  have instance_closed: "named_fv (NApp F (NConst c \<sigma>)) = {}" by (simp add: closed)
  have instance_member: "NApp F (NConst c \<sigma>) \<in> M"
    by (rule paper_R_closed_maximal_consequence[OF maximal instance_proof instance_closed])
  show "\<exists>c\<in>\<Omega> \<sigma>. NApp F (NConst c \<sigma>) \<in> M"
    by (rule bexI[where x=c], rule instance_member, rule declared)
qed

end
