theory Bacon_Source_ZF_Action_BBK_Domains
  imports Bacon_Source_ZF_Action_Model_Nonempty
begin

section \<open>Normalize the ambient F indices outside the source R language\<close>

text \<open>
  At W put Dᴮσ=explode(Dσ(W)) for σ∈R and Dᴮσ={} otherwise.
  Source role: the BBK domains at a target object in Proposition 3.21,
  pp.57 and 70. Empty off-R entries are a representation convention
  for an R-indexed family, not a new source nonemptiness condition.

  Typing against this normalized family is exactly typing against
  the original action domains with the explicit R-support condition.
  This equivalence needs no model premise. The nonemptiness result
  below uses generic action-model totality, not a BBK-model assumption.
  No BBK interpretation or validation of its remaining clauses is
  claimed in this domain-only leaf.
\<close>

definition paper_ZF_action_bbk_domain :: "(otype \<Rightarrow> 'o \<Rightarrow> ZF) \<Rightarrow> 'o \<Rightarrow> otype \<Rightarrow> ZF set" where
  "paper_ZF_action_bbk_domain D W \<rho> = (if paper_R_type \<rho> then explode (D \<rho> W) else {})"

lemma paper_ZF_action_bbk_domain_R:
  "paper_R_type \<rho> \<Longrightarrow> paper_ZF_action_bbk_domain D W \<rho> = explode (D \<rho> W)"
  by (simp add: paper_ZF_action_bbk_domain_def)

lemma paper_ZF_action_bbk_domain_nonR:
  "\<not> paper_R_type \<rho> \<Longrightarrow> paper_ZF_action_bbk_domain D W \<rho> = {}"
  by (simp add: paper_ZF_action_bbk_domain_def)

lemma paper_ZF_action_bbk_domain_member:
  "a \<in> paper_ZF_action_bbk_domain D W \<rho> \<longleftrightarrow> paper_R_type \<rho> \<and> a \<in> explode (D \<rho> W)"
  by (cases "paper_R_type \<rho>") (simp_all add: paper_ZF_action_bbk_domain_def)

theorem paper_ZF_action_bbk_env_iff:
  "named_env_typed (paper_ZF_action_bbk_domain D W) G g \<longleftrightarrow> paper_ZF_action_env_typed D G W g"
proof
  assume typed: "named_env_typed (paper_ZF_action_bbk_domain D W) G g"
  show "paper_ZF_action_env_typed D G W g"
  proof (rule paper_ZF_action_envI)
    show "named_env_typed (\<lambda>\<rho>. explode (D \<rho> W)) G g"
    proof (unfold named_env_typed_def, intro allI impI)
      fix n a
      assume assigned: "g n = Some a"
      have member: "a \<in> paper_ZF_action_bbk_domain D W (G n)" by (rule named_env_value[OF typed assigned])
      show "a \<in> explode (D (G n) W)" using member by (simp only: paper_ZF_action_bbk_domain_member; blast)
    qed
  next
    fix n
    assume defined: "n \<in> dom g"
    obtain a where assigned: "g n = Some a" using defined by blast
    have member: "a \<in> paper_ZF_action_bbk_domain D W (G n)" by (rule named_env_value[OF typed assigned])
    show "paper_R_type (G n)" using member by (simp only: paper_ZF_action_bbk_domain_member; blast)
  qed
next
  assume typed: "paper_ZF_action_env_typed D G W g"
  show "named_env_typed (paper_ZF_action_bbk_domain D W) G g"
  proof (unfold named_env_typed_def, intro allI impI)
    fix n a
    assume assigned: "g n = Some a"
    have rt: "paper_R_type (G n)" by (rule paper_ZF_action_env_assigned_R[OF typed assigned])
    have member: "a \<in> explode (D (G n) W)" by (rule paper_ZF_action_env_value[OF typed assigned])
    show "a \<in> paper_ZF_action_bbk_domain D W (G n)"
      by (simp only: paper_ZF_action_bbk_domain_member; rule conjI[OF rt member])
  qed
qed

corollary paper_ZF_action_bbk_domain_nonempty:
  assumes model: "paper_ZF_action_model \<Sigma> G Obj Ar source target compose identity root D T I"
    and object: "W \<in> Obj" and rt: "paper_R_type \<rho>"
  shows "paper_ZF_action_bbk_domain D W \<rho> \<noteq> {}"
  by (simp only: paper_ZF_action_bbk_domain_R[OF rt]; rule paper_ZF_action_model_R_domain_nonempty[OF model object rt])

end
