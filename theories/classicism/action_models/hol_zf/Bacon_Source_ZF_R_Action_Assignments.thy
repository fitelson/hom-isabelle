theory Bacon_Source_ZF_R_Action_Assignments
  imports Bacon_Source_ZF_Action_Assignments Bacon_Source_ZF_R_Representation_Assignment_Syntax
begin

section \<open>The constructed domains already enforce R support\<close>

text \<open>
  The raw type recursion gives empty domains at non-R indices.
  Consequently named typing in this constructed family already
  implies the explicit R-supported assignment condition required by
  the generic action interpretation (Definitions 3.19–3.20, pp.55–56).
  This bridge needs no model, all-type invariant, bounds, completion,
  old interpretation or evaluation assumption.
\<close>

theorem paper_ZF_R_representation_env_supported:
  assumes typed: "named_env_typed
    (\<lambda>\<rho>. explode (paper_ZF_rep_domain (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows \<rho>) M)) G g"
  shows "paper_ZF_action_env_typed
    (\<lambda>\<rho>. paper_ZF_rep_domain (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows \<rho>)) G M g"
proof (rule paper_ZF_action_envI[
    where D="\<lambda>\<rho>. paper_ZF_rep_domain (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows \<rho>)"
      and G=G and W=M, OF typed])
  fix n
  assume defined: "n \<in> dom g"
  obtain a where assigned: "g n = Some a" using defined by blast
  have member: "a \<in> explode (paper_ZF_rep_domain
      (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows (G n)) M)"
    by (rule named_env_value[OF typed assigned])
  show "paper_R_type (G n)" by (rule paper_ZF_R_type_representation_member_R[OF member])
qed

theorem paper_ZF_R_representation_env_iff:
  "paper_ZF_action_env_typed
      (\<lambda>\<rho>. paper_ZF_rep_domain (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows \<rho>)) G M g \<longleftrightarrow>
    named_env_typed
      (\<lambda>\<rho>. explode (paper_ZF_rep_domain (paper_ZF_R_type_representation \<Sigma> G IndividualBound ArrowBound e Arrows \<rho>) M)) G g"
  by (rule iffI; (rule paper_ZF_action_env_named | rule paper_ZF_R_representation_env_supported); assumption)

end
