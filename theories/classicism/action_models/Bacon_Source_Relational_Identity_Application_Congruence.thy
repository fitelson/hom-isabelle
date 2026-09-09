theory Bacon_Source_Relational_Identity_Application_Congruence
  imports Bacon_Source_Relational_Identity_Interpretation
begin

section \<open>A represented value determines its R type\<close>

lemma paper_R_identity_domain_value_type:
  assumes first: "X \<in> paper_R_identity_domain \<Sigma> G S \<sigma>"
    and second: "X \<in> paper_R_identity_domain \<Sigma> G S \<tau>"
  shows "\<sigma> = \<tau>"
proof (rule ccontr)
  assume different: "\<sigma> \<noteq> \<tau>"
  have disjoint: "paper_R_identity_domain \<Sigma> G S \<sigma> \<inter> paper_R_identity_domain \<Sigma> G S \<tau> = {}"
    by (rule paper_R_identity_domains_disjoint[OF different])
  show False using first second disjoint by blast
qed

section \<open>The heterogeneous application clause is derived, not weakened\<close>

text \<open>
  Definition 3.1(ii.b), p.44, does not assume that the two applications
  have matching type indices. We retain independent σ,τ and υ,ρ
  below. Equality of the head values, together with their proved
  class-domain memberships, implies equality of those arrow types.
  The actual application equation then proves the clause.

  Domain disjointness is a theorem of these typed term classes, not
  an extra condition on arbitrary BBK models. No Henkin, consistency,
  Functionality or BBK-model premise is used.
\<close>

theorem paper_R_identity_denote_application_cong:
  assumes rich: "paper_R_rich G"
    and fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and al: "paper_R_in_language \<Sigma> G A \<sigma>"
    and hl: "paper_R_in_language \<Sigma> G H (Arr \<upsilon> \<rho>)"
    and bl: "paper_R_in_language \<Sigma> G B \<upsilon>"
    and gt: "named_env_typed (paper_R_identity_domain \<Sigma> G S) G g"
    and kt: "named_env_typed (paper_R_identity_domain \<Sigma> G S) G k"
    and ga: "named_adequate g (NApp F A)" and ka: "named_adequate k (NApp H B)"
    and heads: "paper_R_identity_denote \<Sigma> G S g F = paper_R_identity_denote \<Sigma> G S k H"
    and arguments: "paper_R_identity_denote \<Sigma> G S g A = paper_R_identity_denote \<Sigma> G S k B"
  shows "paper_R_identity_denote \<Sigma> G S g (NApp F A) = paper_R_identity_denote \<Sigma> G S k (NApp H B)"
proof -
  have fa: "named_adequate g F" using ga by (auto simp: named_adequate_def)
  have ha: "named_adequate k H" using ka by (auto simp: named_adequate_def)
  have first: "paper_R_identity_denote \<Sigma> G S g F \<in> paper_R_identity_domain \<Sigma> G S (Arr \<sigma> \<tau>)"
    by (rule paper_R_identity_denote_type[OF fl gt fa])
  have second: "paper_R_identity_denote \<Sigma> G S k H \<in> paper_R_identity_domain \<Sigma> G S (Arr \<upsilon> \<rho>)"
    by (rule paper_R_identity_denote_type[OF hl kt ha])
  have moved: "paper_R_identity_denote \<Sigma> G S g F \<in> paper_R_identity_domain \<Sigma> G S (Arr \<upsilon> \<rho>)"
    by (simp only: heads; rule second)
  have arrow_types: "Arr \<sigma> \<tau> = Arr \<upsilon> \<rho>"
    by (rule paper_R_identity_domain_value_type[OF first moved])
  have domain_types: "\<sigma> = \<upsilon>" and result_types: "\<tau> = \<rho>" using arrow_types by simp_all
  show ?thesis by (simp only: paper_R_identity_denote_App[OF rich fl al gt ga]
    paper_R_identity_denote_App[OF rich hl bl kt ka] domain_types result_types heads arguments)
qed

end
