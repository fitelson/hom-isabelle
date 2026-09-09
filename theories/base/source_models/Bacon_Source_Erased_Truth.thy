theory Bacon_Source_Erased_Truth
  imports Bacon_Source_Erased_Denotation Bacon_Source_Framed_Truth
begin

section \<open>Language guards for the complete primitive applications\<close>

lemma erased_truth_unary_language:
  assumes symbol: "paper_logical_type l = Arr \<sigma> \<tau>"
    and argument: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp (SLogical l) A) \<tau>"
proof -
  have at: "has_stype paper_logical_type \<Gamma> A \<sigma>"
    and names: "sterm_in_signature \<Sigma> A"
    using argument unfolding sterm_in_language_def by auto
  have lt: "has_stype paper_logical_type \<Gamma> (SLogical l) (Arr \<sigma> \<tau>)"
    using has_stype.Logical[where logical_type=paper_logical_type and \<Gamma>=\<Gamma> and l=l]
    by (simp only: symbol)
  show ?thesis unfolding sterm_in_language_def
    by (rule conjI[OF has_stype.App[OF lt at]]) (simp add: names)
qed

lemma erased_truth_binary_language:
  assumes symbol: "paper_logical_type l = Arr \<sigma> (Arr \<tau> \<upsilon>)"
    and left: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
    and right: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B \<tau>"
  shows "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp (SApp (SLogical l) A) B) \<upsilon>"
proof -
  have partial: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp (SLogical l) A) (Arr \<tau> \<upsilon>)"
    by (rule erased_truth_unary_language[OF symbol left])
  have ft: "has_stype paper_logical_type \<Gamma> (SApp (SLogical l) A) (Arr \<tau> \<upsilon>)"
    and fs: "sterm_in_signature \<Sigma> (SApp (SLogical l) A)"
    using partial unfolding sterm_in_language_def by auto
  have bt: "has_stype paper_logical_type \<Gamma> B \<tau>"
    and bs: "sterm_in_signature \<Sigma> B"
    using right unfolding sterm_in_language_def by auto
  have names: "sterm_in_signature \<Sigma> (SApp (SApp (SLogical l) A) B)"
    using fs bs by simp
  show ?thesis unfolding sterm_in_language_def
    by (rule conjI[OF has_stype.App[OF ft bt] names])
qed

section \<open>The erased interpretation inherits all six primitive truth clauses\<close>

text \<open>
  Let M be an independent named BBK model with domains
  D′σ = {⟨σ,a⟩ | a ∈ Dσ}. Its erased interpretation J(ρ,A) agrees
  with the framed interpretation whenever Γ types both A and ρ.
  Source: Bacon–Dorr Definition 3.1(iii.a–f), pp.43–44.

  Representation: every application of the agreement theorem below has
  an explicit language proof for the whole formula. Quantifier instances
  use the extended typed environment and the guarded shifted body.
  Status: the named-model premise is explicit. Original Dσ may overlap;
  this leaf proves truth clauses, not locality or a model assembly.
\<close>

context
  fixes \<Sigma> :: "'c ssignature" and G :: sgcontext and D :: "otype \<Rightarrow> 'v set"
    and J :: "(otype \<times> 'v) named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> otype \<times> 'v"
    and V :: "otype \<times> 'v \<Rightarrow> bool"
  assumes named_model: "paper_named_bbk_model \<Sigma> G (named_tag_domain D) J V"
begin

interpretation Named: paper_named_bbk_model \<Sigma> G "named_tag_domain D" J V
  by (rule named_model)

lemma erased_truth_framed_agreement:
  assumes language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<tau>"
    and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
  shows "named_erased_denote G J \<rho> A = Named.framed_denote \<Gamma> \<rho> A"
proof -
  have chart: "named_chart G \<Gamma> (named_chart_choice G \<Gamma>)"
    by (rule named_chart_choice_valid[OF Named.stock_rich])
  have selected: "named_erased_denote G J \<rho> A =
    J (named_chart_assignment (named_chart_choice G \<Gamma>) \<rho>)
      (source_to_named G (named_chart_choice G \<Gamma>) A)"
    by (rule named_erased_denote_agrees[OF named_model language env chart])
  show ?thesis using selected
    by (simp only: Named.framed_denote_def Named.chart_denote_def)
qed

theorem erased_valuation_neg:
  assumes language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
  shows "V (named_erased_denote G J \<rho> (paper_not A)) = (\<not> V (named_erased_denote G J \<rho> A))"
proof -
  have whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_not A) Prop"
    unfolding paper_not_def by (rule erased_truth_unary_language[OF _ language]) simp
  have formula: "named_erased_denote G J \<rho> (paper_not A) = Named.framed_denote \<Gamma> \<rho> (paper_not A)"
    by (rule erased_truth_framed_agreement[OF whole env])
  have operand: "named_erased_denote G J \<rho> A = Named.framed_denote \<Gamma> \<rho> A"
    by (rule erased_truth_framed_agreement[OF language env])
  show ?thesis by (simp only: formula operand; rule Named.framed_valuation_neg[OF language env])
qed

theorem erased_valuation_conj:
  assumes left: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and right: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
  shows "V (named_erased_denote G J \<rho> (paper_and A B)) =
    (V (named_erased_denote G J \<rho> A) \<and> V (named_erased_denote G J \<rho> B))"
proof -
  have whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_and A B) Prop"
    unfolding paper_and_def by (rule erased_truth_binary_language[OF _ left right]) simp
  show ?thesis
    by (simp only: erased_truth_framed_agreement[OF whole env]
      erased_truth_framed_agreement[OF left env] erased_truth_framed_agreement[OF right env];
      rule Named.framed_valuation_conj[OF left right env])
qed

theorem erased_valuation_disj:
  assumes left: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A Prop"
    and right: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B Prop"
    and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
  shows "V (named_erased_denote G J \<rho> (paper_or A B)) =
    (V (named_erased_denote G J \<rho> A) \<or> V (named_erased_denote G J \<rho> B))"
proof -
  have whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (paper_or A B) Prop"
    unfolding paper_or_def by (rule erased_truth_binary_language[OF _ left right]) simp
  show ?thesis
    by (simp only: erased_truth_framed_agreement[OF whole env]
      erased_truth_framed_agreement[OF left env] erased_truth_framed_agreement[OF right env];
      rule Named.framed_valuation_disj[OF left right env])
qed

theorem erased_valuation_identity:
  assumes left: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> A \<sigma>"
    and right: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> B \<sigma>"
    and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
  shows "V (named_erased_denote G J \<rho> (SApp (SApp (SLogical (SEq \<sigma>)) A) B)) =
    (named_erased_denote G J \<rho> A = named_erased_denote G J \<rho> B)"
proof -
  have whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma>
    (SApp (SApp (SLogical (SEq \<sigma>)) A) B) Prop"
    by (rule erased_truth_binary_language[OF _ left right]) simp
  show ?thesis
    by (simp only: erased_truth_framed_agreement[OF whole env]
      erased_truth_framed_agreement[OF left env] erased_truth_framed_agreement[OF right env];
      rule Named.framed_valuation_identity[OF left right env])
qed

lemma erased_truth_quantifier_instance:
  assumes language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
    and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
    and member: "a \<in> named_tag_domain D \<sigma>"
  shows "named_erased_denote G J (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)) =
    Named.framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0))"
proof -
  have body: "sterm_in_language paper_logical_type \<Sigma> (\<sigma> # \<Gamma>)
    (SApp (sshift F) (SVar 0)) Prop"
    by (rule chart_quantifier_body_language[OF language])
  have extended: "pbbk_env_typed (named_tag_domain D) (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>)"
    by (rule pbbk_env_extend[OF env member])
  show ?thesis by (rule erased_truth_framed_agreement[OF body extended])
qed

theorem erased_valuation_forall:
  assumes language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
    and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
  shows "V (named_erased_denote G J \<rho> (SApp (SLogical (SAll \<sigma>)) F)) =
    (\<forall>a \<in> named_tag_domain D \<sigma>. V (named_erased_denote G J (pbbk_extend a \<rho>)
      (SApp (sshift F) (SVar 0))))"
proof -
  have whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp (SLogical (SAll \<sigma>)) F) Prop"
    by (rule erased_truth_unary_language[OF _ language]) simp
  have formula: "named_erased_denote G J \<rho> (SApp (SLogical (SAll \<sigma>)) F) =
    Named.framed_denote \<Gamma> \<rho> (SApp (SLogical (SAll \<sigma>)) F)"
    by (rule erased_truth_framed_agreement[OF whole env])
  have instances:
    "(\<forall>a \<in> named_tag_domain D \<sigma>. V (named_erased_denote G J (pbbk_extend a \<rho>)
       (SApp (sshift F) (SVar 0)))) =
     (\<forall>a \<in> named_tag_domain D \<sigma>. V (Named.framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>)
       (SApp (sshift F) (SVar 0))))"
  proof (rule ball_cong[OF refl])
    fix a
    assume member: "a \<in> named_tag_domain D \<sigma>"
    show "V (named_erased_denote G J (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0))) =
      V (Named.framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)))"
      by (rule arg_cong[where f=V, OF erased_truth_quantifier_instance[OF language env member]])
  qed
  show ?thesis by (simp only: formula instances; rule Named.framed_valuation_forall[OF language env])
qed

theorem erased_valuation_exists:
  assumes language: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> F (Arr \<sigma> Prop)"
    and env: "pbbk_env_typed (named_tag_domain D) \<Gamma> \<rho>"
  shows "V (named_erased_denote G J \<rho> (SApp (SLogical (SEx \<sigma>)) F)) =
    (\<exists>a \<in> named_tag_domain D \<sigma>. V (named_erased_denote G J (pbbk_extend a \<rho>)
      (SApp (sshift F) (SVar 0))))"
proof -
  have whole: "sterm_in_language paper_logical_type \<Sigma> \<Gamma> (SApp (SLogical (SEx \<sigma>)) F) Prop"
    by (rule erased_truth_unary_language[OF _ language]) simp
  have formula: "named_erased_denote G J \<rho> (SApp (SLogical (SEx \<sigma>)) F) =
    Named.framed_denote \<Gamma> \<rho> (SApp (SLogical (SEx \<sigma>)) F)"
    by (rule erased_truth_framed_agreement[OF whole env])
  have instances:
    "(\<exists>a \<in> named_tag_domain D \<sigma>. V (named_erased_denote G J (pbbk_extend a \<rho>)
       (SApp (sshift F) (SVar 0)))) =
     (\<exists>a \<in> named_tag_domain D \<sigma>. V (Named.framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>)
       (SApp (sshift F) (SVar 0))))"
  proof (rule bex_cong[OF refl])
    fix a
    assume member: "a \<in> named_tag_domain D \<sigma>"
    show "V (named_erased_denote G J (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0))) =
      V (Named.framed_denote (\<sigma> # \<Gamma>) (pbbk_extend a \<rho>) (SApp (sshift F) (SVar 0)))"
      by (rule arg_cong[where f=V, OF erased_truth_quantifier_instance[OF language env member]])
  qed
  show ?thesis by (simp only: formula instances; rule Named.framed_valuation_exists[OF language env])
qed

end

end
