theory Bacon_Source_Named_Retraction_Steps
  imports Bacon_Source_Named_Signature_Retraction Bacon_Source_Named_Conversion
begin

section \<open>Retracting foreign constants preserves literal conversion steps\<close>

text \<open>
  Replace each constant outside Σ of type σ by a variable vσ chosen
  away from the names occurring in the conversion. A literal β or η
  step remains a step after this replacement.
  Source role: reconciling βη equivalence in Definition 3.1(ii.d), p.44,
  with the declared language ℒ(Σ), using precisely Figure 2, pp.7–8.

  Isabelle representation. named_retract retains constants belonging to
  Σ and leaves binders unchanged. Avoidance of all endpoint names implies
  avoidance of the contracted binder, preserves β's free-for condition,
  and preserves η's free-variable condition. Contextual induction passes
  the same avoidance condition to the contracted subterms.

  Status. Raw root and contextual steps only. No α step, model hypothesis,
  countability of constant names, or closed term of each type is assumed.
  A subsequent finite-support argument will choose the variables uniformly
  for every intermediate term of a conversion proof.
\<close>

lemma named_retract_beta:
  assumes step: "named_beta_contract A B"
    and fresh: "\<And>\<sigma>. v \<sigma> \<notin> named_vars A \<union> named_vars B"
  shows "named_beta_contract (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
  using step fresh
proof (induction rule: named_beta_contract.induct)
  case (beta B x A)
  have not_x: "\<And>\<sigma>. v \<sigma> \<noteq> x" using beta.prems by auto
  have body_fresh: "\<And>\<sigma>. v \<sigma> \<notin> named_vars A" using beta.prems by auto
  have free_for: "named_free_for (named_retract \<Sigma> v B) x (named_retract \<Sigma> v A)"
    by (rule named_retract_free_for[OF beta.hyps not_x body_fresh])
  have replaced: "named_retract \<Sigma> v (named_subst x B A) =
    named_subst x (named_retract \<Sigma> v B) (named_retract \<Sigma> v A)"
    by (rule named_retract_subst[OF not_x])
  show ?case by (simp only: named_retract.simps replaced;
    rule named_beta_contract.beta[OF free_for])
qed

lemma named_retract_eta:
  assumes step: "named_eta_contract A B"
    and fresh: "\<And>\<sigma>. v \<sigma> \<notin> named_vars A \<union> named_vars B"
  shows "named_eta_contract (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
  using step fresh
proof (induction rule: named_eta_contract.induct)
  case (eta x F)
  have not_x: "\<And>\<sigma>. v \<sigma> \<noteq> x" using eta.prems by auto
  have still_fresh: "x \<notin> named_fv (named_retract \<Sigma> v F)"
    by (rule named_retract_fresh[OF eta.hyps not_x])
  show ?case by (simp only: named_retract.simps;
    rule named_eta_contract.eta[OF still_fresh])
qed

lemma named_retract_compatible:
  assumes step: "named_compatible_step R A B"
    and roots: "\<And>M N. R M N \<Longrightarrow>
      (\<And>\<sigma>. v \<sigma> \<notin> named_vars M \<union> named_vars N) \<Longrightarrow>
      Q (named_retract \<Sigma> v M) (named_retract \<Sigma> v N)"
    and fresh: "\<And>\<sigma>. v \<sigma> \<notin> named_vars A \<union> named_vars B"
  shows "named_compatible_step Q (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
  using step fresh
proof (induction rule: named_compatible_step.induct)
  case (root M N)
  have root_step: "Q (named_retract \<Sigma> v M) (named_retract \<Sigma> v N)"
    by (rule roots[OF root.hyps root.prems])
  show ?case by (rule named_compatible_step.root[where R=Q
    and M="named_retract \<Sigma> v M" and N="named_retract \<Sigma> v N", OF root_step])
next
  case (App_left M M' N)
  have subfresh: "\<And>\<sigma>. v \<sigma> \<notin> named_vars M \<union> named_vars M'"
    using App_left.prems by auto
  have inner: "named_compatible_step Q (named_retract \<Sigma> v M) (named_retract \<Sigma> v M')"
    by (rule App_left.IH[OF subfresh])
  show ?case by (simp only: named_retract.simps;
    rule named_compatible_step.App_left[OF inner])
next
  case (App_right N N' M)
  have subfresh: "\<And>\<sigma>. v \<sigma> \<notin> named_vars N \<union> named_vars N'"
    using App_right.prems by auto
  have inner: "named_compatible_step Q (named_retract \<Sigma> v N) (named_retract \<Sigma> v N')"
    by (rule App_right.IH[OF subfresh])
  show ?case by (simp only: named_retract.simps;
    rule named_compatible_step.App_right[OF inner])
next
  case (Lam_body M M' n)
  have subfresh: "\<And>\<sigma>. v \<sigma> \<notin> named_vars M \<union> named_vars M'"
    using Lam_body.prems by auto
  have inner: "named_compatible_step Q (named_retract \<Sigma> v M) (named_retract \<Sigma> v M')"
    by (rule Lam_body.IH[OF subfresh])
  show ?case by (simp only: named_retract.simps;
    rule named_compatible_step.Lam_body[OF inner])
qed

corollary named_retract_beta_step:
  assumes step: "named_compatible_step named_beta_contract A B"
    and fresh: "\<And>\<sigma>. v \<sigma> \<notin> named_vars A \<union> named_vars B"
  shows "named_compatible_step named_beta_contract
    (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
  by (rule named_retract_compatible[where R=named_beta_contract and Q=named_beta_contract,
    OF step _ fresh]; rule named_retract_beta; assumption)

corollary named_retract_eta_step:
  assumes step: "named_compatible_step named_eta_contract A B"
    and fresh: "\<And>\<sigma>. v \<sigma> \<notin> named_vars A \<union> named_vars B"
  shows "named_compatible_step named_eta_contract
    (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
  by (rule named_retract_compatible[where R=named_eta_contract and Q=named_eta_contract,
    OF step _ fresh]; rule named_retract_eta; assumption)

end
