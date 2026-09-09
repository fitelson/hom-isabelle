theory Bacon_Source_Relational_Signature_Conservativity
  imports Bacon_Source_Relational_Signature_Conversion
begin

section \<open>One finite avoidance set for the entire raw conversion proof\<close>

text \<open>
  A β/η step contributes all variable names of both endpoints, including
  bound names. Transitivity unions the supports of both subproofs.
  Retraction therefore preserves the literal free-for and η-freshness
  conditions throughout the proof, not only at its final endpoints.
  The constant signature and its ambient name type may be arbitrary.

  The resulting guarded conversion can still introduce free variables.
  Later semantic use must extend an endpoint-adequate assignment to cover
  the intermediate R terms, then use locality at the endpoints. This
  syntax theorem neither assumes nor proves semantic totality or completion.
\<close>

definition paper_R_retraction_support where
  "paper_R_retraction_support \<Sigma> G \<tau> A B S \<longleftrightarrow>
    finite S \<and> named_vars A \<union> named_vars B \<subseteq> S \<and>
    (\<forall>v. (\<forall>\<sigma>. paper_R_type \<sigma> \<longrightarrow> G (v \<sigma>) = \<sigma>) \<longrightarrow>
      (\<forall>\<sigma>. v \<sigma> \<notin> S) \<longrightarrow>
      paper_R_beta_eta_in_signature \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v B))"

lemma paper_R_retraction_supportI:
  assumes finite: "finite S" and names: "named_vars A \<union> named_vars B \<subseteq> S"
    and convert: "\<And>v. (\<And>\<sigma>. paper_R_type \<sigma> \<Longrightarrow> G (v \<sigma>) = \<sigma>) \<Longrightarrow>
      (\<And>\<sigma>. v \<sigma> \<notin> S) \<Longrightarrow>
      paper_R_beta_eta_in_signature \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
  shows "paper_R_retraction_support \<Sigma> G \<tau> A B S"
  using finite names convert unfolding paper_R_retraction_support_def by blast

lemma paper_R_retraction_support_finite:
  "paper_R_retraction_support \<Sigma> G \<tau> A B S \<Longrightarrow> finite S"
  unfolding paper_R_retraction_support_def by blast

lemma paper_R_retraction_support_names:
  "paper_R_retraction_support \<Sigma> G \<tau> A B S \<Longrightarrow> named_vars A \<union> named_vars B \<subseteq> S"
  unfolding paper_R_retraction_support_def by blast

lemma paper_R_retraction_support_apply:
  assumes support: "paper_R_retraction_support \<Sigma> G \<tau> A B S"
    and stock: "\<And>\<sigma>. paper_R_type \<sigma> \<Longrightarrow> G (v \<sigma>) = \<sigma>"
    and fresh: "\<And>\<sigma>. v \<sigma> \<notin> S"
  shows "paper_R_beta_eta_in_signature \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
  using support stock fresh unfolding paper_R_retraction_support_def by blast

theorem paper_R_raw_retraction_support:
  assumes conversion: "paper_R_raw_beta_eta G \<tau> A B"
  shows "\<exists>S. paper_R_retraction_support \<Sigma> G \<tau> A B S"
  using conversion
proof (induction rule: paper_R_raw_beta_eta.induct)
  case (Refl A \<tau>)
  show ?case
  proof (rule exI[where x="named_vars A"], rule paper_R_retraction_supportI[OF named_vars_finite])
    show "named_vars A \<union> named_vars A \<subseteq> named_vars A" by simp
  next
    fix v
    assume stock: "\<And>\<sigma>. paper_R_type \<sigma> \<Longrightarrow> G (v \<sigma>) = \<sigma>"
      and fresh: "\<And>\<sigma>. v \<sigma> \<notin> named_vars A"
    show "paper_R_beta_eta_in_signature \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v A)"
      by (rule paper_R_beta_eta_in_signature.Refl[OF paper_R_retract_language[OF Refl.hyps stock]])
  qed
next
  case (Beta A \<tau> B)
  let ?S = "named_vars A \<union> named_vars B"
  have finite: "finite ?S" by (rule finite_UnI; rule named_vars_finite)
  show ?case
  proof (rule exI[where x="?S"], rule paper_R_retraction_supportI[OF finite subset_refl])
    fix v
    assume stock: "\<And>\<sigma>. paper_R_type \<sigma> \<Longrightarrow> G (v \<sigma>) = \<sigma>"
      and fresh: "\<And>\<sigma>. v \<sigma> \<notin> ?S"
    have step: "named_compatible_step named_beta_contract (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
      by (rule named_retract_beta_step[OF Beta.hyps(3) fresh])
    show "paper_R_beta_eta_in_signature \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
      by (rule paper_R_beta_eta_in_signature.Beta[OF
        paper_R_retract_language[OF Beta.hyps(1) stock] paper_R_retract_language[OF Beta.hyps(2) stock] step])
  qed
next
  case (Eta A \<tau> B)
  let ?S = "named_vars A \<union> named_vars B"
  have finite: "finite ?S" by (rule finite_UnI; rule named_vars_finite)
  show ?case
  proof (rule exI[where x="?S"], rule paper_R_retraction_supportI[OF finite subset_refl])
    fix v
    assume stock: "\<And>\<sigma>. paper_R_type \<sigma> \<Longrightarrow> G (v \<sigma>) = \<sigma>"
      and fresh: "\<And>\<sigma>. v \<sigma> \<notin> ?S"
    have step: "named_compatible_step named_eta_contract (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
      by (rule named_retract_eta_step[OF Eta.hyps(3) fresh])
    show "paper_R_beta_eta_in_signature \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v B)"
      by (rule paper_R_beta_eta_in_signature.Eta[OF
        paper_R_retract_language[OF Eta.hyps(1) stock] paper_R_retract_language[OF Eta.hyps(2) stock] step])
  qed
next
  case (Sym \<tau> A B)
  obtain S where support: "paper_R_retraction_support \<Sigma> G \<tau> A B S" using Sym.IH by blast
  have finite: "finite S" by (rule paper_R_retraction_support_finite[OF support])
  have names: "named_vars B \<union> named_vars A \<subseteq> S"
    using paper_R_retraction_support_names[OF support] by blast
  show ?case
  proof (rule exI[where x=S], rule paper_R_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<sigma>. paper_R_type \<sigma> \<Longrightarrow> G (v \<sigma>) = \<sigma>"
      and fresh: "\<And>\<sigma>. v \<sigma> \<notin> S"
    show "paper_R_beta_eta_in_signature \<Sigma> G \<tau> (named_retract \<Sigma> v B) (named_retract \<Sigma> v A)"
      by (rule paper_R_beta_eta_in_signature.Sym[OF paper_R_retraction_support_apply[OF support stock fresh]])
  qed
next
  case (Trans \<tau> A B C)
  obtain S where first: "paper_R_retraction_support \<Sigma> G \<tau> A B S" using Trans.IH(1) by blast
  obtain T where second: "paper_R_retraction_support \<Sigma> G \<tau> B C T" using Trans.IH(2) by blast
  have finite: "finite (S \<union> T)"
    by (rule finite_UnI[OF paper_R_retraction_support_finite[OF first] paper_R_retraction_support_finite[OF second]])
  have names: "named_vars A \<union> named_vars C \<subseteq> S \<union> T"
    using paper_R_retraction_support_names[OF first] paper_R_retraction_support_names[OF second] by blast
  show ?case
  proof (rule exI[where x="S \<union> T"], rule paper_R_retraction_supportI[OF finite names])
    fix v
    assume stock: "\<And>\<sigma>. paper_R_type \<sigma> \<Longrightarrow> G (v \<sigma>) = \<sigma>"
      and fresh: "\<And>\<sigma>. v \<sigma> \<notin> S \<union> T"
    have fs: "\<And>\<sigma>. v \<sigma> \<notin> S" and ft: "\<And>\<sigma>. v \<sigma> \<notin> T" using fresh by blast+
    show "paper_R_beta_eta_in_signature \<Sigma> G \<tau> (named_retract \<Sigma> v A) (named_retract \<Sigma> v C)"
      by (rule paper_R_beta_eta_in_signature.Trans[OF
        paper_R_retraction_support_apply[OF first stock fs] paper_R_retraction_support_apply[OF second stock ft]])
  qed
qed

section \<open>Signature conservativity with R richness alone\<close>

theorem paper_R_conversion_to_signature:
  assumes rich: "paper_R_rich G" and conversion: "paper_R_raw_beta_eta G \<tau> A B"
    and left: "named_in_signature \<Sigma> A" and right: "named_in_signature \<Sigma> B"
  shows "paper_R_beta_eta_in_signature \<Sigma> G \<tau> A B"
proof -
  obtain S where support: "paper_R_retraction_support \<Sigma> G \<tau> A B S"
    using paper_R_raw_retraction_support[where \<Sigma>=\<Sigma>, OF conversion] by blast
  have finite: "finite S" by (rule paper_R_retraction_support_finite[OF support])
  let ?v = "\<lambda>\<sigma>. SOME n. G n = (if paper_R_type \<sigma> then \<sigma> else Prop) \<and> n \<notin> S"
  have chosen: "G (?v \<sigma>) = (if paper_R_type \<sigma> then \<sigma> else Prop) \<and> ?v \<sigma> \<notin> S" for \<sigma>
  proof (rule someI_ex)
    have rt: "paper_R_type (if paper_R_type \<sigma> then \<sigma> else Prop)" by simp
    show "\<exists>n. G n = (if paper_R_type \<sigma> then \<sigma> else Prop) \<and> n \<notin> S"
      by (rule paper_R_rich_avoiding_variable[OF rich rt finite])
  qed
  have stock: "G (?v \<sigma>) = \<sigma>" if rt: "paper_R_type \<sigma>" for \<sigma>
    using conjunct1[OF chosen[of \<sigma>]] by (simp only: if_P[OF rt])
  have fresh: "\<And>\<sigma>. ?v \<sigma> \<notin> S" by (rule conjunct2[OF chosen])
  have retracted: "paper_R_beta_eta_in_signature \<Sigma> G \<tau> (named_retract \<Sigma> ?v A) (named_retract \<Sigma> ?v B)"
    by (rule paper_R_retraction_support_apply[OF support stock fresh])
  show ?thesis using retracted by (simp only: named_retract_fixed[OF left] named_retract_fixed[OF right])
qed

corollary paper_R_raw_to_signature:
  assumes rich: "paper_R_rich G" and conversion: "paper_R_raw_beta_eta G \<tau> A B"
    and left: "paper_R_in_language \<Sigma> G A \<tau>" and right: "paper_R_in_language \<Sigma> G B \<tau>"
  shows "paper_R_beta_eta_in_signature \<Sigma> G \<tau> A B"
proof -
  have ls: "named_in_signature \<Sigma> A" and rs: "named_in_signature \<Sigma> B"
    using left right unfolding paper_R_in_language_def by blast+
  show ?thesis by (rule paper_R_conversion_to_signature[OF rich conversion ls rs])
qed

corollary paper_R_signature_conversion_iff:
  assumes rich: "paper_R_rich G"
  shows "paper_R_beta_eta_in_signature \<Sigma> G \<tau> A B \<longleftrightarrow>
    paper_R_raw_beta_eta G \<tau> A B \<and> paper_R_in_language \<Sigma> G A \<tau> \<and> paper_R_in_language \<Sigma> G B \<tau>"
  using paper_R_signature_conversion_languages paper_R_signature_conversion_raw paper_R_raw_to_signature[OF rich] by blast

end
