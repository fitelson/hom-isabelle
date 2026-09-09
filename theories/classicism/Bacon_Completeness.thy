theory Bacon_Completeness
  imports Bacon_Semantics
begin

section \<open>Semantic consequence and completeness interfaces\<close>

text \<open>
  This auxiliary interface fixes consequence and countermodel notions inside
  one already chosen \<open>applicative_structure\<close>.  It proves implications of
  the form ``countermodel property implies completeness''; it constructs no
  model and proves no unconditional completeness theorem.  These are not Bacon
  and Dorr's BBK or action-model completeness results.

  The notation \<open>\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A\<close> quantifies over assignments in this
  single structure.  Here \<open>\<Gamma>\<close> is a typing context and \<open>\<Delta>\<close> is a finite
  formula list.  The strong interfaces explicitly require all members of
  \<open>\<Delta>\<close> to be well-typed propositions.
\<close>

context applicative_structure
begin

definition satisfies_assumptions :: "ctx \<Rightarrow> oterm list \<Rightarrow> 'v env \<Rightarrow> bool" where
  "satisfies_assumptions \<Gamma> \<Delta> \<rho> \<longleftrightarrow>
    env_typed \<Gamma> \<rho> \<and> (\<forall>A \<in> set \<Delta>. \<Gamma> \<turnstile> A : Prop \<and> holds (eval \<rho> A))"

definition assumptions_typed :: "ctx \<Rightarrow> oterm list \<Rightarrow> bool" where
  "assumptions_typed \<Gamma> \<Delta> \<longleftrightarrow> (\<forall>A \<in> set \<Delta>. \<Gamma> \<turnstile> A : Prop)"

lemma satisfies_assumptions_typed:
  assumes "satisfies_assumptions \<Gamma> \<Delta> \<rho>"
  shows "assumptions_typed \<Gamma> \<Delta>"
  using assms unfolding satisfies_assumptions_def assumptions_typed_def by blast

definition semantically_entails :: "ctx \<Rightarrow> oterm list \<Rightarrow> oterm \<Rightarrow> bool"
    ("_ ; _ \<Turnstile>\<^sub>s _" [50, 50, 50] 50) where
  "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and>
    (\<forall>\<rho>. satisfies_assumptions \<Gamma> \<Delta> \<rho> \<longrightarrow> holds (eval \<rho> A))"

definition satisfiable_assumptions :: "ctx \<Rightarrow> oterm list \<Rightarrow> bool" where
  "satisfiable_assumptions \<Gamma> \<Delta> \<longleftrightarrow>
    (\<exists>\<rho>. satisfies_assumptions \<Gamma> \<Delta> \<rho>)"

definition countermodel_in_context :: "ctx \<Rightarrow> oterm \<Rightarrow> 'v env \<Rightarrow> bool" where
  "countermodel_in_context \<Gamma> A \<rho> \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and> env_typed \<Gamma> \<rho> \<and> \<not> holds (eval \<rho> A)"

definition has_countermodel :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" where
  "has_countermodel \<Gamma> A \<longleftrightarrow> (\<exists>\<rho>. countermodel_in_context \<Gamma> A \<rho>)"

definition countermodel_for_entailment ::
    "ctx \<Rightarrow> oterm list \<Rightarrow> oterm \<Rightarrow> 'v env \<Rightarrow> bool" where
  "countermodel_for_entailment \<Gamma> \<Delta> A \<rho> \<longleftrightarrow>
    \<Gamma> \<turnstile> A : Prop \<and> satisfies_assumptions \<Gamma> \<Delta> \<rho> \<and>
    \<not> holds (eval \<rho> A)"

definition has_entailment_countermodel :: "ctx \<Rightarrow> oterm list \<Rightarrow> oterm \<Rightarrow> bool" where
  "has_entailment_countermodel \<Gamma> \<Delta> A \<longleftrightarrow>
    (\<exists>\<rho>. countermodel_for_entailment \<Gamma> \<Delta> A \<rho>)"

lemma semantically_entails_formula:
  assumes "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
  shows "\<Gamma> \<turnstile> A : Prop"
  using assms unfolding semantically_entails_def by blast

lemma semantically_entails_holds:
  assumes "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
    and "satisfies_assumptions \<Gamma> \<Delta> \<rho>"
  shows "holds (eval \<rho> A)"
  using assms unfolding semantically_entails_def by blast

lemma valid_in_context_no_countermodel:
  assumes "valid_in_context \<Gamma> A"
  shows "\<not> has_countermodel \<Gamma> A"
  using assms
  unfolding valid_in_context_def has_countermodel_def countermodel_in_context_def
  by blast

lemma semantically_entails_no_countermodel:
  assumes "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
  shows "\<not> has_entailment_countermodel \<Gamma> \<Delta> A"
  using assms
  unfolding semantically_entails_def has_entailment_countermodel_def
    countermodel_for_entailment_def
  by blast

lemma H_derivable_sound:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  shows "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
  using assms
proof (induction rule: H_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  then show ?case
    unfolding semantically_entails_def satisfies_assumptions_def by blast
next
  case (Theorem \<Gamma> A \<Delta>)
  have valid: "valid_in_context \<Gamma> A"
    using Theorem.hyps by (rule H_soundness)
  then show ?case
    unfolding semantically_entails_def valid_in_context_def
      satisfies_assumptions_def
    by blast
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using Derive_MP.hyps(2) by (auto dest: H_derivable_formula elim: has_type.cases)
  have "\<forall>\<rho>. satisfies_assumptions \<Gamma> \<Delta> \<rho> \<longrightarrow> holds (eval \<rho> B)"
  proof (intro allI impI)
    fix \<rho>
    assume sat: "satisfies_assumptions \<Gamma> \<Delta> \<rho>"
    have A_holds: "holds (eval \<rho> A)"
      using Derive_MP.IH(1) sat by (rule semantically_entails_holds)
    have imp_holds: "holds (eval \<rho> (Imp A B))"
      using Derive_MP.IH(2) sat by (rule semantically_entails_holds)
    show "holds (eval \<rho> B)"
      using A_holds imp_holds by simp
  qed
  then show ?case
    unfolding semantically_entails_def using B_type by blast
qed

definition H_countermodel_property :: bool where
  "H_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>H A \<longrightarrow>
      has_countermodel \<Gamma> A)"

definition H_entailment_countermodel_property :: bool where
  "H_entailment_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> \<Delta> A. assumptions_typed \<Gamma> \<Delta> \<longrightarrow> \<Gamma> \<turnstile> A : Prop \<longrightarrow>
      \<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A \<longrightarrow>
      has_entailment_countermodel \<Gamma> \<Delta> A)"

theorem H_completeness_from_countermodels:
  assumes "H_countermodel_property"
    and "valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>H A"
proof (rule ccontr)
  assume not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>H A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule valid_formula)
  have "has_countermodel \<Gamma> A"
    using assms(1) A_type not_provable
    unfolding H_countermodel_property_def by blast
  then show False
    using valid_in_context_no_countermodel[OF assms(2)] by blast
qed

theorem H_strong_completeness_from_countermodels:
  assumes "H_entailment_countermodel_property"
    and "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
    and "assumptions_typed \<Gamma> \<Delta>"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
proof (rule ccontr)
  assume not_provable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>H A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule semantically_entails_formula)
  have "has_entailment_countermodel \<Gamma> \<Delta> A"
    using assms(1) assms(3) A_type not_provable
    unfolding H_entailment_countermodel_property_def by blast
  then show False
    using semantically_entails_no_countermodel[OF assms(2)] by blast
qed

end

context classicist_structure
begin

lemma C_derivable_sound:
  assumes "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  shows "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
  using assms
proof (induction rule: C_derivable.induct)
  case (Assumption A \<Delta> \<Gamma>)
  then show ?case
    unfolding semantically_entails_def satisfies_assumptions_def by blast
next
  case (Theorem \<Gamma> A \<Delta>)
  have valid: "valid_in_context \<Gamma> A"
    using Theorem.hyps by (rule C_soundness)
  then show ?case
    unfolding semantically_entails_def valid_in_context_def
      satisfies_assumptions_def
    by blast
next
  case (Derive_MP \<Gamma> \<Delta> A B)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using Derive_MP.hyps(2) by (auto dest: C_derivable_formula elim: has_type.cases)
  have "\<forall>\<rho>. satisfies_assumptions \<Gamma> \<Delta> \<rho> \<longrightarrow> holds (eval \<rho> B)"
  proof (intro allI impI)
    fix \<rho>
    assume sat: "satisfies_assumptions \<Gamma> \<Delta> \<rho>"
    have A_holds: "holds (eval \<rho> A)"
      using Derive_MP.IH(1) sat by (rule semantically_entails_holds)
    have imp_holds: "holds (eval \<rho> (Imp A B))"
      using Derive_MP.IH(2) sat by (rule semantically_entails_holds)
    show "holds (eval \<rho> B)"
      using A_holds imp_holds by simp
  qed
  then show ?case
    unfolding semantically_entails_def using B_type by blast
qed

definition C_countermodel_property :: bool where
  "C_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>C A \<longrightarrow>
      has_countermodel \<Gamma> A)"

definition C_entailment_countermodel_property :: bool where
  "C_entailment_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> \<Delta> A. assumptions_typed \<Gamma> \<Delta> \<longrightarrow> \<Gamma> \<turnstile> A : Prop \<longrightarrow>
      \<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A \<longrightarrow>
      has_entailment_countermodel \<Gamma> \<Delta> A)"

theorem C_completeness_from_countermodels:
  assumes "C_countermodel_property"
    and "valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>C A"
proof (rule ccontr)
  assume not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>C A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule valid_formula)
  have "has_countermodel \<Gamma> A"
    using assms(1) A_type not_provable
    unfolding C_countermodel_property_def by blast
  then show False
    using valid_in_context_no_countermodel[OF assms(2)] by blast
qed

theorem C_strong_completeness_from_countermodels:
  assumes "C_entailment_countermodel_property"
    and "\<Gamma> ; \<Delta> \<Turnstile>\<^sub>s A"
    and "assumptions_typed \<Gamma> \<Delta>"
  shows "\<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
proof (rule ccontr)
  assume not_provable: "\<not> \<Gamma> ; \<Delta> \<turnstile>\<^sub>C A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule semantically_entails_formula)
  have "has_entailment_countermodel \<Gamma> \<Delta> A"
    using assms(1) assms(3) A_type not_provable
    unfolding C_entailment_countermodel_property_def by blast
  then show False
    using semantically_entails_no_countermodel[OF assms(2)] by blast
qed

end

context propositional_equivalence_structure
begin

definition CE_countermodel_property :: bool where
  "CE_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>CE A \<longrightarrow>
      has_countermodel \<Gamma> A)"

theorem CE_completeness_from_countermodels:
  assumes "CE_countermodel_property"
    and "valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CE A"
proof (rule ccontr)
  assume not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CE A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule valid_formula)
  have "has_countermodel \<Gamma> A"
    using assms(1) A_type not_provable
    unfolding CE_countermodel_property_def by blast
  then show False
    using valid_in_context_no_countermodel[OF assms(2)] by blast
qed

end

context vector_equivalence_structure
begin

definition CEV_countermodel_property :: bool where
  "CEV_countermodel_property \<longleftrightarrow>
    (\<forall>\<Gamma> A. \<Gamma> \<turnstile> A : Prop \<longrightarrow> \<not> \<Gamma> \<turnstile>\<^sub>CEV A \<longrightarrow>
      has_countermodel \<Gamma> A)"

theorem CEV_completeness_from_countermodels:
  assumes "CEV_countermodel_property"
    and "valid_in_context \<Gamma> A"
  shows "\<Gamma> \<turnstile>\<^sub>CEV A"
proof (rule ccontr)
  assume not_provable: "\<not> \<Gamma> \<turnstile>\<^sub>CEV A"
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(2) by (rule valid_formula)
  have "has_countermodel \<Gamma> A"
    using assms(1) A_type not_provable
    unfolding CEV_countermodel_property_def by blast
  then show False
    using valid_in_context_no_countermodel[OF assms(2)] by blast
qed

end

end
