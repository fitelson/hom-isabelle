theory Bacon_Source_Relational_Quantifier_Axiom_Truth
  imports Bacon_Source_Relational_Logical_Truth Bacon_Source_Relational_Quasi_Functional_Denotation
begin

section \<open>Literal quantifier applications in the R language\<close>

text \<open>
  From F:σ→t we form ∀σF:t and ∃σF:t, retaining first-class
  logical constants. Source: §1.1, pp.5–6, and Figure 2, p.8.
  The operand guard entails σ∈R; no F-language inversion is used.
\<close>

lemma paper_R_named_quantifier_language:
  assumes predicate: "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
    and symbol: "paper_logical_type l = Arr (Arr \<sigma> Prop) Prop"
  shows "paper_R_in_language \<Sigma> G (NApp (NLogical l) F) Prop"
proof -
  have rt: "paper_R_type (Arr \<sigma> Prop)" by (rule paper_R_language_result_type[OF predicate])
  have lr: "paper_R_type (paper_logical_type l)" using rt by (simp add: symbol)
  have lt: "paper_R_has_type G (NLogical l) (Arr (Arr \<sigma> Prop) Prop)"
    using paper_R_has_type.Logical[where G=G, OF lr] by (simp only: symbol)
  have ll: "paper_R_in_language \<Sigma> G (NLogical l) (Arr (Arr \<sigma> Prop) Prop)"
    using lt by (simp add: paper_R_in_language_def)
  show ?thesis by (rule paper_R_language_App[OF ll predicate])
qed

lemma paper_R_named_all_language:
  "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop) \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_all \<sigma> F) Prop"
  unfolding named_paper_all_def
  by (rule paper_R_named_quantifier_language[OF _ paper_logical_type.simps(4)]; assumption)

lemma paper_R_named_ex_language:
  "paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop) \<Longrightarrow>
    paper_R_in_language \<Sigma> G (named_paper_ex \<sigma> F) Prop"
  unfolding named_paper_ex_def
  by (rule paper_R_named_quantifier_language[OF _ paper_logical_type.simps(5)]; assumption)

context paper_R_bbk_model
begin

lemma paper_R_forall_application_truth:
  assumes fl: "paper_R_in_language signature stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g F"
  shows "valuation (denote g (named_paper_all \<sigma> F)) =
    (\<forall>a\<in>domain \<sigma>. valuation (paper_R_application signature stock domain denote \<sigma> Prop (denote g F) a))"
proof -
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF fl]])
  obtain n where nt: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
    by (rule paper_R_rich_fresh[OF stock_rich rt named_fv_finite])
  have source_truth: "valuation (denote g (named_paper_all \<sigma> F)) =
      (\<forall>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) (NApp F (NVar n))))"
    unfolding named_paper_all_def by (rule valuation_forall[OF fl typed adequate nt fresh])
  have tests: "(\<forall>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) (NApp F (NVar n)))) =
      (\<forall>a\<in>domain \<sigma>. valuation (paper_R_application signature stock domain denote \<sigma> Prop (denote g F) a))"
  proof (rule ball_cong[OF refl])
    fix a
    assume member: "a \<in> domain \<sigma>"
    have equal: "paper_R_application signature stock domain denote \<sigma> Prop (denote g F) a =
        denote (g(n := Some a)) (NApp F (NVar n))"
      by (rule paper_R_fresh_application_denote[OF fl typed adequate nt fresh member])
    show "valuation (denote (g(n := Some a)) (NApp F (NVar n))) =
        valuation (paper_R_application signature stock domain denote \<sigma> Prop (denote g F) a)"
      by (simp only: equal)
  qed
  show ?thesis by (simp only: source_truth tests)
qed

lemma paper_R_exists_application_truth:
  assumes fl: "paper_R_in_language signature stock F (Arr \<sigma> Prop)"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g F"
  shows "valuation (denote g (named_paper_ex \<sigma> F)) =
    (\<exists>a\<in>domain \<sigma>. valuation (paper_R_application signature stock domain denote \<sigma> Prop (denote g F) a))"
proof -
  have rt: "paper_R_type \<sigma>" by (rule paper_R_arrow_domain[OF paper_R_language_result_type[OF fl]])
  obtain n where nt: "stock n = \<sigma>" and fresh: "n \<notin> named_fv F"
    by (rule paper_R_rich_fresh[OF stock_rich rt named_fv_finite])
  have source_truth: "valuation (denote g (named_paper_ex \<sigma> F)) =
      (\<exists>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) (NApp F (NVar n))))"
    unfolding named_paper_ex_def by (rule valuation_exists[OF fl typed adequate nt fresh])
  have tests: "(\<exists>a\<in>domain \<sigma>. valuation (denote (g(n := Some a)) (NApp F (NVar n)))) =
      (\<exists>a\<in>domain \<sigma>. valuation (paper_R_application signature stock domain denote \<sigma> Prop (denote g F) a))"
  proof (rule bex_cong[OF refl])
    fix a
    assume member: "a \<in> domain \<sigma>"
    have equal: "paper_R_application signature stock domain denote \<sigma> Prop (denote g F) a =
        denote (g(n := Some a)) (NApp F (NVar n))"
      by (rule paper_R_fresh_application_denote[OF fl typed adequate nt fresh member])
    show "valuation (denote (g(n := Some a)) (NApp F (NVar n))) =
        valuation (paper_R_application signature stock domain denote \<sigma> Prop (denote g F) a)"
      by (simp only: equal)
  qed
  show ?thesis by (simp only: source_truth tests)
qed

section \<open>UI and EG at adequate partial assignments\<close>

text \<open>
  ∀σF→FA and FA→∃σF are true whenever F:σ→t and A:σ
  belong to ℒ(Σ), and g is typed and adequate for both operands.
  Source: Figure 2, p.8. The witness is the actual value ⟦A⟧ᵍ.
  Implication remains the literal λ-defined Figure 1 operator.
  Status: axiom truth, not an assumed H theorem or a completeness claim.
\<close>

theorem paper_R_UI_truth:
  assumes fl: "paper_R_in_language signature stock F (Arr \<sigma> Prop)"
    and al: "paper_R_in_language signature stock A \<sigma>"
    and typed: "named_env_typed domain stock g" and fa: "named_adequate g F" and aa: "named_adequate g A"
  shows "valuation (denote g (named_paper_imp stock (named_paper_all \<sigma> F) (NApp F A)))"
proof -
  have ql: "paper_R_in_language signature stock (named_paper_all \<sigma> F) Prop"
    by (rule paper_R_named_all_language[OF fl])
  have apl: "paper_R_in_language signature stock (NApp F A) Prop" by (rule paper_R_language_App[OF fl al])
  have qa: "named_adequate g (named_paper_all \<sigma> F)"
    using fa by (simp only: named_adequate_def named_paper_primitive_fv)
  have apa: "named_adequate g (NApp F A)" using fa aa by (auto simp: named_adequate_def)
  have am: "denote g A \<in> domain \<sigma>" by (rule denote_type[OF al typed aa])
  have applied: "paper_R_application signature stock domain denote \<sigma> Prop (denote g F) (denote g A) = denote g (NApp F A)"
    by (rule paper_R_application_denote[OF fl al typed apa])
  have implication: "valuation (denote g (named_paper_imp stock (named_paper_all \<sigma> F) (NApp F A))) =
      (valuation (denote g (named_paper_all \<sigma> F)) \<longrightarrow> valuation (denote g (NApp F A)))"
    by (rule paper_R_named_paper_imp_truth[OF ql apl typed qa apa])
  have conditional: "valuation (denote g (named_paper_all \<sigma> F)) \<longrightarrow>
    valuation (denote g (NApp F A))"
  proof
    assume truth: "valuation (denote g (named_paper_all \<sigma> F))"
    have every: "\<forall>a\<in>domain \<sigma>. valuation
      (paper_R_application signature stock domain denote \<sigma> Prop (denote g F) a)"
      by (rule iffD1[OF paper_R_forall_application_truth[OF fl typed fa] truth])
    have witness_truth: "valuation
      (paper_R_application signature stock domain denote \<sigma> Prop (denote g F) (denote g A))"
      by (rule bspec[OF every am])
    show "valuation (denote g (NApp F A))" using witness_truth by (simp only: applied)
  qed
  show ?thesis by (rule iffD2[OF implication conditional])
qed

theorem paper_R_EG_truth:
  assumes fl: "paper_R_in_language signature stock F (Arr \<sigma> Prop)"
    and al: "paper_R_in_language signature stock A \<sigma>"
    and typed: "named_env_typed domain stock g" and fa: "named_adequate g F" and aa: "named_adequate g A"
  shows "valuation (denote g (named_paper_imp stock (NApp F A) (named_paper_ex \<sigma> F)))"
proof -
  have ql: "paper_R_in_language signature stock (named_paper_ex \<sigma> F) Prop"
    by (rule paper_R_named_ex_language[OF fl])
  have apl: "paper_R_in_language signature stock (NApp F A) Prop" by (rule paper_R_language_App[OF fl al])
  have qa: "named_adequate g (named_paper_ex \<sigma> F)"
    using fa by (simp only: named_adequate_def named_paper_primitive_fv)
  have apa: "named_adequate g (NApp F A)" using fa aa by (auto simp: named_adequate_def)
  have am: "denote g A \<in> domain \<sigma>" by (rule denote_type[OF al typed aa])
  have applied: "paper_R_application signature stock domain denote \<sigma> Prop (denote g F) (denote g A) = denote g (NApp F A)"
    by (rule paper_R_application_denote[OF fl al typed apa])
  have implication: "valuation (denote g (named_paper_imp stock (NApp F A) (named_paper_ex \<sigma> F))) =
      (valuation (denote g (NApp F A)) \<longrightarrow> valuation (denote g (named_paper_ex \<sigma> F)))"
    by (rule paper_R_named_paper_imp_truth[OF apl ql typed apa qa])
  have conditional: "valuation (denote g (NApp F A)) \<longrightarrow>
    valuation (denote g (named_paper_ex \<sigma> F))"
  proof
    assume truth: "valuation (denote g (NApp F A))"
    have witness_truth: "valuation
      (paper_R_application signature stock domain denote \<sigma> Prop (denote g F) (denote g A))"
      by (simp only: applied; rule truth)
    have some: "\<exists>a\<in>domain \<sigma>. valuation
      (paper_R_application signature stock domain denote \<sigma> Prop (denote g F) a)"
      by (rule bexI[where x="denote g A"]; (rule witness_truth | rule am))
    show "valuation (denote g (named_paper_ex \<sigma> F))"
      by (rule iffD2[OF paper_R_exists_application_truth[OF fl typed fa] some])
  qed
  show ?thesis by (rule iffD2[OF implication conditional])
qed

end

end
