theory Bacon_Source_Relational_Language_Inversion
  imports Bacon_Source_Relational_Logical_Language
begin

section \<open>Recovering the R-language operands of literal connectives\<close>

text \<open>
  A well-formed ¬A, A∧B, A∨B, A→B or A↔B has proposition
  operands. Likewise A=σB has σ operands and ∀σF, ∃σF have
  σ→t predicates. Source: §1.1 and Figure 1, pp.5–6.
  These inversions use the independent R typing judgment and declared
  nonlogical signatures. The defined → and ↔ remain λ applications.
  Their known operator types below use R-richness, not F-richness.
\<close>

lemma paper_R_language_AppE:
  assumes whole: "paper_R_in_language \<Sigma> G (NApp F A) \<tau>"
  obtains \<sigma> where "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)" "paper_R_in_language \<Sigma> G A \<sigma>"
proof -
  have typed: "paper_R_has_type G (NApp F A) \<tau>" and names: "named_in_signature \<Sigma> (NApp F A)"
    using whole unfolding paper_R_in_language_def by blast+
  obtain \<sigma> where ft: "paper_R_has_type G F (Arr \<sigma> \<tau>)" and at: "paper_R_has_type G A \<sigma>"
    by (rule paper_R_app_type_obtain[OF typed])
  have fl: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    using ft names by (simp add: paper_R_in_language_def)
  have al: "paper_R_in_language \<Sigma> G A \<sigma>"
    using at names by (simp add: paper_R_in_language_def)
  show thesis by (rule that[OF fl al])
qed

lemma paper_R_binary_operator_operands:
  assumes operator: "paper_R_has_type G L (Arr \<sigma> (Arr \<rho> \<tau>))"
    and whole: "paper_R_in_language \<Sigma> G (NApp (NApp L A) B) \<tau>"
  shows "paper_R_in_language \<Sigma> G A \<sigma> \<and> paper_R_in_language \<Sigma> G B \<rho>"
proof -
  obtain \<delta> where partial: "paper_R_in_language \<Sigma> G (NApp L A) (Arr \<delta> \<tau>)"
    and bl: "paper_R_in_language \<Sigma> G B \<delta>" by (rule paper_R_language_AppE[OF whole])
  obtain \<gamma> where ll: "paper_R_in_language \<Sigma> G L (Arr \<gamma> (Arr \<delta> \<tau>))"
    and al: "paper_R_in_language \<Sigma> G A \<gamma>" by (rule paper_R_language_AppE[OF partial])
  have lt: "paper_R_has_type G L (Arr \<gamma> (Arr \<delta> \<tau>))"
    using ll unfolding paper_R_in_language_def by (rule conjunct1)
  have equality: "Arr \<sigma> (Arr \<rho> \<tau>) = Arr \<gamma> (Arr \<delta> \<tau>)"
    by (rule paper_R_type_unique[OF operator lt])
  show ?thesis using equality al bl by auto
qed

lemma paper_R_logical_unary_operand:
  fixes \<Sigma> :: "'c ssignature"
  assumes symbol: "paper_logical_type l = Arr \<sigma> \<rho>"
    and whole: "paper_R_in_language \<Sigma> G (NApp (NLogical l) A) \<tau>"
  shows "paper_R_in_language \<Sigma> G A \<sigma>"
proof -
  obtain \<delta> where ll: "paper_R_in_language \<Sigma> G (NLogical l) (Arr \<delta> \<tau>)"
    and al: "paper_R_in_language \<Sigma> G A \<delta>" by (rule paper_R_language_AppE[OF whole])
  have lt: "paper_R_has_type G (NLogical l :: 'c paper_named_term) (Arr \<delta> \<tau>)"
    using ll unfolding paper_R_in_language_def by (rule conjunct1)
  have equality: "Arr \<delta> \<tau> = paper_logical_type l"
    by (rule conjunct1[OF iffD1[OF paper_R_logical_type_iff lt]])
  show ?thesis using equality symbol al by auto
qed

lemma paper_R_logical_binary_operands:
  fixes \<Sigma> :: "'c ssignature"
  assumes symbol: "paper_logical_type l = Arr \<sigma> (Arr \<rho> \<nu>)"
    and whole: "paper_R_in_language \<Sigma> G (NApp (NApp (NLogical l) A) B) \<tau>"
  shows "paper_R_in_language \<Sigma> G A \<sigma> \<and> paper_R_in_language \<Sigma> G B \<rho>"
proof -
  obtain \<delta> where partial: "paper_R_in_language \<Sigma> G (NApp (NLogical l) A) (Arr \<delta> \<tau>)"
    and bl: "paper_R_in_language \<Sigma> G B \<delta>" by (rule paper_R_language_AppE[OF whole])
  obtain \<gamma> where ll: "paper_R_in_language \<Sigma> G (NLogical l) (Arr \<gamma> (Arr \<delta> \<tau>))"
    and al: "paper_R_in_language \<Sigma> G A \<gamma>" by (rule paper_R_language_AppE[OF partial])
  have lt: "paper_R_has_type G (NLogical l :: 'c paper_named_term) (Arr \<gamma> (Arr \<delta> \<tau>))"
    using ll unfolding paper_R_in_language_def by (rule conjunct1)
  have equality: "Arr \<gamma> (Arr \<delta> \<tau>) = paper_logical_type l"
    by (rule conjunct1[OF iffD1[OF paper_R_logical_type_iff lt]])
  show ?thesis using equality symbol al bl by auto
qed

lemma paper_R_not_language_operand:
  "paper_R_in_language \<Sigma> G (named_paper_not A) Prop \<Longrightarrow> paper_R_in_language \<Sigma> G A Prop"
  unfolding named_paper_not_def
  by (rule paper_R_logical_unary_operand[OF paper_logical_type.simps(1)]; assumption)

lemma paper_R_and_language_operands:
  "paper_R_in_language \<Sigma> G (named_paper_and A B) Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> G A Prop \<and> paper_R_in_language \<Sigma> G B Prop"
  unfolding named_paper_and_def
  by (rule paper_R_logical_binary_operands[OF paper_logical_type.simps(2)]; assumption)

lemma paper_R_or_language_operands:
  "paper_R_in_language \<Sigma> G (named_paper_or A B) Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> G A Prop \<and> paper_R_in_language \<Sigma> G B Prop"
  unfolding named_paper_or_def
  by (rule paper_R_logical_binary_operands[OF paper_logical_type.simps(3)]; assumption)

lemma paper_R_eq_language_operands:
  "paper_R_in_language \<Sigma> G (named_paper_eq \<sigma> A B) Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> G A \<sigma> \<and> paper_R_in_language \<Sigma> G B \<sigma>"
  unfolding named_paper_eq_def
  by (rule paper_R_logical_binary_operands[OF paper_logical_type.simps(6)]; assumption)

lemma paper_R_all_language_operand:
  "paper_R_in_language \<Sigma> G (named_paper_all \<sigma> F) Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
  unfolding named_paper_all_def
  by (rule paper_R_logical_unary_operand[OF paper_logical_type.simps(4)]; assumption)

lemma paper_R_ex_language_operand:
  "paper_R_in_language \<Sigma> G (named_paper_ex \<sigma> F) Prop \<Longrightarrow>
    paper_R_in_language \<Sigma> G F (Arr \<sigma> Prop)"
  unfolding named_paper_ex_def
  by (rule paper_R_logical_unary_operand[OF paper_logical_type.simps(5)]; assumption)

lemma paper_R_imp_language_operands:
  assumes rich: "paper_R_rich G" and whole: "paper_R_in_language \<Sigma> G (named_paper_imp G A B) Prop"
  shows "paper_R_in_language \<Sigma> G A Prop \<and> paper_R_in_language \<Sigma> G B Prop"
  by (rule paper_R_binary_operator_operands[OF paper_R_named_paper_imp_const_type[OF rich]
    whole[unfolded named_paper_imp_def]])

lemma paper_R_iff_language_operands:
  assumes rich: "paper_R_rich G" and whole: "paper_R_in_language \<Sigma> G (named_paper_iff G A B) Prop"
  shows "paper_R_in_language \<Sigma> G A Prop \<and> paper_R_in_language \<Sigma> G B Prop"
  by (rule paper_R_binary_operator_operands[OF paper_R_named_paper_iff_const_type[OF rich]
    whole[unfolded named_paper_iff_def]])

section \<open>Adequacy descends to Boolean operands\<close>

lemma paper_R_named_connective_adequacy:
  "named_adequate g (named_paper_not A) \<longleftrightarrow> named_adequate g A"
  "named_adequate g (named_paper_and A B) \<longleftrightarrow> named_adequate g A \<and> named_adequate g B"
  "named_adequate g (named_paper_or A B) \<longleftrightarrow> named_adequate g A \<and> named_adequate g B"
  "named_adequate g (named_paper_imp G A B) \<longleftrightarrow> named_adequate g A \<and> named_adequate g B"
  "named_adequate g (named_paper_iff G A B) \<longleftrightarrow> named_adequate g A \<and> named_adequate g B"
  by (auto simp only: named_adequate_def named_paper_primitive_fv named_paper_defined_fv)

end
