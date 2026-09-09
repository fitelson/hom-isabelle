theory Bacon_Source_Relational_Basic_Axiom_Validity
  imports Bacon_Source_Relational_Quantifier_Axiom_Truth
    Bacon_Source_Relational_Identity_Axiom_Truth Bacon_Source_Relational_Language_Inversion
begin

section \<open>Recovering application operands at an already fixed type\<close>

lemma paper_R_application_argument_language:
  assumes head: "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
    and application: "paper_R_in_language \<Sigma> G (NApp F A) \<tau>"
  shows "paper_R_in_language \<Sigma> G A \<sigma>"
proof -
  obtain \<upsilon> where fl: "paper_R_in_language \<Sigma> G F (Arr \<upsilon> \<tau>)"
    and al: "paper_R_in_language \<Sigma> G A \<upsilon>" by (rule paper_R_language_AppE[OF application])
  have ft: "paper_R_has_type G F (Arr \<sigma> \<tau>)" and fu: "paper_R_has_type G F (Arr \<upsilon> \<tau>)"
    using head fl unfolding paper_R_in_language_def by blast+
  have equal: "Arr \<sigma> \<tau> = Arr \<upsilon> \<tau>" by (rule paper_R_type_unique[OF ft fu])
  show ?thesis using equal al by simp
qed

lemma paper_R_application_function_language:
  assumes argument: "paper_R_in_language \<Sigma> G A \<sigma>"
    and application: "paper_R_in_language \<Sigma> G (NApp F A) \<tau>"
  shows "paper_R_in_language \<Sigma> G F (Arr \<sigma> \<tau>)"
proof -
  obtain \<upsilon> where fl: "paper_R_in_language \<Sigma> G F (Arr \<upsilon> \<tau>)"
    and al: "paper_R_in_language \<Sigma> G A \<upsilon>" by (rule paper_R_language_AppE[OF application])
  have at: "paper_R_has_type G A \<sigma>" and au: "paper_R_has_type G A \<upsilon>"
    using argument al unfolding paper_R_in_language_def by blast+
  have equal: "\<sigma> = \<upsilon>" by (rule paper_R_type_unique[OF at au])
  show ?thesis using fl by (simp only: equal)
qed

section \<open>The whole-formula guards of Figure 2 suffice\<close>

text \<open>
  Every well-formed R instance of UI, EG, Ref, and LL is valid.
  Source: Figure 2, p.8, and Definition 3.1, pp.43–44. These endpoints
  use exactly the whole-axiom language guards of the native constructors.
  Typing inversion recovers operand types; adequacy descends through the
  literal connectives. Status: four semantic axiom cases, not a proof
  induction or an F-to-R proof-conservativity assumption.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_UI_valid:
  assumes whole: "paper_R_in_language signature stock
    (named_paper_imp stock (named_paper_all \<sigma> F) (NApp F A)) Prop"
  shows "paper_R_valid (named_paper_imp stock (named_paper_all \<sigma> F) (NApp F A))"
proof -
  have ql: "paper_R_in_language signature stock (named_paper_all \<sigma> F) Prop"
    and apl: "paper_R_in_language signature stock (NApp F A) Prop"
    using paper_R_imp_language_operands[OF stock_rich whole] by blast+
  have fl: "paper_R_in_language signature stock F (Arr \<sigma> Prop)" by (rule paper_R_all_language_operand[OF ql])
  have al: "paper_R_in_language signature stock A \<sigma>" by (rule paper_R_application_argument_language[OF fl apl])
  show ?thesis unfolding paper_R_valid_def paper_R_satisfies_def
  proof (rule conjI[OF whole], intro allI impI)
    fix g
    assume typed: "named_env_typed domain stock g"
      and adequate: "named_adequate g (named_paper_imp stock (named_paper_all \<sigma> F) (NApp F A))"
    have fa: "named_adequate g F" and aa: "named_adequate g A"
      using adequate by (auto simp: named_adequate_def named_paper_defined_fv named_paper_primitive_fv)
    show "valuation (denote g (named_paper_imp stock (named_paper_all \<sigma> F) (NApp F A)))"
      by (rule paper_R_UI_truth[OF fl al typed fa aa])
  qed
qed

theorem paper_R_EG_valid:
  assumes whole: "paper_R_in_language signature stock
    (named_paper_imp stock (NApp F A) (named_paper_ex \<sigma> F)) Prop"
  shows "paper_R_valid (named_paper_imp stock (NApp F A) (named_paper_ex \<sigma> F))"
proof -
  have apl: "paper_R_in_language signature stock (NApp F A) Prop"
    and ql: "paper_R_in_language signature stock (named_paper_ex \<sigma> F) Prop"
    using paper_R_imp_language_operands[OF stock_rich whole] by blast+
  have fl: "paper_R_in_language signature stock F (Arr \<sigma> Prop)" by (rule paper_R_ex_language_operand[OF ql])
  have al: "paper_R_in_language signature stock A \<sigma>" by (rule paper_R_application_argument_language[OF fl apl])
  show ?thesis unfolding paper_R_valid_def paper_R_satisfies_def
  proof (rule conjI[OF whole], intro allI impI)
    fix g
    assume typed: "named_env_typed domain stock g"
      and adequate: "named_adequate g (named_paper_imp stock (NApp F A) (named_paper_ex \<sigma> F))"
    have fa: "named_adequate g F" and aa: "named_adequate g A"
      using adequate by (auto simp: named_adequate_def named_paper_defined_fv named_paper_primitive_fv)
    show "valuation (denote g (named_paper_imp stock (NApp F A) (named_paper_ex \<sigma> F)))"
      by (rule paper_R_EG_truth[OF fl al typed fa aa])
  qed
qed

theorem paper_R_Ref_valid:
  assumes whole: "paper_R_in_language signature stock (named_paper_eq \<sigma> A A) Prop"
  shows "paper_R_valid (named_paper_eq \<sigma> A A)"
proof -
  have al: "paper_R_in_language signature stock A \<sigma>"
    using paper_R_eq_language_operands[OF whole] by blast
  show ?thesis unfolding paper_R_valid_def paper_R_satisfies_def
  proof (rule conjI[OF whole], intro allI impI)
    fix g
    assume typed: "named_env_typed domain stock g" and adequate: "named_adequate g (named_paper_eq \<sigma> A A)"
    have aa: "named_adequate g A" using adequate by (simp add: named_adequate_def named_paper_primitive_fv)
    show "valuation (denote g (named_paper_eq \<sigma> A A))" by (rule paper_R_Ref_truth[OF al typed aa])
  qed
qed

theorem paper_R_LL_valid:
  assumes whole: "paper_R_in_language signature stock (named_paper_imp stock (named_paper_eq \<sigma> A B)
    (named_paper_imp stock (NApp F A) (NApp F B))) Prop"
  shows "paper_R_valid (named_paper_imp stock (named_paper_eq \<sigma> A B)
    (named_paper_imp stock (NApp F A) (NApp F B)))"
proof -
  have el: "paper_R_in_language signature stock (named_paper_eq \<sigma> A B) Prop"
    and il: "paper_R_in_language signature stock (named_paper_imp stock (NApp F A) (NApp F B)) Prop"
    using paper_R_imp_language_operands[OF stock_rich whole] by blast+
  have al: "paper_R_in_language signature stock A \<sigma>" and bl: "paper_R_in_language signature stock B \<sigma>"
    using paper_R_eq_language_operands[OF el] by blast+
  have fal: "paper_R_in_language signature stock (NApp F A) Prop"
    using paper_R_imp_language_operands[OF stock_rich il] by blast
  have fl: "paper_R_in_language signature stock F (Arr \<sigma> Prop)"
    by (rule paper_R_application_function_language[OF al fal])
  show ?thesis unfolding paper_R_valid_def paper_R_satisfies_def
  proof (rule conjI[OF whole], intro allI impI)
    fix g
    assume typed: "named_env_typed domain stock g"
      and adequate: "named_adequate g (named_paper_imp stock (named_paper_eq \<sigma> A B)
        (named_paper_imp stock (NApp F A) (NApp F B)))"
    have aa: "named_adequate g A" and ba: "named_adequate g B" and fa: "named_adequate g F"
      using adequate by (auto simp: named_adequate_def named_paper_defined_fv named_paper_primitive_fv)
    show "valuation (denote g (named_paper_imp stock (named_paper_eq \<sigma> A B)
        (named_paper_imp stock (NApp F A) (NApp F B))))"
      by (rule paper_R_LL_truth[OF al bl fl typed aa ba fa])
  qed
qed

end

end
