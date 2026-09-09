theory Bacon_Source_Relational_Propositional_Truth
  imports Bacon_Source_Relational_Propositional_Inversion Bacon_Source_Relational_Logical_Truth
begin

section \<open>Boolean evaluation of a guarded R template instance\<close>

text \<open>
  The truth of a named Boolean instance is its template's Boolean
  evaluation at the truths of the substituted atoms (Figure 2, p.8).
  Induction recovers the R-language and adequacy guards at each
  connective; → and ↔ use their checked literal λ-operator truths.
  No F-model or proof-translation theorem supplies the conclusion.
\<close>

context paper_R_bbk_model
begin

lemma paper_R_named_instance_truth:
  assumes language: "paper_R_in_language signature stock (named_paper_prop_instance stock v P) Prop"
    and typed: "named_env_typed domain stock g"
    and adequate: "named_adequate g (named_paper_prop_instance stock v P)"
  shows "valuation (denote g (named_paper_prop_instance stock v P)) =
    sprop_eval (\<lambda>a. valuation (denote g (v a))) P"
  using language adequate
proof (induction P)
  case (SPAtom a)
  show ?case by (simp only: named_paper_prop_instance.simps sprop_eval.simps)
next
  case (SPNot P)
  have pl: "paper_R_in_language signature stock (named_paper_prop_instance stock v P) Prop"
    by (rule paper_R_not_language_operand[OF SPNot.prems(1)[unfolded named_paper_prop_instance.simps]])
  have pa: "named_adequate g (named_paper_prop_instance stock v P)"
    using SPNot.prems(2) by (simp only: named_paper_prop_instance.simps paper_R_named_connective_adequacy(1))
  have induction_step: "valuation (denote g (named_paper_prop_instance stock v P)) =
    sprop_eval (\<lambda>a. valuation (denote g (v a))) P" by (rule SPNot.IH[OF pl pa])
  show ?case by (simp only: named_paper_prop_instance.simps sprop_eval.simps
    paper_R_named_not_truth[OF pl typed pa] induction_step)
next
  case (SPAnd P Q)
  have parts: "paper_R_in_language signature stock (named_paper_prop_instance stock v P) Prop \<and>
    paper_R_in_language signature stock (named_paper_prop_instance stock v Q) Prop"
    by (rule paper_R_and_language_operands[OF SPAnd.prems(1)[unfolded named_paper_prop_instance.simps]])
  have pl: "paper_R_in_language signature stock (named_paper_prop_instance stock v P) Prop"
    by (rule conjunct1[OF parts])
  have ql: "paper_R_in_language signature stock (named_paper_prop_instance stock v Q) Prop"
    by (rule conjunct2[OF parts])
  have both: "named_adequate g (named_paper_prop_instance stock v P) \<and>
    named_adequate g (named_paper_prop_instance stock v Q)"
    using SPAnd.prems(2) by (simp only: named_paper_prop_instance.simps paper_R_named_connective_adequacy(2))
  have pa: "named_adequate g (named_paper_prop_instance stock v P)" by (rule conjunct1[OF both])
  have qa: "named_adequate g (named_paper_prop_instance stock v Q)" by (rule conjunct2[OF both])
  have left: "valuation (denote g (named_paper_prop_instance stock v P)) =
    sprop_eval (\<lambda>a. valuation (denote g (v a))) P" by (rule SPAnd.IH(1)[OF pl pa])
  have right: "valuation (denote g (named_paper_prop_instance stock v Q)) =
    sprop_eval (\<lambda>a. valuation (denote g (v a))) Q" by (rule SPAnd.IH(2)[OF ql qa])
  show ?case by (simp only: named_paper_prop_instance.simps sprop_eval.simps
    paper_R_named_and_truth[OF pl ql typed pa qa] left right)
next
  case (SPOr P Q)
  have parts: "paper_R_in_language signature stock (named_paper_prop_instance stock v P) Prop \<and>
    paper_R_in_language signature stock (named_paper_prop_instance stock v Q) Prop"
    by (rule paper_R_or_language_operands[OF SPOr.prems(1)[unfolded named_paper_prop_instance.simps]])
  have pl: "paper_R_in_language signature stock (named_paper_prop_instance stock v P) Prop"
    by (rule conjunct1[OF parts])
  have ql: "paper_R_in_language signature stock (named_paper_prop_instance stock v Q) Prop"
    by (rule conjunct2[OF parts])
  have both: "named_adequate g (named_paper_prop_instance stock v P) \<and>
    named_adequate g (named_paper_prop_instance stock v Q)"
    using SPOr.prems(2) by (simp only: named_paper_prop_instance.simps paper_R_named_connective_adequacy(3))
  have pa: "named_adequate g (named_paper_prop_instance stock v P)" by (rule conjunct1[OF both])
  have qa: "named_adequate g (named_paper_prop_instance stock v Q)" by (rule conjunct2[OF both])
  have left: "valuation (denote g (named_paper_prop_instance stock v P)) =
    sprop_eval (\<lambda>a. valuation (denote g (v a))) P" by (rule SPOr.IH(1)[OF pl pa])
  have right: "valuation (denote g (named_paper_prop_instance stock v Q)) =
    sprop_eval (\<lambda>a. valuation (denote g (v a))) Q" by (rule SPOr.IH(2)[OF ql qa])
  show ?case by (simp only: named_paper_prop_instance.simps sprop_eval.simps
    paper_R_named_or_truth[OF pl ql typed pa qa] left right)
next
  case (SPImp P Q)
  have parts: "paper_R_in_language signature stock (named_paper_prop_instance stock v P) Prop \<and>
    paper_R_in_language signature stock (named_paper_prop_instance stock v Q) Prop"
    by (rule paper_R_imp_language_operands[OF stock_rich SPImp.prems(1)[unfolded named_paper_prop_instance.simps]])
  have pl: "paper_R_in_language signature stock (named_paper_prop_instance stock v P) Prop"
    by (rule conjunct1[OF parts])
  have ql: "paper_R_in_language signature stock (named_paper_prop_instance stock v Q) Prop"
    by (rule conjunct2[OF parts])
  have both: "named_adequate g (named_paper_prop_instance stock v P) \<and>
    named_adequate g (named_paper_prop_instance stock v Q)"
    using SPImp.prems(2) by (simp only: named_paper_prop_instance.simps paper_R_named_connective_adequacy(4))
  have pa: "named_adequate g (named_paper_prop_instance stock v P)" by (rule conjunct1[OF both])
  have qa: "named_adequate g (named_paper_prop_instance stock v Q)" by (rule conjunct2[OF both])
  have left: "valuation (denote g (named_paper_prop_instance stock v P)) =
    sprop_eval (\<lambda>a. valuation (denote g (v a))) P" by (rule SPImp.IH(1)[OF pl pa])
  have right: "valuation (denote g (named_paper_prop_instance stock v Q)) =
    sprop_eval (\<lambda>a. valuation (denote g (v a))) Q" by (rule SPImp.IH(2)[OF ql qa])
  show ?case by (simp only: named_paper_prop_instance.simps sprop_eval.simps
    paper_R_named_paper_imp_truth[OF pl ql typed pa qa] left right)
next
  case (SPIff P Q)
  have parts: "paper_R_in_language signature stock (named_paper_prop_instance stock v P) Prop \<and>
    paper_R_in_language signature stock (named_paper_prop_instance stock v Q) Prop"
    by (rule paper_R_iff_language_operands[OF stock_rich SPIff.prems(1)[unfolded named_paper_prop_instance.simps]])
  have pl: "paper_R_in_language signature stock (named_paper_prop_instance stock v P) Prop"
    by (rule conjunct1[OF parts])
  have ql: "paper_R_in_language signature stock (named_paper_prop_instance stock v Q) Prop"
    by (rule conjunct2[OF parts])
  have both: "named_adequate g (named_paper_prop_instance stock v P) \<and>
    named_adequate g (named_paper_prop_instance stock v Q)"
    using SPIff.prems(2) by (simp only: named_paper_prop_instance.simps paper_R_named_connective_adequacy(5))
  have pa: "named_adequate g (named_paper_prop_instance stock v P)" by (rule conjunct1[OF both])
  have qa: "named_adequate g (named_paper_prop_instance stock v Q)" by (rule conjunct2[OF both])
  have left: "valuation (denote g (named_paper_prop_instance stock v P)) =
    sprop_eval (\<lambda>a. valuation (denote g (v a))) P" by (rule SPIff.IH(1)[OF pl pa])
  have right: "valuation (denote g (named_paper_prop_instance stock v Q)) =
    sprop_eval (\<lambda>a. valuation (denote g (v a))) Q" by (rule SPIff.IH(2)[OF ql qa])
  show ?case by (simp only: named_paper_prop_instance.simps sprop_eval.simps
    paper_R_named_paper_iff_truth[OF pl ql typed pa qa] left right)
qed

section \<open>PC is true at each typed adequate partial assignment\<close>

theorem paper_R_named_PC_truth:
  assumes pc: "paper_R_named_PC signature stock A"
    and typed: "named_env_typed domain stock g" and adequate: "named_adequate g A"
  shows "valuation (denote g A)"
proof -
  have language: "paper_R_in_language signature stock A Prop" by (rule paper_R_named_PC_language[OF pc])
  obtain P :: "nat sprop_template" and v where taut: "sprop_tautology P"
    and shape: "A = named_paper_prop_instance stock v P"
    using pc unfolding paper_R_named_PC_def by blast
  have instance_language: "paper_R_in_language signature stock (named_paper_prop_instance stock v P) Prop"
    using language by (simp only: shape)
  have instance_adequate: "named_adequate g (named_paper_prop_instance stock v P)"
    using adequate by (simp only: shape)
  have evaluated: "valuation (denote g (named_paper_prop_instance stock v P)) =
    sprop_eval (\<lambda>a. valuation (denote g (v a))) P"
    by (rule paper_R_named_instance_truth[OF instance_language typed instance_adequate])
  have boolean_truth: "sprop_eval (\<lambda>a. valuation (denote g (v a))) P"
    using taut unfolding sprop_tautology_def by (rule spec)
  show ?thesis by (simp only: shape evaluated; rule boolean_truth)
qed

end

end
