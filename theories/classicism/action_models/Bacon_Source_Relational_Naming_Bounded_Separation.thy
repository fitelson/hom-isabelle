theory Bacon_Source_Relational_Naming_Bounded_Separation
  imports Bacon_Source_Relational_Naming_Separating_Reduct
    Bacon_Source_Relational_Naming_Signature_Cardinal
    Bacon_Source_Relational_Positive_Diagram_Separating_Bounded
    Bacon_Source_Relational_Parameter_H_Theory Bacon_Source_Relational_Parameter_Validity
begin

section \<open>A separating homomorphic target inside a prescribed infinite carrier\<close>

text \<open>
  If both the declared names and the actual union of M's domains have
  cardinal at most |U|, the naming signature has that bound. The bounded
  separating-model theorem supplies N⁺ with all domains inside U; its
  reduct retains those domains and validates the original theory T.
  Source: p.51–52 n.73 and the fixed-carrier refinement on p.52.

  The source value carrier and the carrier containing U may differ.
  No bound on either entire ambient HOL type is required. The map is
  denotation-preserving, while its images of p and q have different
  target truth values. This does not assert truth preservation.
\<close>

context paper_R_bbk_model
begin

theorem paper_R_naming_bounded_proposition_separation:
  fixes U :: "'u set"
  assumes infinite: "infinite U"
    and names: "card_of (\<Union>\<sigma>. signature \<sigma>) \<le>o card_of U"
    and parameters: "card_of (\<Union>\<sigma>. domain \<sigma>) \<le>o card_of U"
    and theory_h: "paper_R_H_theory signature stock T"
    and pe: "paper_R_PE_closed signature stock T"
    and valid_source: "\<forall>A\<in>T. paper_R_valid A"
    and pm: "p \<in> domain Prop" and qm: "q \<in> domain Prop" and different: "p \<noteq> q"
  shows "\<exists>E :: otype \<Rightarrow> 'u set.
    \<exists>L :: 'u named_assignment \<Rightarrow> 'c paper_named_term \<Rightarrow> 'u.
    \<exists>W :: 'u \<Rightarrow> bool. \<exists>h :: otype \<Rightarrow> 'v \<Rightarrow> 'u.
      paper_R_bbk_model signature stock E L W \<and>
      (\<Union>\<sigma>. E \<sigma>) \<subseteq> U \<and>
      (\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid signature stock E L W A) \<and>
      paper_R_bbk_homomorphism signature stock domain denote E L h \<and>
      W (h Prop p) \<noteq> W (h Prop q)"
proof -
  let ?Sig = "paper_R_naming_signature signature domain"
  let ?T = "paper_R_parameter_theory signature stock domain T"
  let ?P = "NConst (Inr p) Prop :: ('c + 'v) paper_named_term"
  let ?Q = "NConst (Inr q) Prop :: ('c + 'v) paper_named_term"
  interpret Expanded: paper_R_bbk_model ?Sig stock domain paper_R_naming_denote valuation
    by (rule paper_R_naming_model)
  have expanded_names: "card_of (\<Union>\<sigma>. ?Sig \<sigma>) \<le>o card_of U"
    by (rule paper_R_naming_signature_cardinal_bound[OF infinite names parameters])
  have parameter_h: "paper_R_H_theory ?Sig stock ?T"
    by (rule paper_R_H_theory_parameter[OF stock_rich theory_h])
  have parameter_pe: "paper_R_PE_closed ?Sig stock ?T"
    by (rule paper_R_parameter_theory_PE_closed[OF stock_rich theory_h pe])
  have parameter_valid: "\<forall>A\<in>?T. Expanded.paper_R_valid A"
    by (rule paper_R_parameter_theory_valid[OF valid_source])
  have parameter_at: "Expanded.paper_R_valid A" if "A \<in> ?T" for A
    using parameter_valid that by blast
  have pt: "paper_R_has_type stock ?P Prop" and qt: "paper_R_has_type stock ?Q Prop"
    by (rule paper_R_has_type.Const; simp)+
  have pl: "paper_R_in_language ?Sig stock ?P Prop" and ql: "paper_R_in_language ?Sig stock ?Q Prop"
    using pt qt pm qm by (simp_all add: paper_R_in_language_def)
  have pc: "named_fv ?P = {}" and qc: "named_fv ?Q = {}" by simp_all
  have empty_typed: "named_env_typed domain stock Map.empty" by (simp add: named_env_typed_def)
  have pv: "paper_R_naming_denote Map.empty ?P = p"
    by (rule paper_R_naming_denote_value_constant[OF pm empty_typed])
  have qv: "paper_R_naming_denote Map.empty ?Q = q"
    by (rule paper_R_naming_denote_value_constant[OF qm empty_typed])
  have names_different: "paper_R_naming_denote Map.empty ?P \<noteq> paper_R_naming_denote Map.empty ?Q"
    by (simp only: pv qv; rule different)
  obtain E :: "otype \<Rightarrow> 'u set" and K and W
    where model: "paper_R_bbk_model ?Sig stock E K W"
    and bounded: "(\<Union>\<sigma>. E \<sigma>) \<subseteq> U"
    and theory_valid: "\<forall>A\<in>?T. paper_R_bbk_model.paper_R_valid ?Sig stock E K W A"
    and diagram_valid: "\<forall>A\<in>paper_R_positive_diagram ?Sig stock paper_R_naming_denote.
      paper_R_bbk_model.paper_R_valid ?Sig stock E K W A"
    and discriminator: "paper_R_bbk_model.paper_R_valid ?Sig stock E K W
      (named_paper_not (named_paper_iff stock ?P ?Q))"
    using Expanded.paper_R_positive_diagram_separating_bounded_model[
      OF infinite expanded_names parameter_h parameter_pe parameter_at pl ql pc qc names_different] by blast
  interpret Target: paper_R_bbk_model ?Sig stock E K W by (rule model)
  interpret Diagram: paper_R_diagram_target signature stock domain denote valuation E K W
  proof unfold_locales
    fix A
    assume member: "A \<in> paper_R_positive_diagram ?Sig stock paper_R_naming_denote"
    show "Target.paper_R_valid A" using diagram_valid member by blast
  qed
  let ?L = "paper_R_constant_pullback_denote Inl K"
  let ?h = "Diagram.paper_R_diagram_map"
  have reduct_model: "paper_R_bbk_model signature stock E ?L W" by (rule Diagram.paper_R_diagram_reduct_model)
  have reduct_valid: "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid signature stock E ?L W A"
    by (rule Diagram.paper_R_diagram_reduct_validates_theory[OF theory_h theory_valid])
  have hom: "paper_R_bbk_homomorphism signature stock domain denote E ?L ?h"
    by (rule Diagram.paper_R_diagram_reduct_homomorphism)
  have separated: "W (?h Prop p) \<noteq> W (?h Prop q)"
    by (rule Diagram.paper_R_diagram_discriminator_separates[OF pm qm discriminator])
  show ?thesis by (rule exI[where x=E], rule exI[where x="?L"], rule exI[where x=W], rule exI[where x="?h"],
    rule conjI[OF reduct_model], rule conjI[OF bounded], rule conjI[OF reduct_valid], rule conjI[OF hom separated])
qed

end

end
