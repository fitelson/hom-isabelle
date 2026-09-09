theory Bacon_Source_Relational_Bounded_Theory_Countermodel
  imports Bacon_Source_Relational_Bounded_Theory_Models
    Bacon_Source_Relational_H_Theory_Closed_Extension_Bounded
    Bacon_Source_Relational_Universal_Closure_Language
    Bacon_Source_Relational_Universal_Closure_Validity_Converse
begin

section \<open>Every missing formula fails in an actual bounded T-model\<close>

theorem paper_R_bounded_theory_countermodel:
  assumes infinite: "infinite U" and names: "card_of (\<Union>\<sigma>. \<Sigma> \<sigma>) \<le>o card_of U"
    and rich: "paper_R_rich G" and theory_h: "paper_R_H_theory \<Sigma> G T"
    and language: "paper_R_in_language \<Sigma> G P Prop" and absent: "P \<notin> T"
  shows "\<exists>M\<in>paper_R_bounded_theory_models \<Sigma> G U T.
    \<not> paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain M) (paper_bbk_denote M) (paper_bbk_valuation M) P"
proof -
  obtain ns where distinct: "distinct ns" and covers: "set ns = named_fv P"
    and binders: "list_all paper_R_type (map G ns)"
    and cl: "paper_R_in_language \<Sigma> G (paper_R_all_vec G ns P) Prop"
    and cc: "named_fv (paper_R_all_vec G ns P) = {}"
    by (rule paper_R_language_closed_universal[OF language])
  let ?C = "paper_R_all_vec G ns P"
  let ?N = "named_paper_not ?C"
  have instance_H: "paper_R_named_H \<Sigma> G (named_paper_imp G ?C P)"
    by (rule paper_R_named_H_all_vec_instance[OF rich language binders])
  have instance_member: "named_paper_imp G ?C P \<in> T"
    by (rule paper_R_H_theory_H[OF theory_h instance_H])
  have not_derived: "\<not> paper_R_named_derivable \<Sigma> G T ?C"
  proof
    assume derived: "paper_R_named_derivable \<Sigma> G T ?C"
    have member: "?C \<in> T"
      by (rule paper_R_H_theory_local_consequences[OF theory_h derived subset_refl])
    have result: "P \<in> T" by (rule paper_R_H_theory_MP[OF theory_h member instance_member language])
    show False using absent result by contradiction
  qed
  have consistent: "paper_R_named_consistent \<Sigma> G (T \<union> {?N})"
    using paper_R_named_consistent_insert_not[OF rich cl not_derived] by (simp add: insert_commute)
  have nl: "paper_R_in_language \<Sigma> G ?N Prop" by (rule paper_R_named_not_language[OF cl])
  have nc: "named_fv ?N = {}" by (simp only: named_paper_primitive_fv cc)
  have additions: "paper_R_closed_theory \<Sigma> G {?N}"
    by (simp only: paper_R_closed_theory_insert paper_R_closed_theory_empty;
      rule conjI[OF paper_R_sentenceI[OF nl nc]]; rule TrueI)
  obtain D J V where model: "paper_R_bbk_model \<Sigma> G D J V"
    and bound: "(\<Union>\<sigma>. D \<sigma>) \<subseteq> U"
    and valid: "\<forall>A\<in>T \<union> {?N}. paper_R_bbk_model.paper_R_valid \<Sigma> G D J V A"
    using paper_R_H_theory_closed_extension_bounded_model[
      OF infinite names rich theory_h additions consistent] by blast
  interpret Model: paper_R_bbk_model \<Sigma> G D J V by (rule model)
  let ?M = "\<lparr>paper_bbk_domain=D, paper_bbk_denote=J, paper_bbk_valuation=V\<rparr>"
  let ?Normalized = "paper_R_bbk_normalize \<Sigma> G ?M"
  have record_valid: "paper_R_bbk_data_valid \<Sigma> G ?M" using model
    by (simp add: paper_R_bbk_data_valid_def)
  have record_bound: "(\<Union>\<sigma>. paper_bbk_domain ?M \<sigma>) \<subseteq> U" using bound by simp
  have record_truth: "\<forall>A\<in>T. paper_R_bbk_model.paper_R_valid \<Sigma> G
    (paper_bbk_domain ?M) (paper_bbk_denote ?M) (paper_bbk_valuation ?M) A"
    using valid by auto
  have object: "?Normalized \<in> paper_R_bounded_theory_models \<Sigma> G U T"
    by (rule paper_R_bounded_theory_models_normalize[OF record_valid record_bound record_truth])
  have fails: "\<not> paper_R_bbk_model.paper_R_valid \<Sigma> G
    (paper_bbk_domain ?Normalized) (paper_bbk_denote ?Normalized) (paper_bbk_valuation ?Normalized) P"
  proof
    assume normalized: "paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain ?Normalized) (paper_bbk_denote ?Normalized) (paper_bbk_valuation ?Normalized) P"
    have original: "paper_R_bbk_model.paper_R_valid \<Sigma> G
      (paper_bbk_domain ?M) (paper_bbk_denote ?M) (paper_bbk_valuation ?M) P"
      by (rule iffD1[OF paper_R_bbk_normalize_formula_valid_iff[OF record_valid] normalized])
    have pv: "Model.paper_R_valid P" using original by simp
    have cv: "Model.paper_R_valid ?C" by (rule Model.paper_R_valid_all_vec[OF language binders pv])
    have nv: "Model.paper_R_valid ?N" using valid by blast
    have typed: "named_env_typed D G Map.empty" by (simp add: named_env_typed_def)
    have ca: "named_adequate Map.empty ?C" and na: "named_adequate Map.empty ?N"
      by (simp_all add: named_adequate_def cc nc)
    have true_C: "V (J Map.empty ?C)" by (rule Model.paper_R_validE[OF cv typed ca])
    have true_N: "V (J Map.empty ?N)" by (rule Model.paper_R_validE[OF nv typed na])
    have false_C: "\<not> V (J Map.empty ?C)"
      by (rule iffD1[OF Model.paper_R_named_not_truth[OF cl typed ca] true_N])
    show False using true_C false_C by contradiction
  qed
  show ?thesis by (rule bexI[where x="?Normalized"]; (rule fails | rule object))
qed

text \<open>
  P may be open. Add only the CLOSED sentence ¬∀n⃗.P, never
  ¬P as a globally true open assumption. If P were valid in the
  constructed model, its universal closure would be valid too,
  contradicting this added sentence. Normalization then puts the
  countermodel in the exact bounded object set.

  No PE, C, quasi-Fregeanness or consistency premise is needed:
  nonmembership in the H-theory already supplies the consistent
  negative extension. Source: Theorem 3.2 and the common-theory
  step needed in Theorem 3.12, pp.44–45 and 51–52.
\<close>

end
