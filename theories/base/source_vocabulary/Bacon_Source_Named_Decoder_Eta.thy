theory Bacon_Source_Named_Decoder_Eta
  imports Bacon_Source_Named_Decoder_Beta
begin

section \<open>A source η root decodes to literal named βη conversion\<close>

text \<open>
  Decoding a shifted F under a chart extended by n gives an α-variant
  of decoding F under the original chart. The free names of the latter
  lie in that original chart, so the fresh n is absent from both heads.
  Literal η removes λn.(F′n), and the derived α→βη theorem aligns F′
  with the decoded source reduct. Source: Bacon–Dorr Figure 2, p.8.

  Isabelle representation. The shift/index equation is proved first with
  both finite charts explicit. No equality of raw decoder outputs is
  assumed: their internal choices of bound names may differ. Both source
  endpoints are typed and belong to the declared language. There is no
  new α rule, H inference, or semantic assumption.
\<close>

lemma source_to_named_shift_encoding:
  assumes typed: "has_stype L \<Gamma> F \<tau>"
    and chart: "named_chart G \<Gamma> ns"
    and extended: "named_chart G (\<sigma> # \<Gamma>) (n # ns)"
    and rich: "sg_rich G"
  shows "named_to_source G [] (source_to_named G (n # ns) (sshift F)) =
    named_to_source G [] (source_to_named G ns F)"
proof -
  have shifted_type: "has_stype L (\<sigma> # \<Gamma>) (sshift F) \<tau>"
    by (rule sshift_preserves_typing[OF typed])
  have shifted: "named_to_source G [] (source_to_named G (n # ns) (sshift F)) =
    srename (\<lambda>i. (n # ns) ! i) (sshift F)"
    by (rule source_to_named_empty_encoding[OF shifted_type extended rich])
  have original: "named_to_source G [] (source_to_named G ns F) = srename (\<lambda>i. ns ! i) F"
    by (rule source_to_named_empty_encoding[OF typed chart rich])
  have maps: "(\<lambda>i. (n # ns) ! i) \<circ> Suc = (\<lambda>i. ns ! i)"
    by (rule ext) (simp add: comp_def)
  have shift_cancel: "srename (\<lambda>i. (n # ns) ! i) (sshift F) = srename (\<lambda>i. ns ! i) F"
    by (simp only: sshift_def srename_comp maps)
  show ?thesis by (rule trans[OF shifted trans[OF shift_cancel sym[OF original]]])
qed

lemma source_to_named_shift_alpha:
  assumes typed: "has_stype L \<Gamma> F \<tau>"
    and chart: "named_chart G \<Gamma> ns"
    and extended: "named_chart G (\<sigma> # \<Gamma>) (n # ns)"
    and rich: "sg_rich G"
  shows "named_alpha G (source_to_named G (n # ns) (sshift F)) (source_to_named G ns F)"
  by (rule named_encoding_implies_alpha[OF rich source_to_named_shift_encoding[OF typed chart extended rich]])

theorem source_to_named_eta_root_conversion:
  assumes root: "seta_contract X Y"
    and left: "sterm_in_language L \<Sigma> \<Gamma> X \<tau>"
    and right: "sterm_in_language L \<Sigma> \<Gamma> Y \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> (source_to_named G ns X) (source_to_named G ns Y)"
proof -
  obtain \<sigma> F where redex: "X = SLam \<sigma> (SApp (sshift F) (SVar 0))" and reduct: "Y = F"
    using root by (cases rule: seta_contract.cases) blast
  have f_language: "sterm_in_language L \<Sigma> \<Gamma> F \<tau>" using right by (simp only: reduct)
  have f_type: "has_stype L \<Gamma> F \<tau>" and f_sig: "sterm_in_signature \<Sigma> F"
    using f_language unfolding sterm_in_language_def by blast+
  let ?n = "named_chart_fresh G ns \<sigma>"
  let ?F = "source_to_named G (?n # ns) (sshift F)"
  let ?D = "source_to_named G ns F"
  have extended: "named_chart G (\<sigma> # \<Gamma>) (?n # ns)"
    by (rule named_chart_fresh_extend[OF chart rich])
  have alpha: "named_alpha G ?F ?D"
    by (rule source_to_named_shift_alpha[OF f_type chart extended rich])
  have support: "named_fv ?D \<subseteq> set ns"
    by (rule source_to_named_fv_bound[OF f_type chart rich])
  have fresh_chart: "?n \<notin> set ns" by (rule named_chart_fresh_notin[OF rich])
  have fresh_decoded: "?n \<notin> named_fv ?D" using support fresh_chart by blast
  have fv_equal: "named_fv ?F = named_fv ?D" by (rule named_alpha_fv[OF alpha])
  have fresh_head: "?n \<notin> named_fv ?F" by (simp only: fv_equal; rule fresh_decoded)
  have raw_eta: "named_eta_contract (NLam ?n (NApp ?F (NVar ?n))) ?F"
    by (rule named_eta_contract.eta[OF fresh_head])
  have named_root: "named_eta_contract (source_to_named G ns X) ?F"
    using raw_eta by (simp add: redex)
  have named_step: "named_compatible_step named_eta_contract (source_to_named G ns X) ?F"
    by (rule named_compatible_step.root[where R=named_eta_contract
      and M="source_to_named G ns X" and N="?F", OF named_root])
  have shifted_type: "has_stype L (\<sigma> # \<Gamma>) (sshift F) \<tau>"
    by (rule sshift_preserves_typing[OF f_type])
  have shifted_sig: "sterm_in_signature \<Sigma> (sshift F)"
    by (simp only: sshift_def srename_signature; rule f_sig)
  have shifted_language: "sterm_in_language L \<Sigma> (\<sigma> # \<Gamma>) (sshift F) \<tau>"
    unfolding sterm_in_language_def by (rule conjI[OF shifted_type shifted_sig])
  have head_language: "named_in_language L \<Sigma> G ?F \<tau>"
    by (rule source_to_named_language[OF shifted_language extended rich])
  have left_language: "named_in_language L \<Sigma> G (source_to_named G ns X) \<tau>"
    by (rule source_to_named_language[OF left chart rich])
  have eta: "named_beta_eta_in_language L \<Sigma> G \<tau> (source_to_named G ns X) ?F"
    by (rule named_beta_eta_in_language.Eta[OF left_language head_language named_step])
  have alignment: "named_beta_eta_in_language L \<Sigma> G \<tau> ?F ?D"
    by (rule named_alpha_implies_beta_eta[OF alpha head_language])
  have result: "named_beta_eta_in_language L \<Sigma> G \<tau> (source_to_named G ns X) ?D"
    by (rule named_beta_eta_in_language.Trans[OF eta alignment])
  show ?thesis using result by (simp only: reduct)
qed

end
