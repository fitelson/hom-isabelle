theory Bacon_Source_Named_Decoder_Contexts
  imports Bacon_Source_Named_Decoder_Eta
begin

section \<open>Reflecting source contractions in compound contexts\<close>

text \<open>
  A contraction inside a typed application or abstraction decodes to a
  named βη conversion. In an application, uniqueness of the unchanged
  operand's type aligns the two function types. Under λσ, both decoders
  choose the same fresh name from the same input chart.
  Source: Bacon–Dorr Figure 2, pp.7–8, including contexts that bind free
  variables of the replaced occurrence. No outer-context freshness rule
  is added. All recursive language and chart guards are retained.
\<close>

lemma source_decoder_app_languages:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> (SApp F A) \<tau>"
  obtains \<sigma> where "sterm_in_language L \<Sigma> \<Gamma> F (Arr \<sigma> \<tau>)"
    and "sterm_in_language L \<Sigma> \<Gamma> A \<sigma>"
proof -
  have typed: "has_stype L \<Gamma> (SApp F A) \<tau>" and sig: "sterm_in_signature \<Sigma> (SApp F A)"
    using language unfolding sterm_in_language_def by blast+
  obtain \<sigma> where ft: "has_stype L \<Gamma> F (Arr \<sigma> \<tau>)" and at: "has_stype L \<Gamma> A \<sigma>"
    by (rule source_app_type_obtain[OF typed]; rule that; assumption)
  have fs: "sterm_in_signature \<Sigma> F" and asig: "sterm_in_signature \<Sigma> A" using sig by simp_all
  have fl: "sterm_in_language L \<Sigma> \<Gamma> F (Arr \<sigma> \<tau>)"
    unfolding sterm_in_language_def by (rule conjI[OF ft fs])
  have al: "sterm_in_language L \<Sigma> \<Gamma> A \<sigma>"
    unfolding sterm_in_language_def by (rule conjI[OF at asig])
  show thesis by (rule that[OF fl al])
qed

lemma source_decoder_lam_language:
  assumes language: "sterm_in_language L \<Sigma> \<Gamma> (SLam \<sigma> A) \<tau>"
  obtains \<rho> where "\<tau> = Arr \<sigma> \<rho>" and "sterm_in_language L \<Sigma> (\<sigma> # \<Gamma>) A \<rho>"
proof -
  have typed: "has_stype L \<Gamma> (SLam \<sigma> A) \<tau>" and sig: "sterm_in_signature \<Sigma> (SLam \<sigma> A)"
    using language unfolding sterm_in_language_def by blast+
  obtain \<rho> where ty: "\<tau> = Arr \<sigma> \<rho>" and at: "has_stype L (\<sigma> # \<Gamma>) A \<rho>"
    by (rule source_lam_type_obtain[OF typed]; rule that; assumption)
  have names: "sterm_in_signature \<Sigma> A" using sig by simp
  have al: "sterm_in_language L \<Sigma> (\<sigma> # \<Gamma>) A \<rho>"
    unfolding sterm_in_language_def by (rule conjI[OF at names])
  show thesis by (rule that[OF ty al])
qed

lemma source_decoder_language_unique:
  assumes first: "sterm_in_language L \<Sigma> \<Gamma> A \<sigma>"
    and second: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>"
  shows "\<sigma> = \<tau>"
proof -
  have a: "has_stype L \<Gamma> A \<sigma>" using first unfolding sterm_in_language_def by (rule conjunct1)
  have b: "has_stype L \<Gamma> A \<tau>" using second unfolding sterm_in_language_def by (rule conjunct1)
  show ?thesis by (rule source_typing_unique[OF a b])
qed

theorem source_to_named_compatible_conversion:
  assumes step: "scompatible_step R A B"
    and roots: "\<And>X Y \<Gamma> \<rho> ns. R X Y \<Longrightarrow>
      sterm_in_language L \<Sigma> \<Gamma> X \<rho> \<Longrightarrow> sterm_in_language L \<Sigma> \<Gamma> Y \<rho> \<Longrightarrow>
      named_chart G \<Gamma> ns \<Longrightarrow>
      named_beta_eta_in_language L \<Sigma> G \<rho> (source_to_named G ns X) (source_to_named G ns Y)"
    and left: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>"
    and right: "sterm_in_language L \<Sigma> \<Gamma> B \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> (source_to_named G ns A) (source_to_named G ns B)"
  using step left right chart
proof (induction arbitrary: \<Gamma> \<tau> ns rule: scompatible_step.induct)
  case (root M N)
  show ?case by (rule roots[where X=M and Y=N and \<Gamma>=\<Gamma> and \<rho>=\<tau> and ns=ns,
    OF root.hyps root.prems])
next
  case (App_left M M' N)
  obtain \<sigma> where ml: "sterm_in_language L \<Sigma> \<Gamma> M (Arr \<sigma> \<tau>)"
    and nl: "sterm_in_language L \<Sigma> \<Gamma> N \<sigma>"
    by (rule source_decoder_app_languages[OF App_left.prems(1)])
  obtain \<upsilon> where mr: "sterm_in_language L \<Sigma> \<Gamma> M' (Arr \<upsilon> \<tau>)"
    and nr: "sterm_in_language L \<Sigma> \<Gamma> N \<upsilon>"
    by (rule source_decoder_app_languages[OF App_left.prems(2)])
  have same: "\<upsilon> = \<sigma>" by (rule source_decoder_language_unique[OF nr nl])
  have mr_aligned: "sterm_in_language L \<Sigma> \<Gamma> M' (Arr \<sigma> \<tau>)" using mr by (simp only: same)
  have inner: "named_beta_eta_in_language L \<Sigma> G (Arr \<sigma> \<tau>)
    (source_to_named G ns M) (source_to_named G ns M')"
    by (rule App_left.IH[where \<Gamma>=\<Gamma> and \<tau>="Arr \<sigma> \<tau>" and ns=ns,
      OF ml mr_aligned App_left.prems(3)])
  have argument: "named_in_language L \<Sigma> G (source_to_named G ns N) \<sigma>"
    by (rule source_to_named_language[OF nl App_left.prems(3) rich])
  show ?case by (simp only: source_to_named.simps; rule named_conversion_App_left[OF inner argument])
next
  case (App_right N N' M)
  obtain \<sigma> where ml: "sterm_in_language L \<Sigma> \<Gamma> M (Arr \<sigma> \<tau>)"
    and nl: "sterm_in_language L \<Sigma> \<Gamma> N \<sigma>"
    by (rule source_decoder_app_languages[OF App_right.prems(1)])
  obtain \<upsilon> where mr: "sterm_in_language L \<Sigma> \<Gamma> M (Arr \<upsilon> \<tau>)"
    and nr: "sterm_in_language L \<Sigma> \<Gamma> N' \<upsilon>"
    by (rule source_decoder_app_languages[OF App_right.prems(2)])
  have arrows: "Arr \<upsilon> \<tau> = Arr \<sigma> \<tau>" by (rule source_decoder_language_unique[OF mr ml])
  have same: "\<upsilon> = \<sigma>" using arrows by simp
  have nr_aligned: "sterm_in_language L \<Sigma> \<Gamma> N' \<sigma>" using nr by (simp only: same)
  have inner: "named_beta_eta_in_language L \<Sigma> G \<sigma>
    (source_to_named G ns N) (source_to_named G ns N')"
    by (rule App_right.IH[where \<Gamma>=\<Gamma> and \<tau>=\<sigma> and ns=ns,
      OF nl nr_aligned App_right.prems(3)])
  have head: "named_in_language L \<Sigma> G (source_to_named G ns M) (Arr \<sigma> \<tau>)"
    by (rule source_to_named_language[OF ml App_right.prems(3) rich])
  show ?case by (simp only: source_to_named.simps; rule named_conversion_App_right[OF head inner])
next
  case (Lam_body M M' \<sigma>)
  obtain \<rho> where lt: "\<tau> = Arr \<sigma> \<rho>" and ml: "sterm_in_language L \<Sigma> (\<sigma> # \<Gamma>) M \<rho>"
    by (rule source_decoder_lam_language[OF Lam_body.prems(1)])
  obtain \<upsilon> where rt: "\<tau> = Arr \<sigma> \<upsilon>" and mr: "sterm_in_language L \<Sigma> (\<sigma> # \<Gamma>) M' \<upsilon>"
    by (rule source_decoder_lam_language[OF Lam_body.prems(2)])
  have same: "\<upsilon> = \<rho>" using lt rt by simp
  have mr_aligned: "sterm_in_language L \<Sigma> (\<sigma> # \<Gamma>) M' \<rho>" using mr by (simp only: same)
  let ?n = "named_chart_fresh G ns \<sigma>"
  have extended: "named_chart G (\<sigma> # \<Gamma>) (?n # ns)"
    by (rule named_chart_fresh_extend[OF Lam_body.prems(3) rich])
  have inner: "named_beta_eta_in_language L \<Sigma> G \<rho>
    (source_to_named G (?n # ns) M) (source_to_named G (?n # ns) M')"
    by (rule Lam_body.IH[where \<Gamma>="\<sigma> # \<Gamma>" and \<tau>=\<rho> and ns="?n # ns", OF ml mr_aligned extended])
  have abstraction: "named_beta_eta_in_language L \<Sigma> G (Arr (G ?n) \<rho>)
    (NLam ?n (source_to_named G (?n # ns) M)) (NLam ?n (source_to_named G (?n # ns) M'))"
    by (rule named_conversion_Lam[OF inner])
  show ?case using abstraction by (simp only: source_to_named.simps lt named_chart_fresh_type[OF rich])
qed

corollary source_to_named_beta_step_conversion:
  assumes step: "scompatible_step sbeta_contract A B"
    and left: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>" and right: "sterm_in_language L \<Sigma> \<Gamma> B \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> (source_to_named G ns A) (source_to_named G ns B)"
proof (rule source_to_named_compatible_conversion[OF step _ left right chart rich])
  fix X Y \<Gamma> \<rho> ns
  assume root: "sbeta_contract X Y" and xl: "sterm_in_language L \<Sigma> \<Gamma> X \<rho>"
    and yl: "sterm_in_language L \<Sigma> \<Gamma> Y \<rho>" and ch: "named_chart G \<Gamma> ns"
  show "named_beta_eta_in_language L \<Sigma> G \<rho> (source_to_named G ns X) (source_to_named G ns Y)"
    by (rule source_to_named_beta_root_conversion[OF root xl yl ch rich])
qed

corollary source_to_named_eta_step_conversion:
  assumes step: "scompatible_step seta_contract A B"
    and left: "sterm_in_language L \<Sigma> \<Gamma> A \<tau>" and right: "sterm_in_language L \<Sigma> \<Gamma> B \<tau>"
    and chart: "named_chart G \<Gamma> ns" and rich: "sg_rich G"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> (source_to_named G ns A) (source_to_named G ns B)"
proof (rule source_to_named_compatible_conversion[OF step _ left right chart rich])
  fix X Y \<Gamma> \<rho> ns
  assume root: "seta_contract X Y" and xl: "sterm_in_language L \<Sigma> \<Gamma> X \<rho>"
    and yl: "sterm_in_language L \<Sigma> \<Gamma> Y \<rho>" and ch: "named_chart G \<Gamma> ns"
  show "named_beta_eta_in_language L \<Sigma> G \<rho> (source_to_named G ns X) (source_to_named G ns Y)"
    by (rule source_to_named_eta_root_conversion[OF root xl yl ch rich])
qed

end
