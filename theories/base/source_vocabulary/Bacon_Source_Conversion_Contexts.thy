theory Bacon_Source_Conversion_Contexts
  imports Bacon_Source_Conversion
begin

section \<open>Source conversion is congruent under guarded application and abstraction\<close>

text \<open>
  If F ≡βη G and A:σ belongs to ℒ(Σ), then F A ≡βη G A.
  The argument position has the corresponding congruence, and a conversion
  A ≡βη B under x:σ lifts to λx:σ.A ≡βη λx:σ.B.
  Source: contextual β and η in Bacon–Dorr Figure 2, pp.7–8, with
  language-relative conversion as in Definition 3.1(ii.d).

  Isabelle representation.  The source relation fixes the logical-type
  function L and nonlogical signature Σ.  The generic context induction
  maps both endpoint typing and signature guards at each generating step;
  symmetry and transitivity retain the mapped intermediate terms.
  The fixed application operand must itself be in the source language.
  No target conversion, theoremhood reflection, or semantic assumption is
  used in these proofs.
\<close>

lemma sbeta_eta_context:
  assumes conversion: "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> \<tau> M N"
    and typing: "\<And>X. has_stype L \<Gamma> X \<tau> \<Longrightarrow> has_stype L \<Delta> (f X) \<rho>"
    and names: "\<And>X. sterm_in_signature \<Sigma> X \<Longrightarrow> sterm_in_signature \<Sigma> (f X)"
    and beta_context: "\<And>X Y. scompatible_step sbeta_contract X Y \<Longrightarrow>
      scompatible_step sbeta_contract (f X) (f Y)"
    and eta_context: "\<And>X Y. scompatible_step seta_contract X Y \<Longrightarrow>
      scompatible_step seta_contract (f X) (f Y)"
  shows "sbeta_eta_equiv_in_signature L \<Sigma> \<Delta> \<rho> (f M) (f N)"
  using conversion typing
proof (induction rule: sbeta_eta_equiv_in_signature.induct)
  case (Refl \<Gamma> M \<tau>)
  show ?case by (rule sbeta_eta_equiv_in_signature.Refl[
    OF Refl.prems[OF Refl.hyps(1)] names[OF Refl.hyps(2)]])
next
  case (Beta \<Gamma> M \<tau> N)
  have mt: "has_stype L \<Delta> (f M) \<rho>" by (rule Beta.prems[OF Beta.hyps(1)])
  have nt: "has_stype L \<Delta> (f N) \<rho>" by (rule Beta.prems[OF Beta.hyps(2)])
  have ms: "sterm_in_signature \<Sigma> (f M)" by (rule names[OF Beta.hyps(3)])
  have ns: "sterm_in_signature \<Sigma> (f N)" by (rule names[OF Beta.hyps(4)])
  have step: "scompatible_step sbeta_contract (f M) (f N)" by (rule beta_context[OF Beta.hyps(5)])
  show ?case by (rule sbeta_eta_equiv_in_signature.Beta[OF mt nt ms ns step])
next
  case (Eta \<Gamma> M \<tau> N)
  have mt: "has_stype L \<Delta> (f M) \<rho>" by (rule Eta.prems[OF Eta.hyps(1)])
  have nt: "has_stype L \<Delta> (f N) \<rho>" by (rule Eta.prems[OF Eta.hyps(2)])
  have ms: "sterm_in_signature \<Sigma> (f M)" by (rule names[OF Eta.hyps(3)])
  have ns: "sterm_in_signature \<Sigma> (f N)" by (rule names[OF Eta.hyps(4)])
  have step: "scompatible_step seta_contract (f M) (f N)" by (rule eta_context[OF Eta.hyps(5)])
  show ?case by (rule sbeta_eta_equiv_in_signature.Eta[OF mt nt ms ns step])
next
  case (Sym \<Gamma> \<tau> M N)
  show ?case by (rule sbeta_eta_equiv_in_signature.Sym[OF Sym.IH[OF Sym.prems]])
next
  case (Trans \<Gamma> \<tau> M N P)
  show ?case by (rule sbeta_eta_equiv_in_signature.Trans[
    OF Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed

lemma sbeta_eta_App_left:
  fixes F G A :: "('c, 'l) sterm"
  assumes conversion: "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> (Arr \<sigma> \<tau>) F G"
    and argument: "sterm_in_language L \<Sigma> \<Gamma> A \<sigma>"
  shows "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> \<tau> (SApp F A) (SApp G A)"
proof -
  have at: "has_stype L \<Gamma> A \<sigma>" using argument unfolding sterm_in_language_def by (rule conjunct1)
  have asig: "sterm_in_signature \<Sigma> A" using argument unfolding sterm_in_language_def by (rule conjunct2)
  show ?thesis
  proof (rule sbeta_eta_context[where f="\<lambda>X. SApp X A", OF conversion])
    fix X :: "('c, 'l) sterm"
    assume xt: "has_stype L \<Gamma> X (Arr \<sigma> \<tau>)"
    show "has_stype L \<Gamma> (SApp X A) \<tau>" by (rule has_stype.App[OF xt at])
  next
    fix X :: "('c, 'l) sterm"
    assume xs: "sterm_in_signature \<Sigma> X"
    show "sterm_in_signature \<Sigma> (SApp X A)" using xs asig by simp
  next
    show "\<And>X Y. scompatible_step sbeta_contract X Y \<Longrightarrow>
      scompatible_step sbeta_contract (SApp X A) (SApp Y A)" by (rule scompatible_step.App_left)
  next
    show "\<And>X Y. scompatible_step seta_contract X Y \<Longrightarrow>
      scompatible_step seta_contract (SApp X A) (SApp Y A)" by (rule scompatible_step.App_left)
  qed
qed

lemma sbeta_eta_App_right:
  fixes F A B :: "('c, 'l) sterm"
  assumes head: "sterm_in_language L \<Sigma> \<Gamma> F (Arr \<sigma> \<tau>)"
    and conversion: "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> \<sigma> A B"
  shows "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> \<tau> (SApp F A) (SApp F B)"
proof -
  have ft: "has_stype L \<Gamma> F (Arr \<sigma> \<tau>)" using head unfolding sterm_in_language_def by (rule conjunct1)
  have fs: "sterm_in_signature \<Sigma> F" using head unfolding sterm_in_language_def by (rule conjunct2)
  show ?thesis
  proof (rule sbeta_eta_context[where f="SApp F", OF conversion])
    fix X :: "('c, 'l) sterm"
    assume xt: "has_stype L \<Gamma> X \<sigma>"
    show "has_stype L \<Gamma> (SApp F X) \<tau>" by (rule has_stype.App[OF ft xt])
  next
    fix X :: "('c, 'l) sterm"
    assume xs: "sterm_in_signature \<Sigma> X"
    show "sterm_in_signature \<Sigma> (SApp F X)" using fs xs by simp
  next
    show "\<And>X Y. scompatible_step sbeta_contract X Y \<Longrightarrow>
      scompatible_step sbeta_contract (SApp F X) (SApp F Y)" by (rule scompatible_step.App_right)
  next
    show "\<And>X Y. scompatible_step seta_contract X Y \<Longrightarrow>
      scompatible_step seta_contract (SApp F X) (SApp F Y)" by (rule scompatible_step.App_right)
  qed
qed

lemma sbeta_eta_App:
  assumes fun_conv: "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> (Arr \<sigma> \<tau>) F G"
    and arg_conv: "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> \<sigma> A B"
  shows "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> \<tau> (SApp F A) (SApp G B)"
proof -
  have al: "sterm_in_language L \<Sigma> \<Gamma> A \<sigma>"
    by (rule conjunct1[OF sbeta_eta_equiv_in_signature_language[OF arg_conv]])
  have gl: "sterm_in_language L \<Sigma> \<Gamma> G (Arr \<sigma> \<tau>)"
    by (rule conjunct2[OF sbeta_eta_equiv_in_signature_language[OF fun_conv]])
  have left: "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> \<tau> (SApp F A) (SApp G A)"
    by (rule sbeta_eta_App_left[OF fun_conv al])
  have right: "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> \<tau> (SApp G A) (SApp G B)"
    by (rule sbeta_eta_App_right[OF gl arg_conv])
  show ?thesis by (rule sbeta_eta_equiv_in_signature.Trans[OF left right])
qed

lemma sbeta_eta_Lam:
  assumes conversion: "sbeta_eta_equiv_in_signature L \<Sigma> (\<sigma> # \<Gamma>) \<tau> A B"
  shows "sbeta_eta_equiv_in_signature L \<Sigma> \<Gamma> (Arr \<sigma> \<tau>) (SLam \<sigma> A) (SLam \<sigma> B)"
proof (rule sbeta_eta_context[where f="SLam \<sigma>", OF conversion])
  fix X
  assume xt: "has_stype L (\<sigma> # \<Gamma>) X \<tau>"
  show "has_stype L \<Gamma> (SLam \<sigma> X) (Arr \<sigma> \<tau>)" by (rule has_stype.Lam[OF xt])
next
  fix X
  assume xs: "sterm_in_signature \<Sigma> X"
  show "sterm_in_signature \<Sigma> (SLam \<sigma> X)" using xs by simp
next
  show "\<And>X Y. scompatible_step sbeta_contract X Y \<Longrightarrow>
    scompatible_step sbeta_contract (SLam \<sigma> X) (SLam \<sigma> Y)" by (rule scompatible_step.Lam_body)
next
  show "\<And>X Y. scompatible_step seta_contract X Y \<Longrightarrow>
    scompatible_step seta_contract (SLam \<sigma> X) (SLam \<sigma> Y)" by (rule scompatible_step.Lam_body)
qed

end
