theory Bacon_Source_Named_Conversion_Contexts
  imports Bacon_Source_Named_Conversion
begin

section \<open>Named βη conversion under application and λ\<close>

text \<open>
  From A ≡βη B we obtain λn.A ≡βη λn.B. From F ≡βη H
  and a fixed argument P:σ, we obtain FP ≡βη HP; the corresponding
  argument-position rule fixes a head of type σ → τ.
  Source: the contextual β and η patterns of Bacon–Dorr Figure 2,
  p.8, and the language-relative clause of Definition 3.1(ii.d), p.44.

  Isabelle representation. Each context maps every language guard in the
  conversion proof, including the intermediate term of a transitivity
  step. The named stock G is unchanged under a binder: n has its fixed
  type G n. No α step, H theoremhood, or model assumption is introduced.
\<close>

lemma named_language_Lam:
  assumes body: "named_in_language L \<Sigma> G A \<tau>"
  shows "named_in_language L \<Sigma> G (NLam n A) (Arr (G n) \<tau>)"
proof -
  have typed: "has_ntype L G A \<tau>"
    using body unfolding named_in_language_def by (rule conjunct1)
  have sig: "named_in_signature \<Sigma> A"
    using body unfolding named_in_language_def by (rule conjunct2)
  have abstraction: "has_ntype L G (NLam n A) (Arr (G n) \<tau>)"
    by (rule has_ntype.Lam[OF typed])
  have names: "named_in_signature \<Sigma> (NLam n A)"
    by (simp only: named_in_signature.simps; rule sig)
  show ?thesis unfolding named_in_language_def by (rule conjI[OF abstraction names])
qed

lemma named_language_App:
  assumes head: "named_in_language L \<Sigma> G F (Arr \<sigma> \<tau>)"
    and argument: "named_in_language L \<Sigma> G A \<sigma>"
  shows "named_in_language L \<Sigma> G (NApp F A) \<tau>"
proof -
  have ft: "has_ntype L G F (Arr \<sigma> \<tau>)"
    using head unfolding named_in_language_def by (rule conjunct1)
  have at: "has_ntype L G A \<sigma>"
    using argument unfolding named_in_language_def by (rule conjunct1)
  have fs: "named_in_signature \<Sigma> F"
    using head unfolding named_in_language_def by (rule conjunct2)
  have asig: "named_in_signature \<Sigma> A"
    using argument unfolding named_in_language_def by (rule conjunct2)
  have application: "has_ntype L G (NApp F A) \<tau>"
    by (rule has_ntype.App[OF ft at])
  have names: "named_in_signature \<Sigma> (NApp F A)"
    by (simp only: named_in_signature.simps; rule conjI[OF fs asig])
  show ?thesis unfolding named_in_language_def by (rule conjI[OF application names])
qed

lemma named_conversion_context:
  fixes f :: "('c, 'l) named_term \<Rightarrow> ('c, 'l) named_term"
  assumes conversion: "named_beta_eta_in_language L \<Sigma> G \<tau> A B"
    and language_map: "\<And>X. named_in_language L \<Sigma> G X \<tau> \<Longrightarrow>
      named_in_language L \<Sigma> G (f X) \<rho>"
    and beta_context: "\<And>X Y. named_compatible_step named_beta_contract X Y \<Longrightarrow>
      named_compatible_step named_beta_contract (f X) (f Y)"
    and eta_context: "\<And>X Y. named_compatible_step named_eta_contract X Y \<Longrightarrow>
      named_compatible_step named_eta_contract (f X) (f Y)"
  shows "named_beta_eta_in_language L \<Sigma> G \<rho> (f A) (f B)"
  using conversion language_map
proof (induction rule: named_beta_eta_in_language.induct)
  case (Refl A \<tau>)
  show ?case by (rule named_beta_eta_in_language.Refl[OF Refl.prems[OF Refl.hyps]])
next
  case (Beta A \<tau> B)
  have left: "named_in_language L \<Sigma> G (f A) \<rho>" by (rule Beta.prems[OF Beta.hyps(1)])
  have right: "named_in_language L \<Sigma> G (f B) \<rho>" by (rule Beta.prems[OF Beta.hyps(2)])
  have step: "named_compatible_step named_beta_contract (f A) (f B)"
    by (rule beta_context[where X=A and Y=B, OF Beta.hyps(3)])
  show ?case by (rule named_beta_eta_in_language.Beta[OF left right step])
next
  case (Eta A \<tau> B)
  have left: "named_in_language L \<Sigma> G (f A) \<rho>" by (rule Eta.prems[OF Eta.hyps(1)])
  have right: "named_in_language L \<Sigma> G (f B) \<rho>" by (rule Eta.prems[OF Eta.hyps(2)])
  have step: "named_compatible_step named_eta_contract (f A) (f B)"
    by (rule eta_context[where X=A and Y=B, OF Eta.hyps(3)])
  show ?case by (rule named_beta_eta_in_language.Eta[OF left right step])
next
  case (Sym \<tau> A B)
  show ?case by (rule named_beta_eta_in_language.Sym[OF Sym.IH[OF Sym.prems]])
next
  case (Trans \<tau> A B C)
  show ?case by (rule named_beta_eta_in_language.Trans[
    OF Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed

lemma named_conversion_Lam:
  assumes conversion: "named_beta_eta_in_language L \<Sigma> G \<tau> A B"
  shows "named_beta_eta_in_language L \<Sigma> G (Arr (G n) \<tau>) (NLam n A) (NLam n B)"
proof (rule named_conversion_context[where f="NLam n", OF conversion])
  show "\<And>X. named_in_language L \<Sigma> G X \<tau> \<Longrightarrow>
    named_in_language L \<Sigma> G (NLam n X) (Arr (G n) \<tau>)"
    by (rule named_language_Lam)
next
  show "\<And>X Y. named_compatible_step named_beta_contract X Y \<Longrightarrow>
    named_compatible_step named_beta_contract (NLam n X) (NLam n Y)"
    by (rule named_compatible_step.Lam_body)
next
  show "\<And>X Y. named_compatible_step named_eta_contract X Y \<Longrightarrow>
    named_compatible_step named_eta_contract (NLam n X) (NLam n Y)"
    by (rule named_compatible_step.Lam_body)
qed

lemma named_conversion_App_left:
  assumes conversion: "named_beta_eta_in_language L \<Sigma> G (Arr \<sigma> \<tau>) F H"
    and argument: "named_in_language L \<Sigma> G A \<sigma>"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> (NApp F A) (NApp H A)"
proof (rule named_conversion_context[where f="\<lambda>X. NApp X A", OF conversion])
  fix X
  assume head: "named_in_language L \<Sigma> G X (Arr \<sigma> \<tau>)"
  show "named_in_language L \<Sigma> G (NApp X A) \<tau>" by (rule named_language_App[OF head argument])
next
  show "\<And>X Y. named_compatible_step named_beta_contract X Y \<Longrightarrow>
    named_compatible_step named_beta_contract (NApp X A) (NApp Y A)"
    by (rule named_compatible_step.App_left)
next
  show "\<And>X Y. named_compatible_step named_eta_contract X Y \<Longrightarrow>
    named_compatible_step named_eta_contract (NApp X A) (NApp Y A)"
    by (rule named_compatible_step.App_left)
qed

lemma named_conversion_App_right:
  assumes head: "named_in_language L \<Sigma> G F (Arr \<sigma> \<tau>)"
    and conversion: "named_beta_eta_in_language L \<Sigma> G \<sigma> A B"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> (NApp F A) (NApp F B)"
proof (rule named_conversion_context[where f="NApp F", OF conversion])
  fix X
  assume argument: "named_in_language L \<Sigma> G X \<sigma>"
  show "named_in_language L \<Sigma> G (NApp F X) \<tau>" by (rule named_language_App[OF head argument])
next
  show "\<And>X Y. named_compatible_step named_beta_contract X Y \<Longrightarrow>
    named_compatible_step named_beta_contract (NApp F X) (NApp F Y)"
    by (rule named_compatible_step.App_right)
next
  show "\<And>X Y. named_compatible_step named_eta_contract X Y \<Longrightarrow>
    named_compatible_step named_eta_contract (NApp F X) (NApp F Y)"
    by (rule named_compatible_step.App_right)
qed

lemma named_conversion_App:
  assumes head: "named_beta_eta_in_language L \<Sigma> G (Arr \<sigma> \<tau>) F H"
    and argument: "named_beta_eta_in_language L \<Sigma> G \<sigma> A B"
  shows "named_beta_eta_in_language L \<Sigma> G \<tau> (NApp F A) (NApp H B)"
proof -
  have al: "named_in_language L \<Sigma> G A \<sigma>"
    by (rule conjunct1[OF named_beta_eta_languages[OF argument]])
  have hl: "named_in_language L \<Sigma> G H (Arr \<sigma> \<tau>)"
    by (rule conjunct2[OF named_beta_eta_languages[OF head]])
  have left: "named_beta_eta_in_language L \<Sigma> G \<tau> (NApp F A) (NApp H A)"
    by (rule named_conversion_App_left[OF head al])
  have right: "named_beta_eta_in_language L \<Sigma> G \<tau> (NApp H A) (NApp H B)"
    by (rule named_conversion_App_right[OF hl argument])
  show ?thesis by (rule named_beta_eta_in_language.Trans[OF left right])
qed

end
