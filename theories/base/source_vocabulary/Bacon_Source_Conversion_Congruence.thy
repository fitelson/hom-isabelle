theory Bacon_Source_Conversion_Congruence
  imports Bacon_Source_Propositional_Bridge
begin

section \<open>Conversion inside a typed context in the declared language\<close>

text \<open>
  A ≡βη B permits replacement inside Φ[−], including beneath λ
  (Bacon–Dorr Figure 2, pp. 7–8).  All terms of the conversion chain remain
  in ℒ(Σ), as required by Definition 3.1(ii.d).

  Isabelle representation: source_conversion_map transports the indexed
  relation through a context C that preserves typing, signature membership,
  and immediate β and η steps.  The following instances supply those
  premises for Neg, Conj, Disj, App, and Lam.

  Status: congruence of syntactic conversion, not replacement of merely
  materially equivalent propositions inside arbitrary intensional contexts.
\<close>

lemma source_conversion_map:
  assumes step: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M N"
    and types: "\<And>A. has_ptype \<Gamma> A \<tau> \<Longrightarrow> has_ptype \<Delta> (C A) \<rho>"
    and names: "\<And>A. pterm_in_signature \<Sigma> A \<Longrightarrow> pterm_in_signature \<Sigma> (C A)"
    and betas: "\<And>A B. pcompatible_step pbeta_contract A B \<Longrightarrow>
      pcompatible_step pbeta_contract (C A) (C B)"
    and etas: "\<And>A B. pcompatible_step peta_contract A B \<Longrightarrow>
      pcompatible_step peta_contract (C A) (C B)"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Delta> \<rho> (C M) (C N)"
  using step types names betas etas
proof (induction rule: pbeta_eta_equiv_in_signature.induct)
  case Refl
  show ?case by (rule pbeta_eta_equiv_in_signature.Refl[
    OF Refl.prems(1)[OF Refl.hyps(1)] Refl.prems(2)[OF Refl.hyps(2)]])
next
  case Beta
  show ?case by (rule pbeta_eta_equiv_in_signature.Beta[
    OF Beta.prems(1)[OF Beta.hyps(1)] Beta.prems(1)[OF Beta.hyps(2)]
    Beta.prems(2)[OF Beta.hyps(3)] Beta.prems(2)[OF Beta.hyps(4)]
    Beta.prems(3)[OF Beta.hyps(5)]])
next
  case Eta
  show ?case by (rule pbeta_eta_equiv_in_signature.Eta[
    OF Eta.prems(1)[OF Eta.hyps(1)] Eta.prems(1)[OF Eta.hyps(2)]
    Eta.prems(2)[OF Eta.hyps(3)] Eta.prems(2)[OF Eta.hyps(4)]
    Eta.prems(4)[OF Eta.hyps(5)]])
next
  case Sym
  show ?case by (rule pbeta_eta_equiv_in_signature.Sym[OF Sym.IH[OF Sym.prems]])
next
  case Trans
  show ?case by (rule pbeta_eta_equiv_in_signature.Trans[
    OF Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed

lemma source_conversion_left_language:
  assumes "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M N"
  shows "pterm_in_language \<Sigma> \<Gamma> M \<tau>"
  using pbeta_eta_equiv_in_signature_data[OF assms]
  unfolding pterm_in_language_def by blast

lemma source_conversion_right_language:
  assumes "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M N"
  shows "pterm_in_language \<Sigma> \<Gamma> N \<tau>"
  using pbeta_eta_equiv_in_signature_data[OF assms]
  unfolding pterm_in_language_def by blast

lemma source_conversion_Neg:
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop M N"

  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (PNeg M) (PNeg N)"
proof (rule source_conversion_map[where C=PNeg, OF conv])
  show "\<And>X. has_ptype \<Gamma> X Prop \<Longrightarrow> has_ptype \<Gamma> (PNeg X) Prop"
    by (erule has_ptype.PNeg)
  show "\<And>X. pterm_in_signature \<Sigma> X \<Longrightarrow> pterm_in_signature \<Sigma> (PNeg X)"
    by simp
  show "\<And>X Y. pcompatible_step pbeta_contract X Y \<Longrightarrow>
    pcompatible_step pbeta_contract (PNeg X) (PNeg Y)"
    by (erule pcompatible_step.Neg_body)
  show "\<And>X Y. pcompatible_step peta_contract X Y \<Longrightarrow>
    pcompatible_step peta_contract (PNeg X) (PNeg Y)"
    by (erule pcompatible_step.Neg_body)
qed

lemma source_conversion_Conj_left:
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop M N"
    and arg: "pterm_in_language \<Sigma> \<Gamma> B Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (PConj M B) (PConj N B)"
proof (rule source_conversion_map[where C="\<lambda>X. PConj X B", OF conv])
  show "\<And>X. has_ptype \<Gamma> X Prop \<Longrightarrow> has_ptype \<Gamma> (PConj X B) Prop"
    using arg unfolding pterm_in_language_def by (auto intro: has_ptype.PConj)
  show "\<And>X. pterm_in_signature \<Sigma> X \<Longrightarrow> pterm_in_signature \<Sigma> (PConj X B)"
    using arg unfolding pterm_in_language_def by simp
  show "\<And>X Y. pcompatible_step pbeta_contract X Y \<Longrightarrow>
    pcompatible_step pbeta_contract (PConj X B) (PConj Y B)"
    by (erule pcompatible_step.Conj_left)
  show "\<And>X Y. pcompatible_step peta_contract X Y \<Longrightarrow>
    pcompatible_step peta_contract (PConj X B) (PConj Y B)"
    by (erule pcompatible_step.Conj_left)
qed

lemma source_conversion_Conj_right:
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop M N"
    and arg: "pterm_in_language \<Sigma> \<Gamma> A Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (PConj A M) (PConj A N)"
proof (rule source_conversion_map[where C="PConj A", OF conv])
  show "\<And>X. has_ptype \<Gamma> X Prop \<Longrightarrow> has_ptype \<Gamma> (PConj A X) Prop"
    using arg unfolding pterm_in_language_def by (auto intro: has_ptype.PConj)
  show "\<And>X. pterm_in_signature \<Sigma> X \<Longrightarrow> pterm_in_signature \<Sigma> (PConj A X)"
    using arg unfolding pterm_in_language_def by simp
  show "\<And>X Y. pcompatible_step pbeta_contract X Y \<Longrightarrow>
    pcompatible_step pbeta_contract (PConj A X) (PConj A Y)"
    by (erule pcompatible_step.Conj_right)
  show "\<And>X Y. pcompatible_step peta_contract X Y \<Longrightarrow>
    pcompatible_step peta_contract (PConj A X) (PConj A Y)"
    by (erule pcompatible_step.Conj_right)
qed

lemma source_conversion_Disj_left:
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop M N"
    and arg: "pterm_in_language \<Sigma> \<Gamma> B Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (PDisj M B) (PDisj N B)"
proof (rule source_conversion_map[where C="\<lambda>X. PDisj X B", OF conv])
  show "\<And>X. has_ptype \<Gamma> X Prop \<Longrightarrow> has_ptype \<Gamma> (PDisj X B) Prop"
    using arg unfolding pterm_in_language_def by (auto intro: has_ptype.PDisj)
  show "\<And>X. pterm_in_signature \<Sigma> X \<Longrightarrow> pterm_in_signature \<Sigma> (PDisj X B)"
    using arg unfolding pterm_in_language_def by simp
  show "\<And>X Y. pcompatible_step pbeta_contract X Y \<Longrightarrow>
    pcompatible_step pbeta_contract (PDisj X B) (PDisj Y B)"
    by (erule pcompatible_step.Disj_left)
  show "\<And>X Y. pcompatible_step peta_contract X Y \<Longrightarrow>
    pcompatible_step peta_contract (PDisj X B) (PDisj Y B)"
    by (erule pcompatible_step.Disj_left)
qed

lemma source_conversion_Disj_right:
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop M N"
    and arg: "pterm_in_language \<Sigma> \<Gamma> A Prop"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (PDisj A M) (PDisj A N)"
proof (rule source_conversion_map[where C="PDisj A", OF conv])
  show "\<And>X. has_ptype \<Gamma> X Prop \<Longrightarrow> has_ptype \<Gamma> (PDisj A X) Prop"
    using arg unfolding pterm_in_language_def by (auto intro: has_ptype.PDisj)
  show "\<And>X. pterm_in_signature \<Sigma> X \<Longrightarrow> pterm_in_signature \<Sigma> (PDisj A X)"
    using arg unfolding pterm_in_language_def by simp
  show "\<And>X Y. pcompatible_step pbeta_contract X Y \<Longrightarrow>
    pcompatible_step pbeta_contract (PDisj A X) (PDisj A Y)"
    by (erule pcompatible_step.Disj_right)
  show "\<And>X Y. pcompatible_step peta_contract X Y \<Longrightarrow>
    pcompatible_step peta_contract (PDisj A X) (PDisj A Y)"
    by (erule pcompatible_step.Disj_right)
qed

lemma source_conversion_App_left:
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> (Arr \<sigma> \<tau>) M N"
    and arg: "pterm_in_language \<Sigma> \<Gamma> B \<sigma>"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> (PApp M B) (PApp N B)"
proof (rule source_conversion_map[where C="\<lambda>X. PApp X B", OF conv])
  show "\<And>X. has_ptype \<Gamma> X (Arr \<sigma> \<tau>) \<Longrightarrow> has_ptype \<Gamma> (PApp X B) \<tau>"
    using arg unfolding pterm_in_language_def by (auto intro: has_ptype.PApp)
  show "\<And>X. pterm_in_signature \<Sigma> X \<Longrightarrow> pterm_in_signature \<Sigma> (PApp X B)"
    using arg unfolding pterm_in_language_def by simp
  show "\<And>X Y. pcompatible_step pbeta_contract X Y \<Longrightarrow>
    pcompatible_step pbeta_contract (PApp X B) (PApp Y B)"
    by (erule pcompatible_step.App_left)
  show "\<And>X Y. pcompatible_step peta_contract X Y \<Longrightarrow>
    pcompatible_step peta_contract (PApp X B) (PApp Y B)"
    by (erule pcompatible_step.App_left)
qed

lemma source_conversion_App_right:
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<sigma> M N"
    and arg: "pterm_in_language \<Sigma> \<Gamma> A (Arr \<sigma> \<tau>)"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> (PApp A M) (PApp A N)"
proof (rule source_conversion_map[where C="PApp A", OF conv])
  show "\<And>X. has_ptype \<Gamma> X \<sigma> \<Longrightarrow> has_ptype \<Gamma> (PApp A X) \<tau>"
    using arg unfolding pterm_in_language_def by (auto intro: has_ptype.PApp)
  show "\<And>X. pterm_in_signature \<Sigma> X \<Longrightarrow> pterm_in_signature \<Sigma> (PApp A X)"
    using arg unfolding pterm_in_language_def by simp
  show "\<And>X Y. pcompatible_step pbeta_contract X Y \<Longrightarrow>
    pcompatible_step pbeta_contract (PApp A X) (PApp A Y)"
    by (erule pcompatible_step.App_right)
  show "\<And>X Y. pcompatible_step peta_contract X Y \<Longrightarrow>
    pcompatible_step peta_contract (PApp A X) (PApp A Y)"
    by (erule pcompatible_step.App_right)
qed

lemma source_conversion_Lam:
  assumes conv: "pbeta_eta_equiv_in_signature \<Sigma> (\<sigma> # \<Gamma>) \<tau> M N"

  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> (Arr \<sigma> \<tau>) (PLam \<sigma> M) (PLam \<sigma> N)"
proof (rule source_conversion_map[where C="PLam \<sigma>", OF conv])
  show "\<And>X. has_ptype (\<sigma> # \<Gamma>) X \<tau> \<Longrightarrow> has_ptype \<Gamma> (PLam \<sigma> X) (Arr \<sigma> \<tau>)"
    by (erule has_ptype.PLam)
  show "\<And>X. pterm_in_signature \<Sigma> X \<Longrightarrow> pterm_in_signature \<Sigma> (PLam \<sigma> X)"
    by simp
  show "\<And>X Y. pcompatible_step pbeta_contract X Y \<Longrightarrow>
    pcompatible_step pbeta_contract (PLam \<sigma> X) (PLam \<sigma> Y)"
    by (erule pcompatible_step.Lam_body)
  show "\<And>X Y. pcompatible_step peta_contract X Y \<Longrightarrow>
    pcompatible_step peta_contract (PLam \<sigma> X) (PLam \<sigma> Y)"
    by (erule pcompatible_step.Lam_body)
qed

lemma source_conversion_Conj:
  assumes left: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop A A'"
    and right: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop B B'"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (PConj A B) (PConj A' B')"
  by (rule pbeta_eta_equiv_in_signature.Trans[
    OF source_conversion_Conj_left[OF left source_conversion_left_language[OF right]]
    source_conversion_Conj_right[OF right source_conversion_right_language[OF left]]])

lemma source_conversion_Disj:
  assumes left: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop A A'"
    and right: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop B B'"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> Prop (PDisj A B) (PDisj A' B')"
  by (rule pbeta_eta_equiv_in_signature.Trans[
    OF source_conversion_Disj_left[OF left source_conversion_left_language[OF right]]
    source_conversion_Disj_right[OF right source_conversion_right_language[OF left]]])

lemma source_conversion_App:
  assumes left: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> (Arr \<sigma> \<tau>) A A'"
    and right: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<sigma> B B'"
  shows "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> (PApp A B) (PApp A' B')"
  by (rule pbeta_eta_equiv_in_signature.Trans[
    OF source_conversion_App_left[OF left source_conversion_left_language[OF right]]
    source_conversion_App_right[OF right source_conversion_right_language[OF left]]])

end
