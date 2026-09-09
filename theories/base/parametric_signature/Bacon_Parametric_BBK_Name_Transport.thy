theory Bacon_Parametric_BBK_Name_Transport
  imports Bacon_Parametric_H_Soundness Bacon_Parametric_Henkin_One_Step
begin

section \<open>Pulling a BBK interpretation back along constant names\<close>

text \<open>
  ⟦A⟧pull,g = ⟦k(A)⟧target,g, with Dpull = Dtarget and Vpull = Vtarget.
  Source role: the signature-expansion and restriction step of
  Bacon–Dorr, Theorem 3.2, p. 45 n. 64; Bacon, Theorem 15.3, pp. 320–321.

  Isabelle representation: phenkin_map k changes only constant names, not
  their object types or free-variable slots.  The source-name, target-name,
  and semantic-value carriers are three independent HOL types.  Every
  source-declared constant must map to a target-declared constant of the
  same type.

  Status: all model fields and truth are preserved.  No completeness or
  model-existence assumption is used.  Injectivity is needed for a faithful
  syntax embedding, but not for this semantic pullback; the injective
  corollary is stated separately.
\<close>

lemma pbbk_name_map_fv:
  "pbbk_fv (phenkin_map k A) = pbbk_fv A"
  by (induction A) (simp_all only: phenkin_map.simps pbbk_fv.simps)

lemma pbbk_name_map_conversion:
  assumes "pbeta_eta_equiv \<Gamma> \<tau> M N"
  shows "pbeta_eta_equiv \<Gamma> \<tau> (phenkin_map k M) (phenkin_map k N)"
  using assms
proof (induction rule: pbeta_eta_equiv.induct)
  case (Refl \<Gamma> M \<tau>)
  show ?case by (rule pbeta_eta_equiv.Refl[OF phenkin_map_type[OF Refl.hyps]])
next
  case (Beta \<Gamma> M \<tau> N)
  have step: "pcompatible_step pbeta_contract (phenkin_map k M) (phenkin_map k N)"
    by (rule phenkin_map_compatible[OF Beta.hyps(3)]) (rule phenkin_map_beta)
  show ?case by (rule pbeta_eta_equiv.Beta[OF phenkin_map_type[OF Beta.hyps(1)]
    phenkin_map_type[OF Beta.hyps(2)] step])
next
  case (Eta \<Gamma> M \<tau> N)
  have step: "pcompatible_step peta_contract (phenkin_map k M) (phenkin_map k N)"
    by (rule phenkin_map_compatible[OF Eta.hyps(3)]) (rule phenkin_map_eta)
  show ?case by (rule pbeta_eta_equiv.Eta[OF phenkin_map_type[OF Eta.hyps(1)]
    phenkin_map_type[OF Eta.hyps(2)] step])
next
  case (Sym \<Gamma> \<tau> M N)
  show ?case by (rule pbeta_eta_equiv.Sym[OF Sym.IH])
next
  case (Trans \<Gamma> \<tau> M N P)
  show ?case by (rule pbeta_eta_equiv.Trans[OF Trans.IH])
qed

lemma pbbk_name_map_conversion_in_signature:
  assumes conversion: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<tau> M N"
    and names: "\<And>c \<sigma>. c \<in> \<Sigma> \<sigma> \<Longrightarrow> k c \<in> \<Delta> \<sigma>"
  shows "pbeta_eta_equiv_in_signature \<Delta> \<Gamma> \<tau>
    (phenkin_map k M) (phenkin_map k N)"
  using conversion
proof (induction rule: pbeta_eta_equiv_in_signature.induct)
  case (Refl \<Gamma> M \<tau>)
  have mapped_sig: "pterm_in_signature \<Delta> (phenkin_map k M)"
    by (rule phenkin_map_signature[OF Refl.hyps(2) names])
  show ?case by (rule pbeta_eta_equiv_in_signature.Refl[
        OF phenkin_map_type[OF Refl.hyps(1)] mapped_sig])
next
  case (Beta \<Gamma> M \<tau> N)
  have ms: "pterm_in_signature \<Delta> (phenkin_map k M)"
    by (rule phenkin_map_signature[OF Beta.hyps(3) names])
  have ns: "pterm_in_signature \<Delta> (phenkin_map k N)"
    by (rule phenkin_map_signature[OF Beta.hyps(4) names])
  have step: "pcompatible_step pbeta_contract (phenkin_map k M) (phenkin_map k N)"
    by (rule phenkin_map_compatible[OF Beta.hyps(5)]) (rule phenkin_map_beta)
  show ?case by (rule pbeta_eta_equiv_in_signature.Beta[
        OF phenkin_map_type[OF Beta.hyps(1)] phenkin_map_type[OF Beta.hyps(2)] ms ns step])
next
  case (Eta \<Gamma> M \<tau> N)
  have ms: "pterm_in_signature \<Delta> (phenkin_map k M)"
    by (rule phenkin_map_signature[OF Eta.hyps(3) names])
  have ns: "pterm_in_signature \<Delta> (phenkin_map k N)"
    by (rule phenkin_map_signature[OF Eta.hyps(4) names])
  have step: "pcompatible_step peta_contract (phenkin_map k M) (phenkin_map k N)"
    by (rule phenkin_map_compatible[OF Eta.hyps(5)]) (rule phenkin_map_eta)
  show ?case by (rule pbeta_eta_equiv_in_signature.Eta[
        OF phenkin_map_type[OF Eta.hyps(1)] phenkin_map_type[OF Eta.hyps(2)] ms ns step])
next
  case (Sym \<Gamma> \<tau> M N)
  show ?case by (rule pbeta_eta_equiv_in_signature.Sym[OF Sym.IH])
next
  case (Trans \<Gamma> \<tau> M N P)
  show ?case by (rule pbeta_eta_equiv_in_signature.Trans[OF Trans.IH])
qed

definition pbbk_pullback_denote ::
    "('c \<Rightarrow> 'd) \<Rightarrow> ((nat \<Rightarrow> 'v) \<Rightarrow> 'd pterm \<Rightarrow> 'v) \<Rightarrow>
     (nat \<Rightarrow> 'v) \<Rightarrow> 'c pterm \<Rightarrow> 'v" where
  "pbbk_pullback_denote k J g A = J g (phenkin_map k A)"

theorem pbbk_model_name_pullback:
  fixes k :: "'c \<Rightarrow> 'd"
    and J :: "(nat \<Rightarrow> 'v) \<Rightarrow> 'd pterm \<Rightarrow> 'v"
  assumes model: "pbbk_model \<Delta> D J V"
    and names: "\<And>c \<sigma>. c \<in> \<Sigma> \<sigma> \<Longrightarrow> k c \<in> \<Delta> \<sigma>"
  shows "pbbk_model \<Sigma> D (pbbk_pullback_denote k J) V"
proof -
  interpret Target: pbbk_model \<Delta> D J V by (rule model)
  have mapped_sig: "pterm_in_signature \<Delta> (phenkin_map k A)"
    if "pterm_in_signature \<Sigma> A" for A
    by (rule phenkin_map_signature[OF that names])
  show ?thesis
  proof (unfold_locales)
    show "D \<sigma> \<noteq> {}" for \<sigma> by (rule Target.domain_nonempty)
  next
    fix \<Gamma> M \<sigma> g
    assume mt: "has_ptype \<Gamma> M \<sigma>" and ms: "pterm_in_signature \<Sigma> M"
      and env: "pbbk_env_typed D \<Gamma> g"
    show "pbbk_pullback_denote k J g M \<in> D \<sigma>"
      unfolding pbbk_pullback_denote_def
      by (rule Target.denote_type[OF phenkin_map_type[OF mt] mapped_sig[OF ms] env])
  next
    fix \<Gamma> n \<sigma> g
    assume look: "lookup \<Gamma> n = Some \<sigma>" and env: "pbbk_env_typed D \<Gamma> g"
    show "pbbk_pullback_denote k J g (PVar n) = g n"
      by (simp only: pbbk_pullback_denote_def phenkin_map.simps Target.denote_var[OF look env])
  next
    fix \<Gamma> F \<sigma> \<tau> A \<Pi> G B g h
    assume ft: "has_ptype \<Gamma> F (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and at: "has_ptype \<Gamma> A \<sigma>"
      and gt: "has_ptype \<Pi> G (\<sigma> \<rightarrow>\<^sub>o \<tau>)" and bt: "has_ptype \<Pi> B \<sigma>"
      and fs: "pterm_in_signature \<Sigma> (PApp F A)" and gs: "pterm_in_signature \<Sigma> (PApp G B)"
      and ge: "pbbk_env_typed D \<Gamma> g" and he: "pbbk_env_typed D \<Pi> h"
      and fg: "pbbk_pullback_denote k J g F = pbbk_pullback_denote k J h G"
      and ab: "pbbk_pullback_denote k J g A = pbbk_pullback_denote k J h B"
    have mfs: "pterm_in_signature \<Delta> (PApp (phenkin_map k F) (phenkin_map k A))"
      using mapped_sig[OF fs] by (simp only: phenkin_map.simps)
    have mgs: "pterm_in_signature \<Delta> (PApp (phenkin_map k G) (phenkin_map k B))"
      using mapped_sig[OF gs] by (simp only: phenkin_map.simps)
    have mfg: "J g (phenkin_map k F) = J h (phenkin_map k G)"
      using fg unfolding pbbk_pullback_denote_def .
    have mab: "J g (phenkin_map k A) = J h (phenkin_map k B)"
      using ab unfolding pbbk_pullback_denote_def .
    have result: "J g (PApp (phenkin_map k F) (phenkin_map k A)) =
        J h (PApp (phenkin_map k G) (phenkin_map k B))"
      by (rule Target.denote_application_cong[OF phenkin_map_type[OF ft] phenkin_map_type[OF at]
        phenkin_map_type[OF gt] phenkin_map_type[OF bt] mfs mgs ge he mfg mab])
    show "pbbk_pullback_denote k J g (PApp F A) = pbbk_pullback_denote k J h (PApp G B)"
      by (simp only: pbbk_pullback_denote_def phenkin_map.simps result)
  next
    fix \<Gamma> M \<sigma> \<Pi> g h
    assume mt: "has_ptype \<Gamma> M \<sigma>" and nt: "has_ptype \<Pi> M \<sigma>"
      and ms: "pterm_in_signature \<Sigma> M"
      and ge: "pbbk_env_typed D \<Gamma> g" and he: "pbbk_env_typed D \<Pi> h"
      and agree: "\<And>n. n \<in> pbbk_fv M \<Longrightarrow> g n = h n"
    have mapped_agree: "g n = h n" if "n \<in> pbbk_fv (phenkin_map k M)" for n
    proof -
      have original: "n \<in> pbbk_fv M" using that by (simp only: pbbk_name_map_fv)
      show ?thesis by (rule agree[OF original])
    qed
    show "pbbk_pullback_denote k J g M = pbbk_pullback_denote k J h M"
      unfolding pbbk_pullback_denote_def
      by (rule Target.denote_locality[OF phenkin_map_type[OF mt] phenkin_map_type[OF nt]
        mapped_sig[OF ms] ge he mapped_agree])
  next
    fix \<Gamma> M \<sigma> r \<Pi> g
    assume mt: "has_ptype \<Gamma> M \<sigma>" and ms: "pterm_in_signature \<Sigma> M"
      and inj: "inj r" and env: "pbbk_env_typed D \<Pi> g"
      and ren: "\<And>n \<tau>. lookup \<Gamma> n = Some \<tau> \<Longrightarrow> lookup \<Pi> (r n) = Some \<tau>"
    have result: "J g (prename r (phenkin_map k M)) =
        J (\<lambda>n. g (r n)) (phenkin_map k M)"
      by (rule Target.denote_rename[OF phenkin_map_type[OF mt] mapped_sig[OF ms] inj env ren])
    show "pbbk_pullback_denote k J g (prename r M) = pbbk_pullback_denote k J (\<lambda>n. g (r n)) M"
      by (simp only: pbbk_pullback_denote_def phenkin_map_prename result)
  next
    fix \<Gamma> \<sigma> M N g
    assume conv: "pbeta_eta_equiv_in_signature \<Sigma> \<Gamma> \<sigma> M N"
      and ms: "pterm_in_signature \<Sigma> M" and ns: "pterm_in_signature \<Sigma> N"
      and env: "pbbk_env_typed D \<Gamma> g"
    show "pbbk_pullback_denote k J g M = pbbk_pullback_denote k J g N"
      unfolding pbbk_pullback_denote_def
      by (rule Target.denote_beta_eta[OF pbbk_name_map_conversion_in_signature[OF conv names]
        mapped_sig[OF ms] mapped_sig[OF ns] env])
  next
    fix \<Gamma> A g
    assume at: "has_ptype \<Gamma> A Prop" and sa: "pterm_in_signature \<Sigma> A"
      and env: "pbbk_env_typed D \<Gamma> g"
    show "V (pbbk_pullback_denote k J g (PNeg A)) = (\<not> V (pbbk_pullback_denote k J g A))"
      by (simp only: pbbk_pullback_denote_def phenkin_map.simps
        Target.valuation_neg[OF phenkin_map_type[OF at] mapped_sig[OF sa] env])
  next
    fix \<Gamma> A B g
    assume at: "has_ptype \<Gamma> A Prop" and bt: "has_ptype \<Gamma> B Prop"
      and sa: "pterm_in_signature \<Sigma> A" and sb: "pterm_in_signature \<Sigma> B"
      and env: "pbbk_env_typed D \<Gamma> g"
    show "V (pbbk_pullback_denote k J g (PConj A B)) =
        (V (pbbk_pullback_denote k J g A) \<and> V (pbbk_pullback_denote k J g B))"
      by (simp only: pbbk_pullback_denote_def phenkin_map.simps
        Target.valuation_conj[OF phenkin_map_type[OF at] phenkin_map_type[OF bt]
          mapped_sig[OF sa] mapped_sig[OF sb] env])
  next
    fix \<Gamma> A B g
    assume at: "has_ptype \<Gamma> A Prop" and bt: "has_ptype \<Gamma> B Prop"
      and sa: "pterm_in_signature \<Sigma> A" and sb: "pterm_in_signature \<Sigma> B"
      and env: "pbbk_env_typed D \<Gamma> g"
    show "V (pbbk_pullback_denote k J g (PDisj A B)) =
        (V (pbbk_pullback_denote k J g A) \<or> V (pbbk_pullback_denote k J g B))"
      by (simp only: pbbk_pullback_denote_def phenkin_map.simps
        Target.valuation_disj[OF phenkin_map_type[OF at] phenkin_map_type[OF bt]
          mapped_sig[OF sa] mapped_sig[OF sb] env])
  next
    fix \<Gamma> A B g
    assume at: "has_ptype \<Gamma> A Prop" and bt: "has_ptype \<Gamma> B Prop"
      and sa: "pterm_in_signature \<Sigma> A" and sb: "pterm_in_signature \<Sigma> B"
      and env: "pbbk_env_typed D \<Gamma> g"
    show "V (pbbk_pullback_denote k J g (PImp A B)) =
        (V (pbbk_pullback_denote k J g A) \<longrightarrow> V (pbbk_pullback_denote k J g B))"
      by (simp only: pbbk_pullback_denote_def phenkin_map.simps
        Target.valuation_imp[OF phenkin_map_type[OF at] phenkin_map_type[OF bt]
          mapped_sig[OF sa] mapped_sig[OF sb] env])
  next
    fix \<sigma> \<Gamma> A g
    assume at: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sa: "pterm_in_signature \<Sigma> A"
      and env: "pbbk_env_typed D \<Gamma> g"
    show "V (pbbk_pullback_denote k J g (PForall \<sigma> A)) =
        (\<forall>a \<in> D \<sigma>. V (pbbk_pullback_denote k J (pbbk_extend a g) A))"
      by (simp only: pbbk_pullback_denote_def phenkin_map.simps
        Target.valuation_forall[OF phenkin_map_type[OF at] mapped_sig[OF sa] env])
  next
    fix \<sigma> \<Gamma> A g
    assume at: "has_ptype (\<sigma> # \<Gamma>) A Prop" and sa: "pterm_in_signature \<Sigma> A"
      and env: "pbbk_env_typed D \<Gamma> g"
    show "V (pbbk_pullback_denote k J g (PExists \<sigma> A)) =
        (\<exists>a \<in> D \<sigma>. V (pbbk_pullback_denote k J (pbbk_extend a g) A))"
      by (simp only: pbbk_pullback_denote_def phenkin_map.simps
        Target.valuation_exists[OF phenkin_map_type[OF at] mapped_sig[OF sa] env])
  next
    fix \<Gamma> M \<sigma> N g
    assume mt: "has_ptype \<Gamma> M \<sigma>" and nt: "has_ptype \<Gamma> N \<sigma>"
      and ms: "pterm_in_signature \<Sigma> M" and ns: "pterm_in_signature \<Sigma> N"
      and env: "pbbk_env_typed D \<Gamma> g"
    show "V (pbbk_pullback_denote k J g (PEq \<sigma> M N)) =
        (pbbk_pullback_denote k J g M = pbbk_pullback_denote k J g N)"
      by (simp only: pbbk_pullback_denote_def phenkin_map.simps
        Target.valuation_identity[OF phenkin_map_type[OF mt] phenkin_map_type[OF nt]
          mapped_sig[OF ms] mapped_sig[OF ns] env])
  qed
qed

corollary pbbk_model_injective_name_pullback:
  assumes "pbbk_model \<Delta> D J V" and "inj k"
    and "\<And>c \<sigma>. c \<in> \<Sigma> \<sigma> \<Longrightarrow> k c \<in> \<Delta> \<sigma>"
  shows "pbbk_model \<Sigma> D (pbbk_pullback_denote k J) V"
  by (rule pbbk_model_name_pullback[OF assms(1,3)])

section \<open>Truth and realization of source theories\<close>

text \<open>
  𝔐pull,g ⊨ A ⇔ 𝔐target,g ⊨ k(A).
  The equality of truth values is definitional; the preceding theorem
  supplies the nontrivial fact that the pulled interpretation is a BBK
  model.  Quantifiers keep the full original semantic domains, including
  values unnamed by source constants.  No model existence is inferred.
\<close>

lemma pbbk_name_pullback_truth:
  "V (pbbk_pullback_denote k J g A) \<longleftrightarrow> V (J g (phenkin_map k A))"
  by (simp only: pbbk_pullback_denote_def)

lemma pbbk_name_pullback_realizes:
  assumes "\<And>A g. A \<in> S \<Longrightarrow> pbbk_env_typed D \<Gamma> g \<Longrightarrow>
    V (J g (phenkin_map k A))"
  shows "\<And>A g. A \<in> S \<Longrightarrow> pbbk_env_typed D \<Gamma> g \<Longrightarrow>
    V (pbbk_pullback_denote k J g A)"
proof -
  fix A g
  assume member: "A \<in> S" and env: "pbbk_env_typed D \<Gamma> g"
  have "V (J g (phenkin_map k A))" by (rule assms[OF member env])
  then show "V (pbbk_pullback_denote k J g A)" by (simp only: pbbk_pullback_denote_def)
qed

end
