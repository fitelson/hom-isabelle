theory Bacon_Conversion
  imports Bacon_Zeta
begin

section \<open>Beta-eta conversion as a standalone relation\<close>

text \<open>
  The derivability systems already contain beta and eta conversion rules for
  formulas.  This theory factors the conversion relation itself away from those
  proof systems.  The relation remains syntactic and typed; it is not a quotient
  of object-language terms.

  Standardly, \<open>beta_eta_equiv \<Gamma> \<tau> M N\<close> is written
  \<open>\<Gamma> \<turnstile> M \<equiv>\<^sub>\<beta>\<^sub>\<eta> N : \<tau>\<close>.  At proposition type the main
  bridge concludes the object-language biconditional
  \<open>\<Gamma> \<turnstile>\<^sub>H M \<longleftrightarrow>\<^sub>o N\<close>.  It does not add an Isabelle/HOL axiom
  identifying arbitrary beta-eta equivalent terms.
\<close>

inductive beta_eta_equiv :: "ctx \<Rightarrow> otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> bool" where
  Refl[intro]: "\<Gamma> \<turnstile> M : \<tau> \<Longrightarrow> beta_eta_equiv \<Gamma> \<tau> M M"
| Beta[intro]: "\<Gamma> \<turnstile> M : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> N : \<tau> \<Longrightarrow>
    compatible_step beta_contract M N \<Longrightarrow> beta_eta_equiv \<Gamma> \<tau> M N"
| Eta[intro]: "\<Gamma> \<turnstile> M : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> N : \<tau> \<Longrightarrow>
    compatible_step eta_contract M N \<Longrightarrow> beta_eta_equiv \<Gamma> \<tau> M N"
| Sym[intro]: "beta_eta_equiv \<Gamma> \<tau> M N \<Longrightarrow> beta_eta_equiv \<Gamma> \<tau> N M"
| Trans[intro]: "beta_eta_equiv \<Gamma> \<tau> M N \<Longrightarrow>
    beta_eta_equiv \<Gamma> \<tau> N P \<Longrightarrow> beta_eta_equiv \<Gamma> \<tau> M P"

lemma beta_eta_equiv_types:
  assumes "beta_eta_equiv \<Gamma> \<tau> M N"
  shows "\<Gamma> \<turnstile> M : \<tau> \<and> \<Gamma> \<turnstile> N : \<tau>"
  using assms
proof (induction rule: beta_eta_equiv.induct)
  case (Refl \<Gamma> M \<tau>)
  then show ?case by simp
next
  case (Beta \<Gamma> M \<tau> N)
  then show ?case by simp
next
  case (Eta \<Gamma> M \<tau> N)
  then show ?case by simp
next
  case (Sym \<Gamma> \<tau> M N)
  then show ?case by simp
next
  case (Trans \<Gamma> \<tau> M N P)
  then show ?case by simp
qed

lemma beta_eta_equiv_left_type:
  assumes "beta_eta_equiv \<Gamma> \<tau> M N"
  shows "\<Gamma> \<turnstile> M : \<tau>"
  using beta_eta_equiv_types[OF assms] by simp

lemma beta_eta_equiv_right_type:
  assumes "beta_eta_equiv \<Gamma> \<tau> M N"
  shows "\<Gamma> \<turnstile> N : \<tau>"
  using beta_eta_equiv_types[OF assms] by simp

subsection \<open>Conversion inside H\<close>

lemma prop_tautology_conj_intro:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "prop_tautology \<Gamma> (Imp A (Imp B (Conj A B)))"
proof -
  have formula_type: "\<Gamma> \<turnstile> Imp A (Imp B (Conj A B)) : Prop"
    using assms by (intro has_type.Imp has_type.Conj)
  have eval: "\<forall>v. prop_eval v (Imp A (Imp B (Conj A B)))"
  proof
    fix v
    show "prop_eval v (Imp A (Imp B (Conj A B)))"
      apply (simp only: prop_eval.simps)
      by blast
  qed
  show ?thesis
    unfolding prop_tautology_def
    using formula_type eval by blast
qed

lemma prop_tautology_bicond_sym:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
  shows "prop_tautology \<Gamma> (Imp (A \<longleftrightarrow>\<^sub>o B) (B \<longleftrightarrow>\<^sub>o A))"
proof -
  have formula_type: "\<Gamma> \<turnstile> Imp (A \<longleftrightarrow>\<^sub>o B) (B \<longleftrightarrow>\<^sub>o A) : Prop"
    using assms by (intro has_type.Imp has_type.Conj)
  have eval: "\<forall>v. prop_eval v (Imp (A \<longleftrightarrow>\<^sub>o B) (B \<longleftrightarrow>\<^sub>o A))"
  proof
    fix v
    show "prop_eval v (Imp (A \<longleftrightarrow>\<^sub>o B) (B \<longleftrightarrow>\<^sub>o A))"
      apply (simp only: prop_eval.simps)
      by blast
  qed
  show ?thesis
    unfolding prop_tautology_def
    using formula_type eval by blast
qed

lemma prop_tautology_bicond_trans:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
  shows "prop_tautology \<Gamma>
      (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp (B \<longleftrightarrow>\<^sub>o C) (A \<longleftrightarrow>\<^sub>o C)))"
proof -
  have formula_type:
      "\<Gamma> \<turnstile> Imp (A \<longleftrightarrow>\<^sub>o B) (Imp (B \<longleftrightarrow>\<^sub>o C) (A \<longleftrightarrow>\<^sub>o C)) : Prop"
    using assms by (intro has_type.Imp has_type.Conj)
  have eval:
      "\<forall>v. prop_eval v
        (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp (B \<longleftrightarrow>\<^sub>o C) (A \<longleftrightarrow>\<^sub>o C)))"
  proof
    fix v
    show "prop_eval v
        (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp (B \<longleftrightarrow>\<^sub>o C) (A \<longleftrightarrow>\<^sub>o C)))"
      apply (simp only: prop_eval.simps)
      by blast
  qed
  show ?thesis
    unfolding prop_tautology_def
    using formula_type eval by blast
qed

lemma H_conj_intro:
  assumes "\<Gamma> \<turnstile>\<^sub>H A"
    and "\<Gamma> \<turnstile>\<^sub>H B"
  shows "\<Gamma> \<turnstile>\<^sub>H Conj A B"
proof -
  have A_type: "\<Gamma> \<turnstile> A : Prop"
    using assms(1) by (rule H_proves_formula)
  have B_type: "\<Gamma> \<turnstile> B : Prop"
    using assms(2) by (rule H_proves_formula)
  have taut: "prop_tautology \<Gamma> (Imp A (Imp B (Conj A B)))"
    using A_type B_type by (rule prop_tautology_conj_intro)
  have "\<Gamma> \<turnstile>\<^sub>H Imp A (Imp B (Conj A B))"
    by (rule H_proves.PC[OF taut])
  then have "\<Gamma> \<turnstile>\<^sub>H Imp B (Conj A B)"
    by (rule H_proves.MP[OF assms(1)])
  then show ?thesis
    by (rule H_proves.MP[OF assms(2)])
qed

lemma H_bicond_refl:
  assumes "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o A)"
proof -
  have imp_self: "\<Gamma> \<turnstile>\<^sub>H Imp A A"
    using assms by (rule H_imp_self)
  show ?thesis
    by (rule H_conj_intro[OF imp_self imp_self])
qed

lemma H_bicond_sym:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
  shows "\<Gamma> \<turnstile>\<^sub>H (B \<longleftrightarrow>\<^sub>o A)"
proof -
  have bicond_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using assms(1,2) by auto
  have target_type: "\<Gamma> \<turnstile> (B \<longleftrightarrow>\<^sub>o A) : Prop"
    using assms(1,2) by auto
  have taut: "prop_tautology \<Gamma> (Imp (A \<longleftrightarrow>\<^sub>o B) (B \<longleftrightarrow>\<^sub>o A))"
    using assms(1,2) by (rule prop_tautology_bicond_sym)
  have "\<Gamma> \<turnstile>\<^sub>H Imp (A \<longleftrightarrow>\<^sub>o B) (B \<longleftrightarrow>\<^sub>o A)"
    by (rule H_proves.PC[OF taut])
  then show ?thesis
    by (rule H_proves.MP[OF assms(3)])
qed

lemma H_bicond_trans:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "\<Gamma> \<turnstile> C : Prop"
    and "\<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
    and "\<Gamma> \<turnstile>\<^sub>H (B \<longleftrightarrow>\<^sub>o C)"
  shows "\<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o C)"
proof -
  have AB_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o B) : Prop"
    using assms(1,2) by auto
  have BC_type: "\<Gamma> \<turnstile> (B \<longleftrightarrow>\<^sub>o C) : Prop"
    using assms(2,3) by auto
  have AC_type: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o C) : Prop"
    using assms(1,3) by auto
  have taut: "prop_tautology \<Gamma>
      (Imp (A \<longleftrightarrow>\<^sub>o B) (Imp (B \<longleftrightarrow>\<^sub>o C) (A \<longleftrightarrow>\<^sub>o C)))"
    using assms(1,2,3) by (rule prop_tautology_bicond_trans)
  have "\<Gamma> \<turnstile>\<^sub>H Imp (A \<longleftrightarrow>\<^sub>o B) (Imp (B \<longleftrightarrow>\<^sub>o C) (A \<longleftrightarrow>\<^sub>o C))"
    by (rule H_proves.PC[OF taut])
  then have "\<Gamma> \<turnstile>\<^sub>H Imp (B \<longleftrightarrow>\<^sub>o C) (A \<longleftrightarrow>\<^sub>o C)"
    by (rule H_proves.MP[OF assms(4)])
  then show ?thesis
    by (rule H_proves.MP[OF assms(5)])
qed

lemma H_beta_eta_equiv_aux:
  assumes "beta_eta_equiv \<Gamma> \<tau> A B"
  shows "\<tau> = Prop \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
  using assms
proof induction
  case (Refl \<Gamma> M \<tau>)
  have M_type: "\<Gamma> \<turnstile> M : Prop"
    using Refl.hyps Refl.prems by simp
  show ?case
    using M_type by (rule H_bicond_refl)
next
  case (Beta \<Gamma> M \<tau> N)
  have M_type: "\<Gamma> \<turnstile> M : Prop"
    using Beta.hyps(1) Beta.prems by simp
  have N_type: "\<Gamma> \<turnstile> N : Prop"
    using Beta.hyps(2) Beta.prems by simp
  show ?case
    using M_type N_type Beta.hyps(3) by (rule H_proves.Beta)
next
  case (Eta \<Gamma> M \<tau> N)
  have M_type: "\<Gamma> \<turnstile> M : Prop"
    using Eta.hyps(1) Eta.prems by simp
  have N_type: "\<Gamma> \<turnstile> N : Prop"
    using Eta.hyps(2) Eta.prems by simp
  show ?case
    using M_type N_type Eta.hyps(3) by (rule H_proves.Eta)
next
  case (Sym \<Gamma> \<tau> M N)
  have M_type: "\<Gamma> \<turnstile> M : Prop"
    using beta_eta_equiv_left_type[OF Sym.hyps] Sym.prems by simp
  have N_type: "\<Gamma> \<turnstile> N : Prop"
    using beta_eta_equiv_right_type[OF Sym.hyps] Sym.prems by simp
  have MN: "\<Gamma> \<turnstile>\<^sub>H (M \<longleftrightarrow>\<^sub>o N)"
    using Sym.IH Sym.prems by simp
  show ?case
    using M_type N_type MN by (rule H_bicond_sym)
next
  case (Trans \<Gamma> \<tau> M N P)
  have M_type: "\<Gamma> \<turnstile> M : Prop"
    using beta_eta_equiv_left_type[OF Trans.hyps(1)] Trans.prems by simp
  have N_type: "\<Gamma> \<turnstile> N : Prop"
    using beta_eta_equiv_right_type[OF Trans.hyps(1)] Trans.prems by simp
  have P_type: "\<Gamma> \<turnstile> P : Prop"
    using beta_eta_equiv_right_type[OF Trans.hyps(2)] Trans.prems by simp
  have MN: "\<Gamma> \<turnstile>\<^sub>H (M \<longleftrightarrow>\<^sub>o N)"
    using Trans.IH(1) Trans.prems by simp
  have NP: "\<Gamma> \<turnstile>\<^sub>H (N \<longleftrightarrow>\<^sub>o P)"
    using Trans.IH(2) Trans.prems by simp
  show ?case
    using M_type N_type P_type MN NP by (rule H_bicond_trans)
qed

lemma H_beta_eta_equiv:
  assumes "beta_eta_equiv \<Gamma> Prop A B"
  shows "\<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
  using assms by (rule H_beta_eta_equiv_aux) simp

subsection \<open>Lifting conversion through stronger proof systems\<close>

lemma C_beta_eta_equiv:
  assumes "beta_eta_equiv \<Gamma> Prop A B"
  shows "\<Gamma> \<turnstile>\<^sub>C (A \<longleftrightarrow>\<^sub>o B)"
  using H_beta_eta_equiv[OF assms]
  by (rule C_proves.H)

lemma CE_beta_eta_equiv:
  assumes "beta_eta_equiv \<Gamma> Prop A B"
  shows "\<Gamma> \<turnstile>\<^sub>CE (A \<longleftrightarrow>\<^sub>o B)"
  using C_beta_eta_equiv[OF assms]
  by (rule CE_proves.C)

lemma CEV_beta_eta_equiv:
  assumes "beta_eta_equiv \<Gamma> Prop A B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
  using CE_beta_eta_equiv[OF assms]
  by (rule CEV_proves.CE)

subsection \<open>One-step conversion bridges\<close>

lemma H_beta_step:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step beta_contract A B"
  shows "\<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have "beta_eta_equiv \<Gamma> Prop A B"
    using assms by (rule beta_eta_equiv.Beta)
  then show ?thesis
    by (rule H_beta_eta_equiv)
qed

lemma H_eta_step:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step eta_contract A B"
  shows "\<Gamma> \<turnstile>\<^sub>H (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have "beta_eta_equiv \<Gamma> Prop A B"
    using assms by (rule beta_eta_equiv.Eta)
  then show ?thesis
    by (rule H_beta_eta_equiv)
qed

lemma C_beta_step:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step beta_contract A B"
  shows "\<Gamma> \<turnstile>\<^sub>C (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have "beta_eta_equiv \<Gamma> Prop A B"
    using assms by (rule beta_eta_equiv.Beta)
  then show ?thesis
    by (rule C_beta_eta_equiv)
qed

lemma C_eta_step:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step eta_contract A B"
  shows "\<Gamma> \<turnstile>\<^sub>C (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have "beta_eta_equiv \<Gamma> Prop A B"
    using assms by (rule beta_eta_equiv.Eta)
  then show ?thesis
    by (rule C_beta_eta_equiv)
qed

lemma CE_beta_step:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step beta_contract A B"
  shows "\<Gamma> \<turnstile>\<^sub>CE (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have "beta_eta_equiv \<Gamma> Prop A B"
    using assms by (rule beta_eta_equiv.Beta)
  then show ?thesis
    by (rule CE_beta_eta_equiv)
qed

lemma CE_eta_step:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step eta_contract A B"
  shows "\<Gamma> \<turnstile>\<^sub>CE (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have "beta_eta_equiv \<Gamma> Prop A B"
    using assms by (rule beta_eta_equiv.Eta)
  then show ?thesis
    by (rule CE_beta_eta_equiv)
qed

lemma CEV_beta_step:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step beta_contract A B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have "beta_eta_equiv \<Gamma> Prop A B"
    using assms by (rule beta_eta_equiv.Beta)
  then show ?thesis
    by (rule CEV_beta_eta_equiv)
qed

lemma CEV_eta_step:
  assumes "\<Gamma> \<turnstile> A : Prop"
    and "\<Gamma> \<turnstile> B : Prop"
    and "compatible_step eta_contract A B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o B)"
proof -
  have "beta_eta_equiv \<Gamma> Prop A B"
    using assms by (rule beta_eta_equiv.Eta)
  then show ?thesis
    by (rule CEV_beta_eta_equiv)
qed

end
