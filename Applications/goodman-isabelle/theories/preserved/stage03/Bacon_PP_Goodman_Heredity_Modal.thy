theory Bacon_PP_Goodman_Heredity_Modal
  imports
    
    "Goodman_Legacy_03.Bacon_PP_Goodman_Heredity"
    "Goodman_Legacy_03.Bacon_PP_Goodman_WI_Collapse"
begin

section \<open>Modal plumbing for Goodman T3\<close>

subsection \<open>Boxing a conjunction\<close>

lemma CEV_axiom_from_box_conj:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and dA: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o A"
    and dB: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o (Conj A B)"
proof -
  have conj_type: "\<Gamma> \<turnstile> Conj A B : Prop"
    using A_type B_type by (intro has_type.Conj has_type.Imp)
  have taut: "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp B (Conj A B))"
    using A_type B_type
    by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC
        prop_tautology_conj_intro)
  have box_taut:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (Imp A (Imp B (Conj A B)))"
    using CEV_axiom_proves.Base[OF taut] by (rule CEV_axiom_necessitation)
  have K1:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o (Imp A (Imp B (Conj A B))))
        (Imp (\<box>\<^sub>o A) (\<box>\<^sub>o (Imp B (Conj A B))))"
    using CEV_modal_K[OF A_type has_type.Imp[OF B_type conj_type]]
    by (intro CEV_axiom_proves.Base) (simp add: modal_K_def)
  have step1:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o A) (\<box>\<^sub>o (Imp B (Conj A B)))"
    using box_taut K1 by (rule CEV_axiom_proves.MP)
  have d_step1:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (Imp B (Conj A B))"
    using dA CEV_axiom_from.Theorem[OF step1] by (rule CEV_axiom_from.MP)
  have K2:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o (Imp B (Conj A B)))
        (Imp (\<box>\<^sub>o B) (\<box>\<^sub>o (Conj A B)))"
    using CEV_modal_K[OF B_type conj_type]
    by (intro CEV_axiom_proves.Base) (simp add: modal_K_def)
  have d_step2:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (\<box>\<^sub>o B) (\<box>\<^sub>o (Conj A B))"
    using d_step1 CEV_axiom_from.Theorem[OF K2] by (rule CEV_axiom_from.MP)
  show ?thesis
    using dB d_step2 by (rule CEV_axiom_from.MP)
qed

subsection \<open>Necessity of identity, in the local judgement\<close>

lemma CEV_axiom_from_box_of_eq:
  assumes M_type: "\<Gamma> \<turnstile> M : \<sigma>"
    and N_type: "\<Gamma> \<turnstile> N : \<sigma>"
    and d: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq \<sigma> M N"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o (Eq \<sigma> M N)"
proof -
  have rigid:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Eq \<sigma> M N) (\<box>\<^sub>o (Eq \<sigma> M N))"
    using CEV_eq_truth_of_eq[OF M_type N_type] by (simp add: ObjBox_def)
  show ?thesis
    using d
      CEV_axiom_from.Theorem[OF CEV_axiom_proves.Base[OF rigid]]
    by (rule CEV_axiom_from.MP)
qed

subsection \<open>The K-transfer used by T3\<close>

text \<open>
  If \<open>A \<longrightarrow> (B \<longrightarrow> D)\<close> is a theorem of the axiom extension, then
  \<open>\<box>A\<close> together with \<open>\<diamond>B\<close> yields \<open>\<diamond>D\<close>.  The implication
  must be a theorem, not a local assumption: necessitation is applied to it.
\<close>

lemma CEV_axiom_from_box_diamond_mp:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and B_type: "\<Gamma> \<turnstile> B : Prop"
    and D_type: "\<Gamma> \<turnstile> D : Prop"
    and imp_thm: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp A (Imp B D)"
    and dboxA: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o A"
    and ddiaB: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o B"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o D"
proof -
  have BD_type: "\<Gamma> \<turnstile> Imp B D : Prop"
    using B_type D_type by (rule has_type.Imp)
  have box_thm: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (Imp A (Imp B D))"
    using imp_thm by (rule CEV_axiom_necessitation)
  have K1:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o (Imp A (Imp B D)))
        (Imp (\<box>\<^sub>o A) (\<box>\<^sub>o (Imp B D)))"
    using CEV_modal_K[OF A_type BD_type]
    by (intro CEV_axiom_proves.Base) (simp add: modal_K_def)
  have step:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o A) (\<box>\<^sub>o (Imp B D))"
    using box_thm K1 by (rule CEV_axiom_proves.MP)
  have d_boxBD:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o (Imp B D)"
    using dboxA CEV_axiom_from.Theorem[OF step] by (rule CEV_axiom_from.MP)
  \<comment> \<open>from \<open>\<box>(B \<longrightarrow> D)\<close> to \<open>\<diamond>B \<longrightarrow> \<diamond>D\<close>\<close>
  have neg_B_type: "\<Gamma> \<turnstile> Neg B : Prop"
    using B_type by (rule has_type.Neg)
  have neg_D_type: "\<Gamma> \<turnstile> Neg D : Prop"
    using D_type by (rule has_type.Neg)
  have contra_taut:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp B D) (Imp (Neg D) (Neg B))"
  proof (rule CEV_prop_tautology)
    have type:
      "\<Gamma> \<turnstile> Imp (Imp B D) (Imp (Neg D) (Neg B)) : Prop"
      using B_type D_type by auto
    moreover have
      "\<forall>v. prop_eval v (Imp (Imp B D) (Imp (Neg D) (Neg B)))"
      apply (simp only: prop_eval.simps) by blast
    ultimately show
      "prop_tautology \<Gamma> (Imp (Imp B D) (Imp (Neg D) (Neg B)))"
      unfolding prop_tautology_def by blast
  qed
  have box_contra:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      \<box>\<^sub>o (Imp (Imp B D) (Imp (Neg D) (Neg B)))"
    using CEV_axiom_proves.Base[OF contra_taut]
    by (rule CEV_axiom_necessitation)
  have K2:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o (Imp (Imp B D) (Imp (Neg D) (Neg B))))
        (Imp (\<box>\<^sub>o (Imp B D))
          (\<box>\<^sub>o (Imp (Neg D) (Neg B))))"
    using CEV_modal_K[OF BD_type has_type.Imp[OF neg_D_type neg_B_type]]
    by (intro CEV_axiom_proves.Base) (simp add: modal_K_def)
  have step2:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o (Imp B D))
        (\<box>\<^sub>o (Imp (Neg D) (Neg B)))"
    using box_contra K2 by (rule CEV_axiom_proves.MP)
  have d_box_contra:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      \<box>\<^sub>o (Imp (Neg D) (Neg B))"
    using d_boxBD CEV_axiom_from.Theorem[OF step2] by (rule CEV_axiom_from.MP)
  have K3:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o (Imp (Neg D) (Neg B)))
        (Imp (\<box>\<^sub>o (Neg D)) (\<box>\<^sub>o (Neg B)))"
    using CEV_modal_K[OF neg_D_type neg_B_type]
    by (intro CEV_axiom_proves.Base) (simp add: modal_K_def)
  have d_box_imp:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (\<box>\<^sub>o (Neg D)) (\<box>\<^sub>o (Neg B))"
    using d_box_contra CEV_axiom_from.Theorem[OF K3] by (rule CEV_axiom_from.MP)
  have box_neg_B_type: "\<Gamma> \<turnstile> \<box>\<^sub>o (Neg B) : Prop"
    using neg_B_type by (rule typed_ObjBox)
  have box_neg_D_type: "\<Gamma> \<turnstile> \<box>\<^sub>o (Neg D) : Prop"
    using neg_D_type by (rule typed_ObjBox)
  have outer_taut:
    "\<Gamma> \<turnstile>\<^sub>CEV
      Imp (Imp (\<box>\<^sub>o (Neg D)) (\<box>\<^sub>o (Neg B)))
        (Imp (Neg (\<box>\<^sub>o (Neg B))) (Neg (\<box>\<^sub>o (Neg D))))"
  proof (rule CEV_prop_tautology)
    have type:
      "\<Gamma> \<turnstile>
        Imp (Imp (\<box>\<^sub>o (Neg D)) (\<box>\<^sub>o (Neg B)))
          (Imp (Neg (\<box>\<^sub>o (Neg B)))
            (Neg (\<box>\<^sub>o (Neg D)))) : Prop"
      using box_neg_B_type box_neg_D_type by auto
    moreover have
      "\<forall>v. prop_eval v
        (Imp (Imp (\<box>\<^sub>o (Neg D)) (\<box>\<^sub>o (Neg B)))
          (Imp (Neg (\<box>\<^sub>o (Neg B)))
            (Neg (\<box>\<^sub>o (Neg D)))))"
      apply (simp only: prop_eval.simps) by blast
    ultimately show
      "prop_tautology \<Gamma>
        (Imp (Imp (\<box>\<^sub>o (Neg D)) (\<box>\<^sub>o (Neg B)))
          (Imp (Neg (\<box>\<^sub>o (Neg B)))
            (Neg (\<box>\<^sub>o (Neg D)))))"
      unfolding prop_tautology_def by blast
  qed
  have d_dia_imp:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Imp (Neg (\<box>\<^sub>o (Neg B))) (Neg (\<box>\<^sub>o (Neg D)))"
    using d_box_imp
      CEV_axiom_from.Theorem[OF CEV_axiom_proves.Base[OF outer_taut]]
    by (rule CEV_axiom_from.MP)
  show ?thesis
    using ddiaB d_dia_imp unfolding ObjDiamond_def
    by (rule CEV_axiom_from.MP)
qed

end
