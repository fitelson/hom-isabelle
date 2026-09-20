theory Bacon_PP_Goodman_Fun_Prime_Axiom_Collapse
  imports 
    "Goodman_Legacy_02.Bacon_PP_Goodman_Fun_Prime_Six_Distinct"
begin

section \<open>Auditor scratch theory for Goodman T2f\<close>

subsection \<open>Small helpers\<close>

lemma CEV_collapse_taut_plus:
  assumes "prop_tautology \<Gamma> A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ A"
  using assms
  by (intro CEV_axiom_proves.Base CEV_proves.CE CE_proves.C
      C_proves.H H_proves.PC)

lemma CEV_collapse_not_ObjFalse:
  "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg ObjFalse"
proof -
  have d_true: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjTrue"
    by (rule CEV_axiom_proves_ObjTrue)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Imp ObjTrue (Neg ObjFalse)"
  proof (rule CEV_collapse_taut_plus)
    show "prop_tautology \<Gamma> (Imp ObjTrue (Neg ObjFalse))"
      unfolding prop_tautology_def ObjFalse_def
      using typed_ObjTrue
      by (auto intro: has_type.Imp has_type.Neg)
  qed
  show ?thesis using d_true taut by (rule CEV_axiom_proves.MP)
qed

text \<open>
  From a refutation of \<open>A\<close> the Rule of Equivalence (available in
  \<open>CEV\<^sup>+\<close> above the axiom stock) yields identity with falsity.
\<close>

lemma CEV_refuted_imp_eq_ObjFalse:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and refuted: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg A"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop A ObjFalse"
proof -
  have taut_type:
    "\<Gamma> \<turnstile>
      Imp (Neg A) (Imp (Neg ObjFalse) (A \<longleftrightarrow>\<^sub>o ObjFalse)) : Prop"
    using A_type typed_ObjFalse
    by (intro has_type.Imp has_type.Neg has_type.Conj)
  have taut:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Neg A) (Imp (Neg ObjFalse) (A \<longleftrightarrow>\<^sub>o ObjFalse))"
  proof (rule CEV_collapse_taut_plus)
    show "prop_tautology \<Gamma>
      (Imp (Neg A) (Imp (Neg ObjFalse) (A \<longleftrightarrow>\<^sub>o ObjFalse)))"
      unfolding prop_tautology_def
      using taut_type by auto
  qed
  have step1:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Neg ObjFalse) (A \<longleftrightarrow>\<^sub>o ObjFalse)"
    using refuted taut by (rule CEV_axiom_proves.MP)
  have iff:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ (A \<longleftrightarrow>\<^sub>o ObjFalse)"
    using CEV_collapse_not_ObjFalse step1 by (rule CEV_axiom_proves.MP)
  show ?thesis
    using A_type typed_ObjFalse iff
    by (rule CEV_axiom_zeroary_equivalence)
qed

subsection \<open>Part 0: what happens if \<open>fun\<acute>(r)\<close> is added as an axiom\<close>

theorem collapse_when_fun_prime_is_an_axiom:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and ax: "pp_fun_prime r \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (Eq Prop r ObjTrue) ObjFalse"
proof -
  have F_type: "\<Gamma> \<turnstile> pp_fun_prime r : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have E_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have d_F: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_fun_prime r"
    using ax F_type by (rule CEV_axiom_proves.Axiom)
  have d_notE:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (Eq Prop r ObjTrue)"
    using d_F CEV_fun_prime_neq_ObjTrue[
      OF pp_T2_min_axioms_into_T6_extension[OF core] r_type]
    by (rule CEV_axiom_proves.MP)
  show ?thesis
    using E_type d_notE by (rule CEV_refuted_imp_eq_ObjFalse)
qed

theorem collapse_when_fun_prime_is_an_axiom_ObjFalse_case:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and ax: "pp_fun_prime r \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (Eq Prop r ObjFalse) ObjFalse"
proof -
  have F_type: "\<Gamma> \<turnstile> pp_fun_prime r : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have E_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have d_F: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_fun_prime r"
    using ax F_type by (rule CEV_axiom_proves.Axiom)
  have d_notE:
    "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (Eq Prop r ObjFalse)"
    using d_F CEV_fun_prime_neq_ObjFalse[
      OF pp_T2_min_axioms_into_T6_extension[OF core] r_type]
    by (rule CEV_axiom_proves.MP)
  show ?thesis
    using E_type d_notE by (rule CEV_refuted_imp_eq_ObjFalse)
qed

text \<open>
  Hence, with \<open>fun\<acute>(r)\<close> axiomatic, the two identity propositions of T2f
  are both identical with falsity, so they are identical with each other:
  T2f fails outright.  In fact the resulting theory is inconsistent.
\<close>

theorem T2f_fails_when_fun_prime_is_an_axiom:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and ax: "pp_fun_prime r \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
    Eq Prop (Eq Prop r ObjTrue) (Eq Prop r ObjFalse)"
proof -
  have ET_type: "\<Gamma> \<turnstile> Eq Prop r ObjTrue : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have EF_type: "\<Gamma> \<turnstile> Eq Prop r ObjFalse : Prop"
    using r_type typed_ObjFalse by (rule has_type.Eq)
  have a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq Prop (Eq Prop r ObjTrue) ObjFalse"
    using core r_type ax by (rule collapse_when_fun_prime_is_an_axiom)
  have b: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Eq Prop (Eq Prop r ObjFalse) ObjFalse"
    using core r_type ax
    by (rule collapse_when_fun_prime_is_an_axiom_ObjFalse_case)
  have a_s: "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Eq Prop r ObjTrue) ObjFalse"
    using a by (simp add: CEV_axiom_from_empty_iff)
  have b_s: "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Eq Prop r ObjFalse) ObjFalse"
    using b by (simp add: CEV_axiom_from_empty_iff)
  have b_sym: "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop ObjFalse (Eq Prop r ObjFalse)"
    using EF_type typed_ObjFalse b_s by (rule CEV_axiom_from_eq_sym)
  have res: "\<Gamma> ; T ; {} \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Eq Prop r ObjTrue) (Eq Prop r ObjFalse)"
    using ET_type typed_ObjFalse EF_type a_s b_sym
    by (rule CEV_axiom_from_eq_trans)
  show ?thesis
    using res by (simp add: CEV_axiom_from_empty_iff)
qed

theorem inconsistent_when_fun_prime_is_an_axiom:
  assumes core: "pp_T6_core_PP_axioms \<subseteq> T"
    and r_type: "\<Gamma> \<turnstile> r : Prop"
    and ax: "pp_fun_prime r \<in> T"
  shows "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ ObjFalse"
proof -
  let ?E = "Eq Prop r ObjTrue"
  have F_type: "\<Gamma> \<turnstile> pp_fun_prime r : Prop"
    using r_type by (rule typed_pp_fun_prime)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using r_type typed_ObjTrue by (rule has_type.Eq)
  have d_F: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ pp_fun_prime r"
    using ax F_type by (rule CEV_axiom_proves.Axiom)
  have d_notE: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg ?E"
    using d_F CEV_fun_prime_neq_ObjTrue[
      OF pp_T2_min_axioms_into_T6_extension[OF core] r_type]
    by (rule CEV_axiom_proves.MP)
  have d_box_notE: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (Neg ?E)"
    using d_notE by (rule CEV_axiom_necessitation)
  have t2c: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_fun_prime r) (Imp (pp_pure Prop ObjTrue) (\<diamond>\<^sub>o ?E))"
    using pp_T2_min_axioms_into_T6_extension[OF core]
      r_type typed_ObjTrue by (rule CEV_Goodman_T2c_parameter)
  have step: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (pp_pure Prop ObjTrue) (\<diamond>\<^sub>o ?E)"
    using d_F t2c by (rule CEV_axiom_proves.MP)
  have d_diamond: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<diamond>\<^sub>o ?E"
    using pp_ObjTrue_pure_in_core_extension[OF core] step
    by (rule CEV_axiom_proves.MP)
  have d_neg: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Neg (\<box>\<^sub>o (Neg ?E))"
    using d_diamond unfolding ObjDiamond_def .
  have box_type: "\<Gamma> \<turnstile> \<box>\<^sub>o (Neg ?E) : Prop"
    using E_type by (intro typed_ObjBox has_type.Neg)
  have taut: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (\<box>\<^sub>o (Neg ?E))
        (Imp (Neg (\<box>\<^sub>o (Neg ?E))) ObjFalse)"
  proof (rule CEV_collapse_taut_plus)
    show "prop_tautology \<Gamma>
      (Imp (\<box>\<^sub>o (Neg ?E))
        (Imp (Neg (\<box>\<^sub>o (Neg ?E))) ObjFalse))"
      unfolding prop_tautology_def
      using box_type typed_ObjFalse
      by (auto intro: has_type.Imp has_type.Neg)
  qed
  have s1: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+
      Imp (Neg (\<box>\<^sub>o (Neg ?E))) ObjFalse"
    using d_box_notE taut by (rule CEV_axiom_proves.MP)
  show ?thesis using d_neg s1 by (rule CEV_axiom_proves.MP)
qed

end
