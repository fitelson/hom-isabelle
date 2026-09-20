theory Bacon_PP_Goodman_T2f_Separation
  imports 
    "Goodman_Legacy_02.Bacon_PP_Goodman_T2f_Operators"
begin

section \<open>Separation machinery for T2f\<close>

subsection \<open>Generic helpers in the local layer\<close>

lemma CEVs_eq_refl:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop A A"
proof -
  have iff: "\<Gamma> \<turnstile>\<^sub>CEV (A \<longleftrightarrow>\<^sub>o A)"
  proof (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.PC)
    have t: "\<Gamma> \<turnstile> (A \<longleftrightarrow>\<^sub>o A) : Prop"
      using A_type by (intro has_type.Conj has_type.Imp)
    show "prop_tautology \<Gamma> (A \<longleftrightarrow>\<^sub>o A)"
      unfolding prop_tautology_def using t by auto
  qed
  have "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop A A"
    using A_type A_type iff by (rule CEV_zeroary_equivalence)
  then show ?thesis
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
qed

lemma CEVs_eq_of_beta:
  assumes X_type: "\<Gamma> \<turnstile> X : Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : Prop"
    and step: "compatible_step beta_contract X Y"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop X Y"
proof -
  have iff: "\<Gamma> \<turnstile>\<^sub>CEV (X \<longleftrightarrow>\<^sub>o Y)"
    using X_type Y_type step by (rule CEV_beta_step)
  have "\<Gamma> \<turnstile>\<^sub>CEV Eq Prop X Y"
    using X_type Y_type iff by (rule CEV_zeroary_equivalence)
  then show ?thesis
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
qed

lemma CEVs_eq_prop_intro:
  assumes X_type: "\<Gamma> \<turnstile> X : Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : Prop"
    and dY: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Y"
    and XY: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop X Y"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s X"
proof -
  have YX: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop Y X"
    using X_type Y_type XY by (rule CEV_axiom_from_eq_sym)
  show ?thesis
    using Y_type X_type dY YX by (rule CEV_axiom_from_eq_prop_elim)
qed

subsection \<open>Congruence for negation\<close>

lemma CEVs_eq_neg_cong:
  assumes X_type: "\<Gamma> \<turnstile> X : Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : Prop"
    and XY: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop X Y"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop (Neg X) (Neg Y)"
proof -
  have nX_type: "\<Gamma> \<turnstile> Neg X : Prop"
    using X_type by (rule has_type.Neg)
  have nY_type: "\<Gamma> \<turnstile> Neg Y : Prop"
    using Y_type by (rule has_type.Neg)
  have N_type: "\<Gamma> \<turnstile> pp_negation_operator : pp_unary_ty"
    by (rule typed_pp_negation_operator)
  have appX_type: "\<Gamma> \<turnstile> App pp_negation_operator X : Prop"
    using N_type X_type unfolding pp_unary_ty_def by (rule has_type.App)
  have appY_type: "\<Gamma> \<turnstile> App pp_negation_operator Y : Prop"
    using N_type Y_type unfolding pp_unary_ty_def by (rule has_type.App)
  have cong:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_negation_operator X) (App pp_negation_operator Y)"
    using N_type X_type Y_type XY
    unfolding pp_unary_ty_def
    by (rule CEV_axiom_from_eq_app_right)
  have bX:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_negation_operator X) (Neg X)"
    using CEV_pp_negation_apply_eq[OF X_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have bY:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App pp_negation_operator Y) (Neg Y)"
    using CEV_pp_negation_apply_eq[OF Y_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  have bX_sym:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg X) (App pp_negation_operator X)"
    using appX_type nX_type bX by (rule CEV_axiom_from_eq_sym)
  have s1:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg X) (App pp_negation_operator Y)"
    using nX_type appX_type appY_type bX_sym cong
    by (rule CEV_axiom_from_eq_trans)
  show ?thesis
    using nX_type appY_type nY_type s1 bY
    by (rule CEV_axiom_from_eq_trans)
qed

subsection \<open>Possibility excludes identity with falsity\<close>

lemma CEVs_possible_imp_neq_ObjFalse:
  assumes A_type: "\<Gamma> \<turnstile> A : Prop"
    and poss: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<diamond>\<^sub>o A"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq Prop A ObjFalse)"
proof -
  let ?E = "Eq Prop A ObjFalse"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using A_type typed_ObjFalse by (rule has_type.Eq)
  have nA_type: "\<Gamma> \<turnstile> Neg A : Prop"
    using A_type by (rule has_type.Neg)
  have nF_type: "\<Gamma> \<turnstile> Neg ObjFalse : Prop"
    using typed_ObjFalse by (rule has_type.Neg)
  have box_type: "\<Gamma> \<turnstile> \<box>\<^sub>o (Neg A) : Prop"
    using nA_type by (rule typed_ObjBox)
  have sub: "S \<subseteq> insert ?E S" by blast
  have d_E: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using E_type by (intro CEV_axiom_from.Assumption) simp
  have negs:
    "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg A) (Neg ObjFalse)"
    using A_type typed_ObjFalse d_E by (rule CEVs_eq_neg_cong)
  have nf_true:
    "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (Neg ObjFalse) ObjTrue"
  proof (rule CEV_axiom_from.Theorem)
    have "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ \<box>\<^sub>o (Neg ObjFalse)"
      using CEVp_not_ObjFalse by (rule CEV_axiom_necessitation)
    then show "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sup>+ Eq Prop (Neg ObjFalse) ObjTrue"
      unfolding ObjBox_def .
  qed
  have box_negA:
    "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s \<box>\<^sub>o (Neg A)"
    unfolding ObjBox_def
    using nA_type nF_type typed_ObjTrue negs nf_true
    by (rule CEV_axiom_from_eq_trans)
  have poss':
    "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (\<box>\<^sub>o (Neg A))"
    using poss sub
    unfolding ObjDiamond_def
    by (rule CEV_axiom_from_mono)
  have d_false:
    "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using box_negA poss' by (rule CEV_axiom_from_contradiction)
  have imp:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?E ObjFalse"
    using E_type d_false by (rule CEV_axiom_from_deduction)
  have to_neg:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (Imp ?E ObjFalse) (Neg ?E)"
    using CEV_proves_imp_false_to_neg[OF E_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis using imp to_neg by (rule CEV_axiom_from.MP)
qed

subsection \<open>Operator inequality from a separating witness\<close>

lemma CEVs_operator_neq_via_witness:
  assumes A_type: "\<Gamma> \<turnstile> A : pp_unary_ty"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and q_type: "\<Gamma> \<turnstile> q : Prop"
    and dA: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App A q"
    and dnB: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App B q)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty A B)"
proof -
  let ?E = "Eq pp_unary_ty A B"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using A_type B_type by (rule has_type.Eq)
  have Aq_type: "\<Gamma> \<turnstile> App A q : Prop"
    using A_type q_type unfolding pp_unary_ty_def by (rule has_type.App)
  have Bq_type: "\<Gamma> \<turnstile> App B q : Prop"
    using B_type q_type unfolding pp_unary_ty_def by (rule has_type.App)
  have sub: "S \<subseteq> insert ?E S" by blast
  have d_E: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using E_type by (intro CEV_axiom_from.Assumption) simp
  have cong:
    "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
      Eq Prop (App A q) (App B q)"
    using A_type B_type q_type d_E
    by (rule CEV_axiom_from_pp_apply_cong_left)
  have dA': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App A q"
    using dA sub by (rule CEV_axiom_from_mono)
  have dnB': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (App B q)"
    using dnB sub by (rule CEV_axiom_from_mono)
  have dB: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s App B q"
    using Aq_type Bq_type dA' cong by (rule CEV_axiom_from_eq_prop_elim)
  have d_false: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using dB dnB' by (rule CEV_axiom_from_contradiction)
  have imp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?E ObjFalse"
    using E_type d_false by (rule CEV_axiom_from_deduction)
  have to_neg:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (Imp ?E ObjFalse) (Neg ?E)"
    using CEV_proves_imp_false_to_neg[OF E_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis using imp to_neg by (rule CEV_axiom_from.MP)
qed

subsection \<open>Lifting an operator inequality to the outputs at a \<open>fun\<acute>\<close> input\<close>

lemma CEVs_fun_prime_separates:
  assumes p_type: "\<Gamma> \<turnstile> p : Prop"
    and A_type: "\<Gamma> \<turnstile> A : pp_unary_ty"
    and B_type: "\<Gamma> \<turnstile> B : pp_unary_ty"
    and pure_A: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty A"
    and pure_B: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty B"
    and neq_AB: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq pp_unary_ty A B)"
    and d_F: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s
    Neg (Eq Prop (App A p) (App B p))"
proof -
  let ?E = "Eq Prop (App A p) (App B p)"
  let ?AB = "Eq pp_unary_ty A B"
  have Ap_type: "\<Gamma> \<turnstile> App A p : Prop"
    using A_type p_type unfolding pp_unary_ty_def by (rule has_type.App)
  have Bp_type: "\<Gamma> \<turnstile> App B p : Prop"
    using B_type p_type unfolding pp_unary_ty_def by (rule has_type.App)
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using Ap_type Bp_type by (rule has_type.Eq)
  have sub: "S \<subseteq> insert ?E S" by blast
  have d_E: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using E_type by (intro CEV_axiom_from.Assumption) simp
  have d_F': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_fun_prime p"
    using d_F sub by (rule CEV_axiom_from_mono)
  have pA': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty A"
    using pure_A sub by (rule CEV_axiom_from_mono)
  have pB': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s pp_pure pp_unary_ty B"
    using pure_B sub by (rule CEV_axiom_from_mono)
  have nAB': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg ?AB"
    using neq_AB sub by (rule CEV_axiom_from_mono)
  have d_AB: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?AB"
    using p_type A_type B_type d_F' pA' pB' d_E
    by (rule CEV_axiom_from_fun_prime)
  have d_false: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using d_AB nAB' by (rule CEV_axiom_from_contradiction)
  have imp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?E ObjFalse"
    using E_type d_false by (rule CEV_axiom_from_deduction)
  have to_neg:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (Imp ?E ObjFalse) (Neg ?E)"
    using CEV_proves_imp_false_to_neg[OF E_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis using imp to_neg by (rule CEV_axiom_from.MP)
qed

subsection \<open>Transporting an inequality across identities\<close>

lemma CEVs_neq_transport:
  assumes X_type: "\<Gamma> \<turnstile> X : Prop"
    and Y_type: "\<Gamma> \<turnstile> Y : Prop"
    and X'_type: "\<Gamma> \<turnstile> X' : Prop"
    and Y'_type: "\<Gamma> \<turnstile> Y' : Prop"
    and eX: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop X X'"
    and eY: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop Y Y'"
    and neq: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq Prop X Y)"
  shows "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq Prop X' Y')"
proof -
  let ?E = "Eq Prop X' Y'"
  have E_type: "\<Gamma> \<turnstile> ?E : Prop"
    using X'_type Y'_type by (rule has_type.Eq)
  have sub: "S \<subseteq> insert ?E S" by blast
  have d_E: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ?E"
    using E_type by (intro CEV_axiom_from.Assumption) simp
  have eX': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop X X'"
    using eX sub by (rule CEV_axiom_from_mono)
  have eY': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop Y Y'"
    using eY sub by (rule CEV_axiom_from_mono)
  have neq': "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Neg (Eq Prop X Y)"
    using neq sub by (rule CEV_axiom_from_mono)
  have eY'sym: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop Y' Y"
    using Y_type Y'_type eY' by (rule CEV_axiom_from_eq_sym)
  have s1: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop X Y'"
    using X_type X'_type Y'_type eX' d_E
    by (rule CEV_axiom_from_eq_trans)
  have s2: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Eq Prop X Y"
    using X_type Y'_type Y_type s1 eY'sym
    by (rule CEV_axiom_from_eq_trans)
  have d_false: "\<Gamma> ; T ; insert ?E S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s ObjFalse"
    using s2 neq' by (rule CEV_axiom_from_contradiction)
  have imp: "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp ?E ObjFalse"
    using E_type d_false by (rule CEV_axiom_from_deduction)
  have to_neg:
    "\<Gamma> ; T ; S \<turnstile>\<^sub>CEV\<^sup>+\<^sub>s Imp (Imp ?E ObjFalse) (Neg ?E)"
    using CEV_proves_imp_false_to_neg[OF E_type]
    by (intro CEV_axiom_from.Theorem CEV_axiom_proves.Base)
  show ?thesis using imp to_neg by (rule CEV_axiom_from.MP)
qed

end

