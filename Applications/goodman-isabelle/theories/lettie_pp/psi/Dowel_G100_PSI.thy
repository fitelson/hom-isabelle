theory Dowel_G100_PSI
  imports PoP_SYN.PoP_G100_Syn
begin
text \<open>Purity of Pure: C_FP Refutes Psi_T
  Helm and the Purity of Pure team, a group of Claude Opus 5.5 sessions
  This companion theory holds a theorem of Rabbet's, by Rabbet's route; Dowel built it on the S companion, with Jacob, on 2026-11-08; not Branden
  Fitelson's. In the kernel's C_FP (cfp2's calculus), for every T of type u -> t, not Psi_T, where Psi_T says Pure(T), T(P_T), T(P'_T), the closure
  sB T, and that every Y T holds of is Pure. From Psi_T: sA T by LP at rc_P and rc_Pp, Application and Exhaustion_0 (psi_a); sC T by Fundamental
  Means Universal, u_fun_step (psi_c); EF from C_FP; then syn_S's instance at T gives falsity. T is Var 0 under one binder, bound by Gen at the end.\<close>
declare has_type.App[rule del]

section \<open>1. Psi_T and the claims used\<close>
definition sD :: "oterm \<Rightarrow> oterm" where "sD T = Forall rc_u (Imp (App (shift T) (Var 0)) (App rc_p (Var 0)))"
definition sPsi :: "oterm \<Rightarrow> oterm" where
  "sPsi T = Conj (pp_pure rc_c T) (Conj (App T (App rc_P T)) (Conj (App T (App rc_Pp T)) (Conj (sB T) (sD T))))"
definition psi_L :: "oterm list" where
  "psi_L = [pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_P, pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_Pp, pp_application_closure rc_c rc_u,
    pp_application_closure rc_u Prop, cfp_Exh [], pp_pure (rc_u \<rightarrow>\<^sub>o rc_u) k_C, pp_application_closure rc_u rc_u, cfp_Rec [Prop], k_EF]"

lemma sD_ty: assumes T: "\<Gamma> \<turnstile> T : rc_c" shows "\<Gamma> \<turnstile> sD T : Prop" proof -
  have T1: "rc_u # \<Gamma> \<turnstile> shift T : rc_c" by (rule weaken_shift_type_ok[OF T])
  have v: "rc_u # \<Gamma> \<turnstile> Var 0 : rc_u" by simp
  show ?thesis unfolding sD_def by (intro has_type.Forall has_type.Imp has_type.App[OF T1 v] rc_pure_ty[OF v])
qed
lemma sPsi_ty: assumes T: "\<Gamma> \<turnstile> T : rc_c" shows "\<Gamma> \<turnstile> sPsi T : Prop" proof -
  have a1: "\<Gamma> \<turnstile> App T (App rc_P T) : Prop" by (rule has_type.App[OF T has_type.App[OF rc_P_ty T]])
  have a2: "\<Gamma> \<turnstile> App T (App rc_Pp T) : Prop" by (rule has_type.App[OF T has_type.App[OF rc_Pp_ty T]])
  show ?thesis unfolding sPsi_def using typed_pp_pure[OF T] a1 a2 sABC_ty(2)[OF T] sD_ty[OF T] by blast
qed

section \<open>2. Item (a): Pure(T) and T(P_T) give box T(P_T), by LP, Application and Exhaustion_0\<close>
lemma psi_ac_ty: "\<Gamma> \<turnstile> pp_application_closure \<sigma> \<tau> : Prop"
  by (rule infer_type_sound) (simp add: pp_application_closure_def pp_pure_def pp_Pure_def lookup_def)
lemma psi_ex_ty: "\<Gamma> \<turnstile> pp_zeroary_exhaustion : Prop"
  by (rule infer_type_sound) (simp add: pp_zeroary_exhaustion_def pp_pure_def pp_Pure_def ObjBox_def ObjTrue_def lookup_def)
lemma psi_ur_ty: "\<Gamma> \<turnstile> pp_unary_recombination : Prop"
  by (rule infer_type_sound) (simp add: pp_unary_recombination_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)
lemma psi_a: assumes T: "\<Gamma> \<turnstile> T : rc_c"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_P) (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_Pp) (Conj (pp_application_closure rc_c rc_u)
    (Conj (pp_application_closure rc_u Prop) pp_zeroary_exhaustion)))) (Imp (sPsi T) (sA T))" (is "_ \<turnstile>\<^sub>U Imp ?H _") proof -
  have tP: "\<Gamma> \<turnstile> App rc_P T : rc_u" and tQ: "\<Gamma> \<turnstile> App rc_Pp T : rc_u" by (rule has_type.App[OF rc_P_ty T], rule has_type.App[OF rc_Pp_ty T])
  have t1: "\<Gamma> \<turnstile> App T (App rc_P T) : Prop" and t2: "\<Gamma> \<turnstile> App T (App rc_Pp T) : Prop" by (rule has_type.App[OF T tP], rule has_type.App[OF T tQ])
  note a1 = u_rc_ac[OF rc_P_ty T] and b1 = u_rc_ac[OF rc_Pp_ty T] and a2 = u_rc_ac[OF T tP] and b2 = u_rc_ac[OF T tQ]
  have tH: "\<Gamma> \<turnstile> ?H : Prop" using typed_pp_pure[OF rc_P_ty] typed_pp_pure[OF rc_Pp_ty] psi_ac_ty psi_ex_ty by blast
  have d1: "\<Gamma> \<turnstile>\<^sub>U Imp ?H (Imp (sPsi T) (\<box>\<^sub>o (App T (App rc_P T))))" by (rule u_rc_pc3[OF a1 a2 u_zI[OF t1]])
    (insert tH sPsi_ty[OF T] typed_ObjBox[OF t1], (unfold zI_def sPsi_def prop_eval.simps)?, blast+)
  have d2: "\<Gamma> \<turnstile>\<^sub>U Imp ?H (Imp (sPsi T) (\<box>\<^sub>o (App T (App rc_Pp T))))" by (rule u_rc_pc3[OF b1 b2 u_zI[OF t2]])
    (insert tH sPsi_ty[OF T] typed_ObjBox[OF t2], (unfold zI_def sPsi_def prop_eval.simps)?, blast+)
  show ?thesis by (rule u_rc_pc2[OF d1 d2]) (insert tH sPsi_ty[OF T] sABC_ty(1)[OF T], (unfold sA_def prop_eval.simps)?, blast+)
qed

section \<open>3. Item (c): every Y that T holds of is Pure, so each such Y satisfies Fun-WP, by Fundamental Means Universal\<close>
lemmas psi_sh = shift_def pp_fun_def pp_Fun_def rcH5_def k_C_def pp_application_closure_def pp_unary_recombination_def pp_pure_def
  pp_Pure_def ObjBox_def ObjTrue_def eval_nat_numeral
lemma psi_c: "[rc_c] \<turnstile>\<^sub>U Imp rcH5 (Imp (sD (Var 0)) (sC (Var 0)))" proof -
  let ?G0 = "[rc_c]" let ?G1 = "[rc_u, rc_c]" let ?G2 = "[Prop, rc_u, rc_c]" let ?G3 = "[Prop, Prop, rc_u, rc_c]"
  have v0: "?G0 \<turnstile> Var 0 : rc_c" and Y1: "?G1 \<turnstile> Var 0 : rc_u" and T1: "?G1 \<turnstile> Var 1 : rc_c" by simp_all
  have z2: "?G2 \<turnstile> Var 0 : Prop" and Y2: "?G2 \<turnstile> Var 1 : rc_u" by simp_all
  have z3: "?G3 \<turnstile> Var 1 : Prop" and x3: "?G3 \<turnstile> Var 0 : Prop" and Y3: "?G3 \<turnstile> Var 2 : rc_u" by (simp_all add: eval_nat_numeral lookup_def)
  have tYx3: "?G3 \<turnstile> App (Var 2) (Var 0) : Prop" and tYz3: "?G3 \<turnstile> App (Var 2) (Var 1) : Prop" by (rule has_type.App[OF Y3 x3], rule has_type.App[OF Y3 z3])
  have tYz2: "?G2 \<turnstile> App (Var 1) (Var 0) : Prop" and tTY1: "?G1 \<turnstile> App (Var 1) (Var 0) : Prop" by (rule has_type.App[OF Y2 z2], rule has_type.App[OF T1 Y1])
  note st = u_fun_step[OF z3 x3 Y3]
  let ?Q2 = "Imp rcH5 (Imp (App rc_p (Var 1)) (Imp (pp_fun Prop (Var 0)) (Neg (\<box>\<^sub>o (Neg (App (Var 1) (Var 0)))))))"
  have shQ2: "shift ?Q2 = Imp rcH5 (Imp (App rc_p (Var 2)) (Imp (pp_fun Prop (Var 1)) (Neg (\<box>\<^sub>o (Neg (App (Var 2) (Var 1)))))))" by (simp add: psi_sh)
  have tQ2: "?G2 \<turnstile> ?Q2 : Prop" using rcH5_ty rc_pure_ty[OF Y2] typed_pp_fun[OF z2] typed_ObjBox[OF has_type.Neg[OF tYz2]] by blast
  have s3: "?G3 \<turnstile>\<^sub>U Imp (App (Var 2) (Var 0)) (shift ?Q2)" unfolding shQ2 by (rule u_rc_pc1[OF st])
    (insert tYx3 rcH5_ty[of ?G3] rc_pure_ty[OF Y3] typed_pp_fun[OF z3] typed_ObjBox[OF has_type.Neg[OF tYz3]], (unfold prop_eval.simps)?, blast+)
  have i2: "?G2 \<turnstile>\<^sub>U Imp (Exists Prop (App (Var 2) (Var 0))) ?Q2" by (rule U_proves.Inst[OF tYx3 tQ2 s3])
  let ?P1 = "Conj rcH5 (Conj (App rc_p (Var 0)) (Exists Prop (App (Var 1) (Var 0))))"
  let ?Q1 = "Imp (pp_fun Prop (Var 0)) (Neg (\<box>\<^sub>o (Neg (App (Var 1) (Var 0)))))"
  have shP1: "shift ?P1 = Conj rcH5 (Conj (App rc_p (Var 1)) (Exists Prop (App (Var 2) (Var 0))))" by (simp add: psi_sh)
  have tE2: "?G2 \<turnstile> Exists Prop (App (Var 2) (Var 0)) : Prop" by (rule has_type.Exists[OF tYx3])
  have tE1: "?G1 \<turnstile> Exists Prop (App (Var 1) (Var 0)) : Prop" by (rule has_type.Exists[OF tYz2])
  have tQ1: "?G2 \<turnstile> ?Q1 : Prop" using typed_pp_fun[OF z2] typed_ObjBox[OF has_type.Neg[OF tYz2]] by blast
  have s2: "?G2 \<turnstile>\<^sub>U Imp (shift ?P1) ?Q1" unfolding shP1 by (rule u_rc_pc1[OF i2])
    (insert tE2 tQ1 rcH5_ty[of ?G2] rc_pure_ty[OF Y2], (unfold prop_eval.simps)?, blast+)
  have tP1: "?G1 \<turnstile> ?P1 : Prop" using rcH5_ty rc_pure_ty[OF Y1] tE1 by blast
  have g1: "?G1 \<turnstile>\<^sub>U Imp ?P1 (Forall Prop ?Q1)" by (rule U_proves.Gen[OF tP1 tQ1 s2])
  let ?B = "Imp (App (Var 2) (Var 0)) (App rc_p (Var 0))"
  have shD: "shift (sD (Var 0)) = Forall rc_u ?B" by (simp add: sD_def psi_sh)
  have tB: "rc_u # ?G1 \<turnstile> ?B : Prop" proof -
    have a: "rc_u # ?G1 \<turnstile> Var 2 : rc_c" and b: "rc_u # ?G1 \<turnstile> Var 0 : rc_u" by (simp_all add: eval_nat_numeral lookup_def)
    show ?thesis by (intro has_type.Imp has_type.App[OF a b] rc_pure_ty[OF b])
  qed
  have esub: "subst0 (Var 0) ?B = Imp (App (Var 1) (Var 0)) (App rc_p (Var 0))" by (simp add: subst0_def eval_nat_numeral)
  have ui: "?G1 \<turnstile>\<^sub>U Imp (Forall rc_u ?B) (Imp (App (Var 1) (Var 0)) (App rc_p (Var 0)))" unfolding esub[symmetric] using tB Y1
    by (intro U_proves.H H_proves.UI)
  let ?BB = "Imp (App (Var 1) (Var 0)) (Imp (Exists Prop (App (Var 1) (Var 0))) (Forall Prop ?Q1))"
  have eC: "sC (Var 0) = Forall rc_u ?BB" by (simp add: sC_def shift_def)
  have shP0: "shift (Conj rcH5 (sD (Var 0))) = Conj rcH5 (Forall rc_u ?B)" by (simp only: rc_sft rcH5_shift shD)
  have tF1: "?G1 \<turnstile> Forall Prop ?Q1 : Prop" by (rule has_type.Forall[OF tQ1])
  have tB0: "?G1 \<turnstile> ?BB : Prop" using tTY1 tE1 tF1 by blast
  have s1: "?G1 \<turnstile>\<^sub>U Imp (shift (Conj rcH5 (sD (Var 0)))) ?BB" unfolding shP0 by (rule u_rc_pc2[OF ui g1])
    (insert rcH5_ty[of ?G1] has_type.Forall[OF tB] tB0 rc_pure_ty[OF Y1] tE1 tF1 tTY1, (unfold prop_eval.simps)?, blast+)
  have tP0: "?G0 \<turnstile> Conj rcH5 (sD (Var 0)) : Prop" using rcH5_ty sD_ty[OF v0] by blast
  have g0: "?G0 \<turnstile>\<^sub>U Imp (Conj rcH5 (sD (Var 0))) (Forall rc_u ?BB)" by (rule U_proves.Gen[OF tP0 tB0 s1])
  show ?thesis by (rule u_rc_pc1[OF g0[folded eC]]) (insert rcH5_ty[of ?G0] sD_ty[OF v0] sABC_ty(3)[OF v0], (unfold prop_eval.simps)?, blast+)
qed

section \<open>4. The theorem: C_FP proves, for every T, not Psi_T\<close>
lemma psi_L_shift: "shift (cfp_and psi_L) = cfp_and psi_L" proof -
  have p: "shift (pp_Pure \<sigma>) = pp_Pure \<sigma>" for \<sigma> by (simp add: pp_Pure_def shift_def)
  have ac: "shift (pp_application_closure \<sigma> \<tau>) = pp_application_closure \<sigma> \<tau>" for \<sigma> \<tau> by (simp add: pp_application_closure_def pp_pure_def pp_Pure_def shift_def)
  have ex: "shift pp_zeroary_exhaustion = pp_zeroary_exhaustion" by (simp add: pp_zeroary_exhaustion_def pp_pure_def pp_Pure_def shift_def ObjBox_def ObjTrue_def)
  have ur: "shift pp_unary_recombination = pp_unary_recombination"
    by (simp add: pp_unary_recombination_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def shift_def ObjBox_def ObjTrue_def eval_nat_numeral)
  have ef: "shift k_EF = k_EF" by (simp add: k_EF_def pp_fun_def pp_Fun_def shift_def)
  have kc: "shift k_C = k_C" by (simp add: k_C_def shift_def)
  show ?thesis by (simp add: psi_L_def cfp_lit rc_sft pp_pure_def p ac ex ur ef kc)
qed
lemma psi_L_ty: "\<Gamma> \<turnstile> cfp_and psi_L : Prop" unfolding psi_L_def cfp_lit
  by (rule cfp_and_ty) (auto intro: typed_pp_pure rc_P_ty rc_Pp_ty k_C_ty psi_ac_ty psi_ex_ty
    psi_ur_ty s_EF_ty)
theorem syn_Psi_thm: "[] \<turnstile>\<^sub>CEV Imp (cfp_and psi_L) (Forall rc_c (Neg (sPsi (Var 0))))" proof -
  have v0: "[rc_c] \<turnstile> Var 0 : rc_c" by simp
  have tN: "[rc_c] \<turnstile> Neg (sPsi (Var 0)) : Prop" using sPsi_ty[OF v0] by blast
  have core: "[rc_c] \<turnstile>\<^sub>CEV Imp (cfp_and psi_L) (Neg (sPsi (Var 0)))"
    by (rule rc_pc3[OF U_sub_CEV[OF psi_a[OF v0]] U_sub_CEV[OF psi_c] syn_S_term[OF v0]])
      (insert psi_L_ty[of "[rc_c]"] tN, (unfold psi_L_def cfp_lit cfp_and.simps rcH5_def sPsi_def sPhi_def prop_eval.simps)?, blast+)
  show ?thesis by (rule CEV_proves.Gen[OF psi_L_ty tN]) (unfold psi_L_shift, rule core)
qed
theorem syn_Psi: "[] ; pp_CFP_axioms \<turnstile>\<^sub>CEV\<^sub>s Forall rc_c (Neg (sPsi (Var 0)))" proof -
  have sub: "set psi_L \<subseteq> pp_CFP_axioms" unfolding psi_L_def
    using cfp_LP[OF rc_P_ty rc_consts(4)] cfp_LP[OF rc_Pp_ty rc_consts(5)] cfp_LP[OF k_C_ty k_C_consts] cfp_AC cfp_mem by simp
  have "[] ; pp_CFP_axioms \<turnstile>\<^sub>CEV\<^sub>s cfp_and psi_L" by (rule cfp_and_local) (use sub pp_CFP_closed in blast)
  then show ?thesis by (rule CEV_set_derivable.Derive_MP[OF _ CEV_set_derivable.Theorem[OF syn_Psi_thm]])
qed

end
