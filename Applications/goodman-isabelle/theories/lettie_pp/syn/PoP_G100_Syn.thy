theory PoP_G100_Syn
  imports PoP_Main.PoP_G100_Kernel
begin

text \<open>Purity of Pure: The Theorem S
  Helm and the Purity of Pure team, a group of Claude Opus 5.5 sessions
  This companion theory holds S, the supplementary note's section 5, in the kernel; Loupe built it on the main theory, with Jacob, on 2026-11-08; none of
  this text is Branden Fitelson's. C proves, for every T of type u -> t, not Phi_T, where Phi_T says (a) T holds necessarily of P_T and P'_T, (b)
  T is closed under Y |-> lambda z. Y(Q_T(z)), (c) each Y that T holds of satisfies Fun-WP, and (d) EF. The proof is the main note's with T for
  pi, by Rabbet's route. It is done once at the bare constant pi in U, for every context, so every beta-step is at a closed constant; then Var 0
  is put for pi by the library's CEV_proves_subst_const and bound by Gen. T is a bound variable in syn_S, so no step uses that T is logical, and
  the statement has no premise about Pure (s_no_Pure). s_stepU, s_coreU, s_uni_ctx, s_EG and s_ExUni are the kept lemmas u_rc_stepU, u_rc_coreU,
  u_uni_ctx, u_EG and u_fun_ExUni, by Dowel and Loupe, with (b) for rcHU, (c) for rcH5, and every context for the empty one.\<close>

declare has_type.App[rule del]

section \<open>1. The four items of Phi_T\<close>

text \<open>T has the type of pi = Pure_u, rc_c = (Prop -> Prop) -> Prop. Under a binder T is written shift T. (a) T holds necessarily of
  P_T and P'_T, the main note's P and P' built with T (the Terms theory's closed combinators rc_P, rc_Pp applied to T). (b) T is
  closed under Y |-> rc_W T Y, which is lambda z. Y(Q_T(z)) up to beta. (c) each Y that T holds of satisfies Fun-WP:
  if some x has Y, each fundamental z possibly has Y. (d) EF.\<close>

definition sA :: "oterm \<Rightarrow> oterm" where "sA T = Conj (\<box>\<^sub>o (App T (App rc_P T))) (\<box>\<^sub>o (App T (App rc_Pp T)))"

definition sB :: "oterm \<Rightarrow> oterm" where
  "sB T = Forall rc_u (Imp (App (shift T) (Var 0)) (App (shift T) (App (App rc_W (shift T)) (Var 0))))"

definition sC :: "oterm \<Rightarrow> oterm" where
  "sC T = Forall rc_u (Imp (App (shift T) (Var 0)) (Imp (Exists Prop (App (Var 1) (Var 0)))
    (Forall Prop (Imp (pp_fun Prop (Var 0)) (Neg (\<box>\<^sub>o (Neg (App (Var 1) (Var 0)))))))))"

definition sPhi :: "oterm \<Rightarrow> oterm" where "sPhi T = Conj (sA T) (Conj (sB T) (Conj (sC T) k_EF))"

lemma sABC_ty: assumes T: "\<Gamma> \<turnstile> T : rc_c"
  shows "\<Gamma> \<turnstile> sA T : Prop" and "\<Gamma> \<turnstile> sB T : Prop" and "\<Gamma> \<turnstile> sC T : Prop"
proof -
  have T1: "rc_u # \<Gamma> \<turnstile> shift T : rc_c" by (rule weaken_shift_type_ok[OF T])
  have v: "rc_u # \<Gamma> \<turnstile> Var 0 : rc_u" by simp
  have v1: "Prop # rc_u # \<Gamma> \<turnstile> Var 1 : rc_u" and v0: "Prop # rc_u # \<Gamma> \<turnstile> Var 0 : Prop" by simp_all
  have a1: "\<Gamma> \<turnstile> App T (App rc_P T) : Prop" by (rule has_type.App[OF T has_type.App[OF rc_P_ty T]])
  have a2: "\<Gamma> \<turnstile> App T (App rc_Pp T) : Prop" by (rule has_type.App[OF T has_type.App[OF rc_Pp_ty T]])
  have b1: "rc_u # \<Gamma> \<turnstile> App (shift T) (Var 0) : Prop" by (rule has_type.App[OF T1 v])
  have b2: "rc_u # \<Gamma> \<turnstile> App (shift T) (App (App rc_W (shift T)) (Var 0)) : Prop"
    by (rule has_type.App[OF T1 has_type.App[OF has_type.App[OF rc_W_ty T1] v]])
  have c1: "Prop # rc_u # \<Gamma> \<turnstile> App (Var 1) (Var 0) : Prop" by (rule has_type.App[OF v1 v0])
  have c2: "Prop # rc_u # \<Gamma> \<turnstile> pp_fun Prop (Var 0) : Prop" by (rule typed_pp_fun[OF v0])
  show "\<Gamma> \<turnstile> sA T : Prop" unfolding sA_def using typed_ObjBox[OF a1] typed_ObjBox[OF a2] by blast
  show "\<Gamma> \<turnstile> sB T : Prop" unfolding sB_def using b1 b2 by blast
  show "\<Gamma> \<turnstile> sC T : Prop" unfolding sC_def using b1 c1 c2 typed_ObjBox[OF has_type.Neg[OF c1]] by blast
qed

lemma s_EF_ty: "\<Gamma> \<turnstile> k_EF : Prop" unfolding k_EF_def by (rule has_type.Exists, rule typed_pp_fun) simp

lemma sPhi_ty: assumes T: "\<Gamma> \<turnstile> T : rc_c" shows "\<Gamma> \<turnstile> sPhi T : Prop"
  unfolding sPhi_def using sABC_ty[OF T] s_EF_ty by blast

section \<open>2. At pi: closedness and typing\<close>

lemma s_rename_W[simp]: "rename \<rho> rc_W = rc_W"
  by (simp add: rc_W_def rc_Q_def rc_F_def rc_R_def ObjBox_def ObjTrue_def eval_nat_numeral)

lemma s_subst_W[simp]: "subst s rc_W = rc_W"
  by (simp add: rc_W_def rc_Q_def rc_F_def rc_R_def ObjBox_def ObjTrue_def eval_nat_numeral)

lemma sB_pi_shift[simp]: "shift (sB rc_p) = sB rc_p" by (simp add: sB_def shift_def)

lemma sC_pi_shift[simp]: "shift (sC rc_p) = sC rc_p"
  by (simp add: sC_def shift_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def eval_nat_numeral)

lemma sB_pi_ty: "\<Gamma> \<turnstile> sB rc_p : Prop" by (rule sABC_ty(2)[OF rc_p_ty])

lemma sC_pi_ty: "\<Gamma> \<turnstile> sC rc_p : Prop" by (rule sABC_ty(3)[OF rc_p_ty])

lemma sA_pi: "sA rc_p = Conj rcBP rcBQ" by (simp add: sA_def rcP_def rcPp_def)

section \<open>3. The substitution of T for pi\<close>

lemma s_subst: "subst_const pp_pure_name rc_c N (sPhi rc_p) = sPhi N"
  by (simp add: sPhi_def sA_def sB_def sC_def k_EF_def pp_Pure_def pp_fun_def pp_Fun_def pp_fun_name_def pp_pure_name_def
    ObjBox_def ObjTrue_def shift_def rc_consts rc_W_consts)

lemma s_no_Pure: "pp_pure_name \<notin> consts_of (Forall rc_c (Neg (sPhi (Var 0))))"
  by (simp add: sPhi_def sA_def sB_def sC_def k_EF_def pp_fun_def pp_Fun_def pp_fun_name_def pp_pure_name_def
    ObjBox_def ObjTrue_def shift_def rc_consts rc_W_consts)

text \<open>Context checks, in the forms the proofs below use: a symbolic tail.\<close>
lemma s_ctx_1: "rc_u # Prop # \<Gamma> \<turnstile> Var 1 : Prop" by simp
lemma s_ctx_2: "Prop # rc_u # \<Gamma> \<turnstile> Var 1 : rc_u" by simp
lemma s_ctx_3: "rc_u # Prop # Prop # \<Gamma> \<turnstile> Var 2 : Prop" by (simp_all add: eval_nat_numeral lookup_def)

section \<open>4. The instance at pi, in U, for every context\<close>

text \<open>Item (b) at Y: the closure that rcHU gave by LP at rc_W, PP_u and Application, here a hypothesis.\<close>
lemma s_B_inst: assumes Y: "\<Gamma> \<turnstile> Y : rc_u" shows "\<Gamma> \<turnstile>\<^sub>U Imp (sB rc_p) (Imp (App rc_p Y) (App rc_p (rcW Y)))"
proof -
  let ?A = "Imp (App rc_p (Var 0)) (App rc_p (App (App rc_W rc_p) (Var 0)))"
  have d: "sB rc_p = Forall rc_u ?A" by (simp add: sB_def)
  have v: "rc_u # \<Gamma> \<turnstile> Var 0 : rc_u" by simp
  have tA: "rc_u # \<Gamma> \<turnstile> ?A : Prop" using rc_pure_ty[OF v] rc_pure_ty[OF rcW_ty[OF v]] unfolding rcW_def by (rule has_type.Imp)
  have e: "subst0 Y ?A = Imp (App rc_p Y) (App rc_p (rcW Y))" by (simp add: subst0_def rcW_def)
  show ?thesis unfolding d e[symmetric] using tA Y by (intro U_proves.H H_proves.UI)
qed

text \<open>Item (c) at Y: Fun-WP at Y itself. If Y(y), then something has Y, so
  each fundamental r possibly has Y. No Recombination, LP or Application.\<close>
lemma s_fun_step: assumes r: "\<Gamma> \<turnstile> r : Prop" and y: "\<Gamma> \<turnstile> y : Prop" and Y: "\<Gamma> \<turnstile> Y : rc_u"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (sC rc_p) (Imp (pp_fun Prop r) (Imp (App rc_p Y) (Imp (App Y y) (Neg (\<box>\<^sub>o (Neg (App Y r)))))))"
proof -
  let ?B = "\<lambda>Z. Forall Prop (Imp (pp_fun Prop (Var 0)) (Neg (\<box>\<^sub>o (Neg (App Z (Var 0))))))"
  let ?A = "Imp (App rc_p (Var 0)) (Imp (Exists Prop (App (Var 1) (Var 0))) (?B (Var 1)))"
  let ?X = "Exists Prop (App (shift Y) (Var 0))"
  let ?B0 = "Imp (pp_fun Prop (Var 0)) (Neg (\<box>\<^sub>o (Neg (App (shift Y) (Var 0)))))"
  have d: "sC rc_p = Forall rc_u ?A" by (simp add: sC_def)
  have v: "rc_u # \<Gamma> \<turnstile> Var 0 : rc_u" by simp
  have v1: "Prop # rc_u # \<Gamma> \<turnstile> Var 1 : rc_u" and v0: "Prop # rc_u # \<Gamma> \<turnstile> Var 0 : Prop" by simp_all
  have c1: "Prop # rc_u # \<Gamma> \<turnstile> App (Var 1) (Var 0) : Prop" by (rule has_type.App[OF v1 v0])
  have c2: "Prop # rc_u # \<Gamma> \<turnstile> pp_fun Prop (Var 0) : Prop" by (rule typed_pp_fun[OF v0])
  have tA: "rc_u # \<Gamma> \<turnstile> ?A : Prop" using rc_pure_ty[OF v] c1 c2 typed_ObjBox[OF has_type.Neg[OF c1]] by blast
  have e1: "subst0 Y ?A = Imp (App rc_p Y) (Imp ?X (Forall Prop ?B0))" by (simp add: subst0_def pp_fun_def pp_Fun_def flip: shift_def)
  have ui1: "\<Gamma> \<turnstile>\<^sub>U Imp (sC rc_p) (Imp (App rc_p Y) (Imp ?X (Forall Prop ?B0)))"
    unfolding d e1[symmetric] using tA Y by (intro U_proves.H H_proves.UI)
  have Y1: "Prop # \<Gamma> \<turnstile> shift Y : rc_u" by (rule weaken_shift_type_ok[OF Y])
  have w0: "Prop # \<Gamma> \<turnstile> Var 0 : Prop" by simp
  have tYx: "Prop # \<Gamma> \<turnstile> App (shift Y) (Var 0) : Prop" by (rule has_type.App[OF Y1 w0])
  have e2: "subst0 y (App (shift Y) (Var 0)) = App Y y" by (simp add: subst0_def)
  have eg: "\<Gamma> \<turnstile>\<^sub>U Imp (App Y y) ?X" unfolding e2[symmetric] using tYx y by (intro U_proves.H H_proves.EG)
  have tB0: "Prop # \<Gamma> \<turnstile> ?B0 : Prop" using typed_pp_fun[OF w0] typed_ObjBox[OF has_type.Neg[OF tYx]] by blast
  have e3: "subst0 r ?B0 = Imp (pp_fun Prop r) (Neg (\<box>\<^sub>o (Neg (App Y r))))" by (simp add: subst0_def pp_fun_def pp_Fun_def)
  have ui2: "\<Gamma> \<turnstile>\<^sub>U Imp (Forall Prop ?B0) (Imp (pp_fun Prop r) (Neg (\<box>\<^sub>o (Neg (App Y r)))))"
    unfolding e3[symmetric] using tB0 r by (intro U_proves.H H_proves.UI)
  have tYy: "\<Gamma> \<turnstile> App Y y : Prop" and tYr: "\<Gamma> \<turnstile> App Y r : Prop" by (rule has_type.App[OF Y y], rule has_type.App[OF Y r])
  have tG: "\<Gamma> \<turnstile> Imp (sC rc_p) (Imp (pp_fun Prop r) (Imp (App rc_p Y) (Imp (App Y y) (Neg (\<box>\<^sub>o (Neg (App Y r))))))) : Prop"
    using sC_pi_ty[of \<Gamma>] typed_pp_fun[OF r] rc_pure_ty[OF Y] tYy typed_ObjBox[OF has_type.Neg[OF tYr]] by blast
  show ?thesis by (rule u_rc_pc3[OF ui1 eg ui2 tG]) (unfold prop_eval.simps, blast)
qed

lemma s_stepU: assumes r: "\<Gamma> \<turnstile> r : Prop" and Y: "\<Gamma> \<turnstile> Y : rc_u" shows "\<Gamma> \<turnstile>\<^sub>U Imp (sB rc_p) (Imp (rcUni r) (Imp (rcF (rcQ r)) (Imp (App rc_p Y) (Imp (App Y (Neg (rcQ r))) (Neg (\<box>\<^sub>o (Neg (App Y (rcQ r)))))))))" proof -
  let ?e = "rcQ r" let ?n = "Neg (rcQ r)" let ?W = "rcW Y"
  have te: "\<Gamma> \<turnstile> ?e : Prop" by (rule rcQ_ty[OF r])
  have tn: "\<Gamma> \<turnstile> ?n : Prop" using te by blast
  have tW: "\<Gamma> \<turnstile> ?W : rc_u" by (rule rcW_ty[OF Y])
  have tQn: "\<Gamma> \<turnstile> rcQ ?n : Prop" by (rule rcQ_ty[OF tn])
  note w1 = u_rcW_iff[OF Y r] and w2 = u_rcW_iff[OF Y tn]
  have tYe: "\<Gamma> \<turnstile> App Y ?e : Prop" and tYn: "\<Gamma> \<turnstile> App Y ?n : Prop" and tYQ: "\<Gamma> \<turnstile> App Y (rcQ ?n) : Prop" by (rule has_type.App[OF Y te], rule has_type.App[OF Y tn], rule has_type.App[OF Y tQn])
  have tWr: "\<Gamma> \<turnstile> App ?W r : Prop" and tWn: "\<Gamma> \<turnstile> App ?W ?n : Prop" by (rule has_type.App[OF tW r], rule has_type.App[OF tW tn])
  have k0: "\<Gamma> \<turnstile>\<^sub>U Imp (Neg (App Y ?e)) (Neg (App ?W r))" by (rule u_rc_pc1[OF w1]) (insert tYe tWr, (unfold prop_eval.simps)?, blast+)
  note k = u_rc_K[OF k0]
  have s1: "\<Gamma> \<turnstile>\<^sub>U Imp (rcF ?e) (Imp (App Y ?n) (App Y (rcQ ?n)))" by (rule u_rc_pc4[OF u_rc1b[OF tn] u_rc1c[OF te] U_eq_sym[OF tQn tn] u_rc_LL[OF tn tQn Y]]) (insert rcF_ty[OF te] tYn tYQ, (unfold prop_eval.simps)?, blast+)
  have t1: "\<Gamma> \<turnstile>\<^sub>U Imp (rcF ?e) (Imp (App Y ?n) (App ?W ?n))" by (rule u_rc_pc2[OF s1 w2]) (insert rcF_ty[OF te] tYn tWn, (unfold prop_eval.simps)?, blast+)
  have tH: "\<Gamma> \<turnstile> sB rc_p : Prop" by (rule sB_pi_ty)
  have s3: "\<Gamma> \<turnstile>\<^sub>U Imp (sB rc_p) (Imp (App rc_p Y) (App rc_p ?W))" by (rule s_B_inst[OF Y])
  have tU: "\<Gamma> \<turnstile> rcUni r : Prop" by (rule rcUni_ty[OF r])
  have tGoal: "\<Gamma> \<turnstile> Imp (sB rc_p) (Imp (rcUni r) (Imp (rcF ?e) (Imp (App rc_p Y) (Imp (App Y ?n) (Neg (\<box>\<^sub>o (Neg (App Y ?e)))))))) : Prop" using tH tU rcF_ty[OF te] rc_pure_ty[OF Y] tYn typed_ObjBox[OF has_type.Neg[OF tYe]] by blast
  show ?thesis by (rule u_rc_pc5[OF s3 u_rcUni_inst[OF r tn] u_rcR_elim[OF r tn tW] t1 k tGoal]) (unfold prop_eval.simps, blast) qed

lemma s_coreU: "\<Gamma> \<turnstile>\<^sub>U Imp (sB rc_p) (Imp rcBP (Imp rcBQ (Neg rcExUni)))" proof -
  let ?G = "Prop # \<Gamma>" let ?G1 = "rc_u # Prop # \<Gamma>" let ?r = "Var 0"
  have r: "?G \<turnstile> ?r : Prop" by simp
  have r1: "?G1 \<turnstile> Var 1 : Prop" by simp
  have y1: "?G1 \<turnstile> Var 0 : rc_u" by simp
  let ?e = "rcQ ?r" let ?n = "Neg (rcQ ?r)" let ?P = "Conj (sB rc_p) (Conj (rcUni ?r) (rcF ?e))"
  have te: "?G \<turnstile> ?e : Prop" by (rule rcQ_ty[OF r])
  have tn: "?G \<turnstile> ?n : Prop" using te by blast
  have tf: "?G \<turnstile> rcUni ?r : Prop" by (rule rcUni_ty[OF r])
  have tP: "?G \<turnstile> ?P : Prop" using sB_pi_ty[of ?G] rcF_ty[OF te] tf by blast
  have sh: "shift ?P = Conj (sB rc_p) (Conj (rcUni (Var 1)) (rcF (rcQ (Var 1))))" by (simp add: rc_sft rcUni_shift)
  have sh2: "shift ?n = Neg (rcQ (Var 1))" and sh3: "shift ?e = rcQ (Var 1)" by (simp_all add: rc_sft)
  note st = s_stepU[OF r1 y1]
  have s: "?G1 \<turnstile>\<^sub>U Imp (shift ?P) (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift ?n)) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (shift ?e)))))))" unfolding sh sh2 sh3 proof (rule u_rc_pc1[OF st]) show "?G1 \<turnstile> Imp (Conj (sB rc_p) (Conj (rcUni (Var 1)) (rcF (rcQ (Var 1))))) (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (Neg (rcQ (Var 1)))) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (rcQ (Var 1)))))))) : Prop" using U_formula[OF st] sB_pi_ty[of ?G1] rcUni_ty[OF r1] rcF_ty[OF rcQ_ty[OF r1]] by (auto elim!: has_type.cases[of _ "Imp _ _"]) qed (unfold prop_eval.simps, blast)
  note ri = u_rcR_intro[OF te tn tP s]
  note u = u_rcF_iff[OF te] and T = U_modal_T[OF rcB_ty[OF te], unfolded modal_T_def]
  have c: "?G \<turnstile>\<^sub>U Imp (sB rc_p) (Imp rcBP (Imp rcBQ (Neg (rcUni ?r))))" by (rule u_rc_pc4[OF ri u T u_rc2[OF r]]) (insert sB_pi_ty[of ?G] rcBP_ty[of ?G] rcBQ_ty[of ?G] tf, (unfold prop_eval.simps)?, blast+)
  let ?Q = "Neg (Conj (sB rc_p) (Conj rcBP rcBQ))"
  have tQ: "\<Delta> \<turnstile> ?Q : Prop" for \<Delta> using sB_pi_ty[of \<Delta>] rcBP_ty[of \<Delta>] rcBQ_ty[of \<Delta>] by blast
  have shq: "shift ?Q = ?Q" by (simp add: rc_sft rcP_def rcPp_def)
  have i: "?G \<turnstile>\<^sub>U Imp (rcUni ?r) (shift ?Q)" unfolding shq by (rule u_rc_pc1[OF c]) (insert tf tQ[of ?G], (unfold prop_eval.simps)?, blast+)
  note inst = U_proves.Inst[OF tf tQ i]
  have tE: "\<Gamma> \<turnstile> rcExUni : Prop" unfolding rcExUni_def by (rule has_type.Exists[OF tf])
  show ?thesis by (rule u_rc_pc1[OF inst[folded rcExUni_def]]) (insert tE rcBP_ty[of \<Gamma>] rcBQ_ty[of \<Gamma>] sB_pi_ty[of \<Gamma>], (unfold prop_eval.simps)?, blast+) qed

lemma s_uni_ctx: "Prop # \<Gamma> \<turnstile>\<^sub>U Imp (sC rc_p) (Imp (pp_fun Prop (Var 0)) (rcUni (Var 0)))" proof -
  let ?G0 = "Prop # \<Gamma>" let ?G1 = "Prop # Prop # \<Gamma>" let ?G2 = "rc_u # Prop # Prop # \<Gamma>"
  let ?P0 = "Conj (sC rc_p) (pp_fun Prop (Var 0))" let ?P1 = "Conj (sC rc_p) (pp_fun Prop (Var 1))"
  have r0: "?G0 \<turnstile> Var 0 : Prop" by simp
  have r1: "?G1 \<turnstile> Var 1 : Prop" and y1: "?G1 \<turnstile> Var 0 : Prop" by simp_all
  have r2: "?G2 \<turnstile> Var 2 : Prop" and y2: "?G2 \<turnstile> Var 1 : Prop" and Y2: "?G2 \<turnstile> Var 0 : rc_u" by (simp_all add: eval_nat_numeral lookup_def)
  have tF0: "?G0 \<turnstile> pp_fun Prop (Var 0) : Prop" by (rule typed_pp_fun[OF r0])
  have tF1: "?G1 \<turnstile> pp_fun Prop (Var 1) : Prop" by (rule typed_pp_fun[OF r1])
  have tF2: "?G2 \<turnstile> pp_fun Prop (Var 2) : Prop" by (rule typed_pp_fun[OF r2])
  have tP0: "?G0 \<turnstile> ?P0 : Prop" using sC_pi_ty[of ?G0] tF0 by blast
  have tP1: "?G1 \<turnstile> ?P1 : Prop" using sC_pi_ty[of ?G1] tF1 by blast
  have sh0: "shift ?P0 = ?P1" by (simp add: rc_sft k_fun_shift)
  have sh1: "shift ?P1 = Conj (sC rc_p) (pp_fun Prop (Var 2))" by (simp add: rc_sft k_fun_shift numeral_2_eq_2)
  have e1: "shift (Var 0) = Var 1" and e2: "shift (Var 1) = Var 2" by (simp_all add: shift_def)
  note st = s_fun_step[OF r2 y2 Y2]
  have tYy: "?G2 \<turnstile> App (Var 0) (Var 1) : Prop" and tYr: "?G2 \<turnstile> App (Var 0) (Var 2) : Prop" by (rule has_type.App[OF Y2 y2], rule has_type.App[OF Y2 r2])
  have s: "?G2 \<turnstile>\<^sub>U Imp (shift ?P1) (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift (Var 0))) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (shift (Var 1))))))))" unfolding sh1 e1 e2
    by (rule u_rc_pc1[OF st]) (insert sC_pi_ty[of ?G2] tF2 rc_pure_ty[OF Y2] tYy typed_ObjBox[OF has_type.Neg[OF tYr]], (unfold prop_eval.simps)?, blast+)
  have ri: "?G1 \<turnstile>\<^sub>U Imp ?P1 (rcR (Var 1) (Var 0))" by (rule u_rcR_intro[OF r1 y1 tP1 s])
  have ty: "?G1 \<turnstile> rcR (Var 1) (Var 0) : Prop" by (rule rcR_ty[OF r1 y1])
  have g: "?G0 \<turnstile>\<^sub>U Imp ?P0 (Forall Prop (rcR (Var 1) (Var 0)))" by (rule U_proves.Gen[OF tP0 ty]) (unfold sh0, rule ri)
  have e: "rcUni (Var 0) = Forall Prop (rcR (Var 1) (Var 0))" by (simp add: rcUni_def shift_def)
  have tU: "?G0 \<turnstile> rcUni (Var 0) : Prop" by (rule rcUni_ty[OF r0])
  show ?thesis by (rule u_rc_pc1[OF g[folded e]]) (insert sC_pi_ty[of ?G0] tF0 tU, (unfold prop_eval.simps)?, blast+) qed

lemma s_EG: "Prop # \<Gamma> \<turnstile>\<^sub>U Imp (rcUni (Var 0)) rcExUni" proof -
  have A: "Prop # Prop # \<Gamma> \<turnstile> rcUni (Var 0) : Prop" by (rule rcUni_ty) simp
  have T: "Prop # \<Gamma> \<turnstile> Var 0 : Prop" by simp
  have e: "subst0 (Var 0) (rcUni (Var 0)) = rcUni (Var 0)" by (simp add: rcUni_def rcR_def subst0_def shift_def)
  have "Prop # \<Gamma> \<turnstile>\<^sub>U Imp (subst0 (Var 0) (rcUni (Var 0))) (Exists Prop (rcUni (Var 0)))" using A T by (intro U_proves.H H_proves.EG)
  then show ?thesis unfolding e rcExUni_def . qed

lemma s_ExUni: "\<Gamma> \<turnstile>\<^sub>U Imp k_EF (Imp (sC rc_p) rcExUni)" proof -
  let ?Q = "Imp (sC rc_p) rcExUni"
  have tP: "Prop # \<Gamma> \<turnstile> pp_fun Prop (Var 0) : Prop" by (rule typed_pp_fun) simp
  have tQ: "\<Delta> \<turnstile> ?Q : Prop" for \<Delta> using sC_pi_ty[of \<Delta>] k_ExUni_ty[of \<Delta>] by blast
  have shq: "shift ?Q = ?Q" by (simp add: shift_def k_ExUni_shift[unfolded shift_def] sC_pi_shift[unfolded shift_def])
  have tU: "Prop # \<Gamma> \<turnstile> rcUni (Var 0) : Prop" by (rule rcUni_ty) simp
  have i: "Prop # \<Gamma> \<turnstile>\<^sub>U Imp (pp_fun Prop (Var 0)) (shift ?Q)" unfolding shq by (rule u_rc_pc2[OF s_uni_ctx s_EG]) (insert tP tQ[of "Prop # \<Gamma>"] sC_pi_ty[of "Prop # \<Gamma>"] k_ExUni_ty[of "Prop # \<Gamma>"] tU, (unfold prop_eval.simps)?, blast+)
  show ?thesis unfolding k_EF_def by (rule U_proves.Inst[OF tP tQ i]) qed

text \<open>The instance at pi, for every context: U proves not Phi_pi. Steps 1, 2 and 4 of the main note through s_coreU, with (a) for
  the two necessities and (b) for the closure; FMU and EF through s_ExUni.\<close>
lemma s_pi: "\<Gamma> \<turnstile>\<^sub>U Neg (sPhi rc_p)"
proof -
  have t: "\<Gamma> \<turnstile> Neg (sPhi rc_p) : Prop" using sPhi_ty[OF rc_p_ty] by blast
  show ?thesis by (rule u_rc_pc2[OF s_coreU s_ExUni t]) (unfold sPhi_def sA_pi prop_eval.simps, blast)
qed

section \<open>5. S: C proves, for every T, not Phi_T\<close>

text \<open>U sits in CEV by U_sub_CEV. The library's CEV_proves_subst_const puts the term Var 0 for the constant Pure at type rc_c,
  shifting it under each binder; s_subst says the result is sPhi (Var 0). Gen then binds T.\<close>
lemma s_syn_sub: "[rc_c] \<turnstile>\<^sub>CEV Neg (sPhi (Var 0))"
proof -
  have "[rc_c] \<turnstile>\<^sub>CEV subst_const pp_pure_name rc_c (Var 0) (Neg (sPhi rc_p))"
    by (rule CEV_proves_subst_const[OF U_sub_CEV[OF s_pi]]) simp
  then show ?thesis by (simp only: subst_const.simps s_subst)
qed

theorem syn_S: "[] \<turnstile>\<^sub>CEV Forall rc_c (Neg (sPhi (Var 0)))"
proof -
  have tQ: "[rc_c] \<turnstile> Neg (sPhi (Var 0)) : Prop" by (rule CEV_proves_formula[OF s_syn_sub])
  have st: "shift ObjTrue = ObjTrue" by (simp add: ObjTrue_def shift_def)
  have i: "[rc_c] \<turnstile>\<^sub>CEV Imp (shift ObjTrue) (Neg (sPhi (Var 0)))" unfolding st
    by (rule rc_pc1[OF s_syn_sub has_type.Imp[OF typed_ObjTrue tQ]]) (unfold prop_eval.simps, blast)
  have g: "[] \<turnstile>\<^sub>CEV Imp ObjTrue (Forall rc_c (Neg (sPhi (Var 0))))" by (rule CEV_proves.Gen[OF typed_ObjTrue tQ i])
  show ?thesis by (rule CEV_proves.MP[OF CEV_proves_ObjTrue g])
qed

corollary syn_S_term: assumes T: "\<Gamma> \<turnstile> T : rc_c" shows "\<Gamma> \<turnstile>\<^sub>CEV Neg (sPhi T)"
proof -
  have "\<Gamma> \<turnstile>\<^sub>CEV subst_const pp_pure_name rc_c T (Neg (sPhi rc_p))" by (rule CEV_proves_subst_const[OF U_sub_CEV[OF s_pi] T])
  then show ?thesis by (simp only: subst_const.simps s_subst)
qed

end
