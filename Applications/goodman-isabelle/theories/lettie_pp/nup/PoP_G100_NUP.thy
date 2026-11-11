theory PoP_G100_NUP
  imports PoP_Main.PoP_G100_Kernel
begin

text \<open>Purity of Pure: The Named Pieces of the Proof of NUP
  Helm and the Purity of Pure team, a group of Claude Opus 5.5 sessions
  This companion theory of the main theory holds the main note's named pieces of its proof of NUP (Lemmas A to D, the
  claim of Step 1, the identity, Steps 1 to 4, and the assembly), each in U and then in C. Dowel ported them, with Jacob, on
  2026-11-08, from four theories by Dowel; the typing lemma nup_rcS_ty is Reticle's proof. Each section below holds
  one source theory; the first two hold the blocks the main theory lacks. None of this text is Branden Fitelson's.\<close>

section \<open>1. Closed-term purity, application closure and PP_u as premises\<close>
definition rc_T0P :: "oterm set" where
  "rc_T0P = insert pp_target_PP (pp_purity_schema \<union> pp_application_closure_schema)"

lemma rc_T0P_ty: "A \<in> rc_T0P \<Longrightarrow> [] \<turnstile> A : Prop"
  unfolding rc_T0P_def using typed_pp_target_PP pp_purity_schema_typed pp_application_closure_schema_typed by blast

lemma rc_T0P_pure: "[] \<turnstile> M : \<sigma> \<Longrightarrow> consts_of M = {} \<Longrightarrow> pp_pure \<sigma> M \<in> rc_T0P"
  unfolding rc_T0P_def pp_purity_schema_def pp_logical_vocabulary_def by blast
lemma rc_T0P_ac: "pp_application_closure \<sigma> \<tau> \<in> rc_T0P"
  unfolding rc_T0P_def pp_application_closure_schema_def by blast
lemma rc_T0P_pp: "pp_pure rc_c rc_p \<in> rc_T0P"
  unfolding rc_T0P_def pp_target_PP_def pp_purity_of_pure_def by blast

section \<open>2. Shifts and local derivations\<close>

lemma rc_shift_box_closed: "shift rcBP = rcBP" "shift rcBQ = rcBQ"
  by (simp_all add: rc_sft rcP_def rcPp_def)

lemma rc_L_m: "[] ; T \<turnstile>\<^sub>CEV\<^sub>s A \<Longrightarrow> [] \<turnstile>\<^sub>CEV Imp A B \<Longrightarrow> [] ; T \<turnstile>\<^sub>CEV\<^sub>s B"
  by (rule CEV_set_derivable.Derive_MP[OF _ CEV_set_derivable.Theorem])

lemma rc_L_cj:
  assumes a: "[] ; T \<turnstile>\<^sub>CEV\<^sub>s A" and b: "[] ; T \<turnstile>\<^sub>CEV\<^sub>s B"
  shows "[] ; T \<turnstile>\<^sub>CEV\<^sub>s Conj A B"
proof -
  have ta: "[] \<turnstile> A : Prop" and tb: "[] \<turnstile> B : Prop" by (rule CEV_set_derivable_formula[OF a], rule CEV_set_derivable_formula[OF b])
  have c: "[] \<turnstile>\<^sub>CEV Imp A (Imp B (Conj A B))"
    by (rule CEV_prop_tautology) (insert ta tb, unfold prop_tautology_def prop_eval.simps, blast)
  show ?thesis by (rule CEV_set_derivable.Derive_MP[OF b rc_L_m[OF a c]])
qed

section \<open>3. The definitions, and Steps 1 and 2\<close>

text \<open>By Dowel, with Jacob, 2026-11-08; not Branden Fitelson's. The pieces of the main note's proof of NUP (its section
  4.2) under the paper's names, each in Loupe's U (H with the Rule of Equivalence at type t, without Modalized
  Functionality) and then in C by U_sub_CEV. The kernel's terms take pi (rc_p) as an argument: rcR a b is R(a, b),
  rcUni s is U(s), rcF x is F(x), rcQ x is Q(x), App rcP z is P(z), App rcPp z is P'(z); the possibility operator is
  written as not-box-not. This part: the definitions, Step 1 (Lemmas A to D, the claim of Step 1, the identity) and Step 2.\<close>
declare has_type.App[rule del]

subsection \<open>3.1 The definitions: N, and F(x) = box (not N(x))\<close>
definition nupN :: "oterm \<Rightarrow> oterm" where "nupN x = Disj (rcR x (Neg x)) (rcR (Neg x) x)"
lemma nupN_ty: "\<Gamma> \<turnstile> x : Prop \<Longrightarrow> \<Gamma> \<turnstile> nupN x : Prop" unfolding nupN_def by (intro has_type.Disj rcR_ty) (simp_all add: has_type.Neg)
lemma nup_F_eq: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Eq Prop (rcF x) (\<box>\<^sub>o (Neg (nupN x)))" proof -
  have tB: "\<Gamma> \<turnstile> rcB x : Prop" by (rule rcB_ty[OF x])
  have tN: "\<Gamma> \<turnstile> Neg (nupN x) : Prop" using nupN_ty[OF x] by blast
  have tF: "\<Gamma> \<turnstile> rcF x : Prop" by (rule rcF_ty[OF x])
  have e: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (rcB x) (Neg (nupN x))"
    by (rule u_rc_eq_of_iff[OF tB tN U_taut]) (insert tB tN, unfold nupN_def prop_tautology_def prop_eval.simps, blast)
  have b: "\<Gamma> \<turnstile>\<^sub>U (\<box>\<^sub>o (rcB x) \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (Neg (nupN x)))"
    using u_rc_congr[of \<Gamma> "\<box>\<^sub>o (Var 0)", OF typed_ObjBox[OF Var_typed_iff[THEN iffD2]] tB tN e] by (simp add: subst0_def)
  have i: "\<Gamma> \<turnstile>\<^sub>U (rcF x \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (Neg (nupN x)))"
    by (rule u_rc_pc2[OF u_rcF_iff[OF x] b]) (insert tF typed_ObjBox[OF tB] typed_ObjBox[OF tN], (unfold prop_eval.simps)?, blast+)
  show ?thesis by (rule u_rc_eq_of_iff[OF tF typed_ObjBox[OF tN] i])
qed
lemmas nup_R_iff = u_rcR_iff and nup_Q_iff = u_rcQ_iff and nup_P_iff = u_rcP_iff and nup_Pp_iff = u_rcPp_iff

subsection \<open>3.2 Step 1: four lemmas and a claim, for every proposition x\<close>
lemma nup_lemA: "\<Gamma> \<turnstile> x : Prop \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>U Imp (rcF x) (\<box>\<^sub>o (rcF x))" by (rule u_rc1a)
lemma nup_lemB: "\<Gamma> \<turnstile> x : Prop \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>U Imp (rcF x) (Eq Prop (rcQ x) x)" by (rule u_rc1b)
lemma nup_lemC: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Eq Prop (rcF (Neg x)) (rcF x)"
  by (rule u_rc_eq_of_iff[OF rcF_ty[OF has_type.Neg[OF x]] rcF_ty[OF x] u_rc1c[OF x]])
lemma nup_lemD: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Imp (Neg (rcQ x)) (rcF (rcQ x))"
  by (rule u_rc_pc1[OF u_rc_noP[OF x]]) (insert rcQ_ty[OF x] rcF_ty[OF rcQ_ty[OF x]], (unfold prop_eval.simps)?, blast+)
lemma nup_cor: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U \<box>\<^sub>o (Neg (App rcP (rcQ x)))" proof -
  have tq: "\<Gamma> \<turnstile> rcQ x : Prop" by (rule rcQ_ty[OF x])
  have tP: "\<Gamma> \<turnstile> App rcP (rcQ x) : Prop" by (rule has_type.App[OF rcP_ty tq])
  have n: "\<Gamma> \<turnstile>\<^sub>U Neg (App rcP (rcQ x))"
    by (rule u_rc_pc2[OF nup_lemD[OF x] u_rcP_iff[OF tq]]) (insert tq tP rcF_ty[OF tq], (unfold prop_eval.simps)?, blast+)
  show ?thesis by (rule U_nec[OF n])
qed
text \<open>The identity used below: P'(z) = P(not z), by Lemma C (at its iff form) and not-not-z iff z.\<close>
lemma nup_ident: assumes z: "\<Gamma> \<turnstile> z : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Eq Prop (App rcPp z) (App rcP (Neg z))" proof -
  have tn: "\<Gamma> \<turnstile> Neg z : Prop" using z by blast
  have t1: "\<Gamma> \<turnstile> App rcPp z : Prop" and t2: "\<Gamma> \<turnstile> App rcP (Neg z) : Prop" by (rule has_type.App[OF rcPp_ty z], rule has_type.App[OF rcP_ty tn])
  have i: "\<Gamma> \<turnstile>\<^sub>U (App rcPp z \<longleftrightarrow>\<^sub>o App rcP (Neg z))"
    by (rule u_rc_pc3[OF u_rcPp_iff[OF z] u_rcP_iff[OF tn] u_rc1c[OF z]]) (insert t1 t2, (unfold prop_eval.simps)?, blast+)
  show ?thesis by (rule u_rc_eq_of_iff[OF t1 t2 i])
qed
lemma nup_step1: assumes x: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Conj (Imp (rcF x) (\<box>\<^sub>o (rcF x))) (Conj (Imp (rcF x) (Eq Prop (rcQ x) x)) (Conj (Eq Prop (rcF (Neg x)) (rcF x))
    (Conj (Imp (Neg (rcQ x)) (rcF (rcQ x))) (\<box>\<^sub>o (Neg (App rcP (rcQ x)))))))"
  by (rule u_rc_pc5[OF nup_lemA[OF x] nup_lemB[OF x] nup_lemC[OF x] nup_lemD[OF x] nup_cor[OF x]]) (insert U_formula[OF nup_lemA[OF x]]
    U_formula[OF nup_lemB[OF x]] U_formula[OF nup_lemC[OF x]] U_formula[OF nup_lemD[OF x]] U_formula[OF nup_cor[OF x]], (unfold prop_eval.simps)?, blast+)

subsection \<open>3.3 Step 2: if pi(P) and pi(P') are necessary, every Q(x) is firm\<close>
lemma nup_step2: "\<Gamma> \<turnstile> x : Prop \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o (App rc_p rcP)) (Imp (\<box>\<^sub>o (App rc_p rcPp)) (rcF (rcQ x)))" by (rule u_rc2)

subsection \<open>3.4 The same pieces in C\<close>
lemmas nup_F_eq_C = nup_F_eq[THEN U_sub_CEV] and nup_lemA_C = nup_lemA[THEN U_sub_CEV] and nup_lemB_C = nup_lemB[THEN U_sub_CEV]
  and nup_lemC_C = nup_lemC[THEN U_sub_CEV] and nup_lemD_C = nup_lemD[THEN U_sub_CEV] and nup_cor_C = nup_cor[THEN U_sub_CEV]
  and nup_ident_C = nup_ident[THEN U_sub_CEV] and nup_step1_C = nup_step1[THEN U_sub_CEV] and nup_step2_C = nup_step2[THEN U_sub_CEV]

section \<open>4. Steps 3 and 4, and the assembly\<close>

text \<open>By Dowel, with Jacob, 2026-11-08; not Branden Fitelson's. The second part, line for line, with one
  change: rcS's typing is proved from its parts (nup_rcS_ty, Reticle's proof) in place of U_formula
  at u_S, in nup_step3 and nup_NUP_U. So the assembly is NUP from the named steps alone, at u_S's
  statement in U and at the local statement of the main proof in C. nupC Y is lambda z. Y(Q(z)).\<close>
declare has_type.App[rule del]

subsection \<open>4.1 The operator lambda z. Y(Q(z)), and Step 3's two facts as formulas\<close>
definition nupC :: "oterm \<Rightarrow> oterm" where "nupC Y = Lam Prop (App (shift Y) (rcQ (Var 0)))"
definition nupS3a :: oterm where "nupS3a = Forall Prop (rcF (rcQ (Var 0)))"
definition nupS3b :: oterm where "nupS3b = Forall rc_u (Imp (App rc_p (Var 0)) (App rc_p (Lam Prop (App (Var 1) (rcQ (Var 0))))))"
lemma nupC_ty: assumes Y: "\<Gamma> \<turnstile> Y : rc_u" shows "\<Gamma> \<turnstile> nupC Y : rc_u" proof -
  have "Prop # \<Gamma> \<turnstile> App (shift Y) (rcQ (Var 0)) : Prop" by (rule has_type.App[OF weaken_shift_type_ok[OF Y] rcQ_ty]) simp
  then show ?thesis unfolding nupC_def by (rule has_type.Lam)
qed
lemma nupC_iff: assumes Y: "\<Gamma> \<turnstile> Y : rc_u" and x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U (App (nupC Y) x \<longleftrightarrow>\<^sub>o App Y (rcQ x))" proof -
  have t: "\<Gamma> \<turnstile> App (Lam Prop (App (shift Y) (rcQ (Var 0)))) x : Prop" using has_type.App[OF nupC_ty[OF Y] x] unfolding nupC_def .
  show ?thesis using u_beta[OF t] by (simp add: nupC_def rcQ_def subst0_def)
qed
lemma nup_be_arg: assumes "beta_eta_equiv \<Gamma> \<sigma> a a'" and "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" shows "beta_eta_equiv \<Gamma> \<tau> (App F a) (App F a')"
  using assms
proof (induction rule: beta_eta_equiv.induct)
  case (Refl \<Gamma> M \<rho>) show ?case by (rule beta_eta_equiv.Refl[OF has_type.App[OF Refl.prems Refl.hyps]])
next
  case (Beta \<Gamma> M \<rho> N) show ?case by (rule beta_eta_equiv.Beta[OF has_type.App[OF Beta.prems Beta.hyps(1)] has_type.App[OF Beta.prems Beta.hyps(2)]
    compatible_step.App_right[OF Beta.hyps(3)]])
next
  case (Eta \<Gamma> M \<rho> N) show ?case by (rule beta_eta_equiv.Eta[OF has_type.App[OF Eta.prems Eta.hyps(1)] has_type.App[OF Eta.prems Eta.hyps(2)]
    compatible_step.App_right[OF Eta.hyps(3)]])
next
  case (Sym \<Gamma> \<rho> M N) show ?case by (rule beta_eta_equiv.Sym[OF Sym.IH[OF Sym.prems]])
next
  case (Trans \<Gamma> \<rho> M N P) show ?case by (rule beta_eta_equiv.Trans[OF Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed
lemma nupC_W: assumes Y: "\<Gamma> \<turnstile> Y : rc_u" shows "beta_eta_equiv \<Gamma> rc_u (rcW Y) (nupC Y)" proof -
  let ?B = "\<lambda>q. Lam Prop (App (Var 1) (App (App rc_Q q) (Var 0)))"
  have s0: "beta_eta_equiv \<Gamma> (rc_u \<rightarrow>\<^sub>o rc_u) (App rc_W rc_p) (Lam rc_u (?B rc_p))"
    using rc_be1[OF has_type.App[OF rc_W_ty rc_p_ty, unfolded rc_W_def]] unfolding rc_W_def by (simp add: subst0_def eval_nat_numeral)
  have s1: "beta_eta_equiv \<Gamma> rc_u (rcW Y) (App (Lam rc_u (?B rc_p)) Y)" unfolding rcW_def by (rule rc_be_app[OF s0 refl Y])
  have "beta_eta_equiv \<Gamma> rc_u (rcW Y) (Lam Prop (App (shift Y) (App (App rc_Q rc_p) (Var 0))))"
    using beta_eta_equiv.Trans[OF s1 rc_be1[OF beta_eta_equiv_right_type[OF s1]]] by (simp add: subst0_def flip: shift_def)
  then show ?thesis unfolding nupC_def rcQ_def .
qed
lemma nup_piC: assumes Y: "\<Gamma> \<turnstile> Y : rc_u" shows "\<Gamma> \<turnstile>\<^sub>U (App rc_p (rcW Y) \<longleftrightarrow>\<^sub>o App rc_p (nupC Y))"
  by (rule U_beta_eta_equiv[OF nup_be_arg[OF nupC_W[OF Y] rc_p_ty]])
lemma nup_rename_FQ: "rename \<rho> rc_F = rc_F" "rename \<rho> rc_Q = rc_Q"
  by (simp_all add: rc_F_def rc_Q_def rc_rename_R ObjBox_def ObjTrue_def eval_nat_numeral)
lemma nupS3a_shift[simp]: "shift nupS3a = nupS3a" by (simp add: nupS3a_def rcF_def rcQ_def shift_def nup_rename_FQ)
lemma nupS3b_shift[simp]: "shift nupS3b = nupS3b" by (simp add: nupS3b_def rcQ_def shift_def nup_rename_FQ eval_nat_numeral)
lemma nupS3a_ty: "\<Gamma> \<turnstile> nupS3a : Prop" unfolding nupS3a_def by (intro has_type.Forall rcF_ty rcQ_ty) simp
lemma nupS3b_ty: "\<Gamma> \<turnstile> nupS3b : Prop" proof -
  have y: "rc_u # \<Gamma> \<turnstile> Var 0 : rc_u" by simp
  have c: "rc_u # \<Gamma> \<turnstile> Lam Prop (App (Var 1) (rcQ (Var 0))) : rc_u" using nupC_ty[OF y] by (simp add: nupC_def shift_def eval_nat_numeral)
  show ?thesis unfolding nupS3b_def by (intro has_type.Forall has_type.Imp rc_pure_ty[OF y] rc_pure_ty[OF c])
qed

lemma nup_rcS_ty: "[] \<turnstile> rcS : Prop" proof -
  have z: "[] \<turnstile> zI (App rc_p rcP) : Prop" "[] \<turnstile> zI (App rc_p rcPp) : Prop"
    unfolding zI_def by (intro has_type.Imp typed_pp_pure rc_pure_ty rcP_ty rcPp_ty typed_ObjBox)+
  show ?thesis unfolding rcS_def by (intro has_type.Conj rcHU_ty typed_pp_pure rc_P_ty rc_Pp_ty z rc_T0P_ty[OF rc_T0P_ac])
qed

subsection \<open>4.2 Step 3: pi(P) and pi(P') are necessary, every Q(x) is firm, and lambda z. Y(Q(z)) is pure when Y is\<close>
theorem nup_step3: "[] \<turnstile>\<^sub>U Imp rcS (Conj rcBP (Conj rcBQ (Conj nupS3a nupS3b)))" proof -
  note p1 = u_rc_piP[of "[]"] and p2 = u_rc_piPp[of "[]"] and a1 = u_rc_ac[OF rc_p_ty rcP_ty, of "[]"] and a2 = u_rc_ac[OF rc_p_ty rcPp_ty, of "[]"]
  have tS: "[] \<turnstile> rcS : Prop" by (rule nup_rcS_ty)
  have tBB: "[] \<turnstile> Conj rcBP rcBQ : Prop" using rcBP_ty[of "[]"] rcBQ_ty[of "[]"] by blast
  have tb: "[] \<turnstile> Imp rcS (Conj rcBP rcBQ) : Prop" using tS tBB by blast
  have b: "[] \<turnstile>\<^sub>U Imp rcS (Conj rcBP rcBQ)"
    by (rule u_rc_pc4[OF p1 p2 a1 a2 tb]) (unfold rcS_def zI_def rcHU_def pp_pure_def rcP_def rcPp_def prop_eval.simps, blast)
  have v0: "[Prop] \<turnstile> Var 0 : Prop" by simp
  have tFQ: "[Prop] \<turnstile> rcF (rcQ (Var 0)) : Prop" by (rule rcF_ty[OF rcQ_ty[OF v0]])
  have g0: "[Prop] \<turnstile>\<^sub>U Imp (shift (Conj rcBP rcBQ)) (rcF (rcQ (Var 0)))" unfolding rc_sft rc_shift_box_closed
    by (rule u_rc_pc1[OF u_rc2[OF v0]]) (insert rcBP_ty[of "[Prop]"] rcBQ_ty[of "[Prop]"] tFQ, (unfold prop_eval.simps)?, blast+)
  have g: "[] \<turnstile>\<^sub>U Imp (Conj rcBP rcBQ) nupS3a" unfolding nupS3a_def by (rule U_proves.Gen[OF tBB tFQ g0])
  have y: "[rc_u] \<turnstile> Var 0 : rc_u" by simp
  have tW: "[rc_u] \<turnstile> rcW (Var 0) : rc_u" by (rule rcW_ty[OF y])
  have tC: "[rc_u] \<turnstile> App rc_p (nupC (Var 0)) : Prop" by (rule rc_pure_ty[OF nupC_ty[OF y]])
  note c1 = u_rc_ac[OF rc_W_ty rc_p_ty, of "[rc_u]"] and c2 = u_rc_ac[OF has_type.App[OF rc_W_ty rc_p_ty] y]
  have s3: "[rc_u] \<turnstile>\<^sub>U Imp rcHU (Imp (App rc_p (Var 0)) (App rc_p (rcW (Var 0))))" by (rule u_rc_pc2[OF c1 c2])
    (insert rcHU_ty[of "[rc_u]"] rc_pure_ty[OF y] rc_pure_ty[OF tW], (unfold rcHU_def rcW_def pp_pure_def prop_eval.simps)?, blast+)
  have c: "[rc_u] \<turnstile>\<^sub>U Imp rcHU (Imp (App rc_p (Var 0)) (App rc_p (nupC (Var 0))))" by (rule u_rc_pc2[OF s3 nup_piC[OF y]])
    (insert rcHU_ty[of "[rc_u]"] rc_pure_ty[OF y] rc_pure_ty[OF tW] tC, (unfold prop_eval.simps)?, blast+)
  have e: "nupC (Var 0) = Lam Prop (App (Var 1) (rcQ (Var 0)))" by (simp add: nupC_def shift_def eval_nat_numeral)
  have h0: "[rc_u] \<turnstile>\<^sub>U Imp (shift rcHU) (Imp (App rc_p (Var 0)) (App rc_p (Lam Prop (App (Var 1) (rcQ (Var 0))))))"
    unfolding rcHU_shift e[symmetric] by (rule c)
  have tB0: "[rc_u] \<turnstile> Imp (App rc_p (Var 0)) (App rc_p (Lam Prop (App (Var 1) (rcQ (Var 0))))) : Prop"
    using nupS3b_ty[of "[]"] unfolding nupS3b_def by (auto elim: has_type.cases)
  have h: "[] \<turnstile>\<^sub>U Imp rcHU nupS3b" unfolding nupS3b_def by (rule U_proves.Gen[OF rcHU_ty tB0 h0])
  have tG: "[] \<turnstile> Imp rcS (Conj rcBP (Conj rcBQ (Conj nupS3a nupS3b))) : Prop" using tS rcBP_ty[of "[]"] rcBQ_ty[of "[]"] nupS3a_ty[of "[]"] nupS3b_ty[of "[]"] by blast
  show ?thesis by (rule u_rc_pc3[OF b g h tG]) (unfold rcS_def prop_eval.simps, blast)
qed
theorem nup_step3_T: "[] ; insert pp_zeroary_exhaustion rc_T0P \<turnstile>\<^sub>CEV\<^sub>s Conj rcBP (Conj rcBQ (Conj nupS3a nupS3b))" proof -
  let ?T = "insert pp_zeroary_exhaustion rc_T0P"
  have ty: "[] \<turnstile> A : Prop" if "A \<in> ?T" for A using that typed_pp_zeroary_exhaustion rc_T0P_ty by blast
  have ax: "[] ; ?T \<turnstile>\<^sub>CEV\<^sub>s A" if "A \<in> ?T" for A by (rule CEV_set_derivable.Assumption[OF that ty[OF that]])
  have ar: "[] ; ?T \<turnstile>\<^sub>CEV\<^sub>s A" if "A \<in> rc_T0P" for A using that ax by blast
  note W = ar[OF rc_T0P_pure[OF rc_W_ty rc_W_consts]] and PP = ar[OF rc_T0P_pp] and AC = ar[OF rc_T0P_ac]
  note P = ar[OF rc_T0P_pure[OF rc_P_ty rc_consts(4)]] and Pp = ar[OF rc_T0P_pure[OF rc_Pp_ty rc_consts(5)]]
  note E = ax[of pp_zeroary_exhaustion, OF insertI1]
  have H: "[] ; ?T \<turnstile>\<^sub>CEV\<^sub>s rcHU" unfolding rcHU_def by (intro rc_L_cj W PP AC)
  have zP: "[] ; ?T \<turnstile>\<^sub>CEV\<^sub>s zI (App rc_p rcP)" by (rule rc_L_m[OF E U_sub_CEV[OF u_zI[OF rc_pure_ty[OF rcP_ty]]]])
  have zQ: "[] ; ?T \<turnstile>\<^sub>CEV\<^sub>s zI (App rc_p rcPp)" by (rule rc_L_m[OF E U_sub_CEV[OF u_zI[OF rc_pure_ty[OF rcPp_ty]]]])
  have S: "[] ; ?T \<turnstile>\<^sub>CEV\<^sub>s rcS" unfolding rcS_def by (intro rc_L_cj H P Pp AC zP zQ)
  show ?thesis by (rule rc_L_m[OF S U_sub_CEV[OF nup_step3]])
qed

subsection \<open>4.3 Step 4: if U(s), then Q(s) is not firm; so no proposition is universal\<close>
lemma nup_s4_core: assumes r: "\<Gamma> \<turnstile> r : Prop" and Y: "\<Gamma> \<turnstile> Y : rc_u"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp nupS3b (Imp (rcUni r) (Imp (rcF (rcQ r)) (Imp (App rc_p Y) (Imp (App Y (Neg (rcQ r))) (Neg (\<box>\<^sub>o (Neg (App Y (rcQ r)))))))))" proof -
  let ?e = "rcQ r" let ?n = "Neg (rcQ r)" let ?C = "nupC Y"
  have te: "\<Gamma> \<turnstile> ?e : Prop" by (rule rcQ_ty[OF r])
  have tn: "\<Gamma> \<turnstile> ?n : Prop" using te by blast
  have tC: "\<Gamma> \<turnstile> ?C : rc_u" by (rule nupC_ty[OF Y])
  have tQn: "\<Gamma> \<turnstile> rcQ ?n : Prop" by (rule rcQ_ty[OF tn])
  have tB: "rc_u # \<Gamma> \<turnstile> Imp (App rc_p (Var 0)) (App rc_p (Lam Prop (App (Var 1) (rcQ (Var 0))))) : Prop"
    using nupS3b_ty[of \<Gamma>] unfolding nupS3b_def by (auto elim: has_type.cases)
  have eb: "subst0 Y (Imp (App rc_p (Var 0)) (App rc_p (Lam Prop (App (Var 1) (rcQ (Var 0)))))) = Imp (App rc_p Y) (App rc_p ?C)"
    by (simp add: nupC_def rcQ_def subst0_def flip: shift_def)
  have pb: "\<Gamma> \<turnstile>\<^sub>U Imp nupS3b (Imp (App rc_p Y) (App rc_p ?C))" unfolding nupS3b_def eb[symmetric] using tB Y by (intro U_proves.H H_proves.UI)
  note w1 = nupC_iff[OF Y r] and w2 = nupC_iff[OF Y tn]
  have tYe: "\<Gamma> \<turnstile> App Y ?e : Prop" and tYn: "\<Gamma> \<turnstile> App Y ?n : Prop" and tYQ: "\<Gamma> \<turnstile> App Y (rcQ ?n) : Prop"
    by (rule has_type.App[OF Y te], rule has_type.App[OF Y tn], rule has_type.App[OF Y tQn])
  have tCr: "\<Gamma> \<turnstile> App ?C r : Prop" and tCn: "\<Gamma> \<turnstile> App ?C ?n : Prop" by (rule has_type.App[OF tC r], rule has_type.App[OF tC tn])
  have k0: "\<Gamma> \<turnstile>\<^sub>U Imp (Neg (App Y ?e)) (Neg (App ?C r))" by (rule u_rc_pc1[OF w1]) (insert tYe tCr, (unfold prop_eval.simps)?, blast+)
  note k = u_rc_K[OF k0]
  have s1: "\<Gamma> \<turnstile>\<^sub>U Imp (rcF ?e) (Imp (App Y ?n) (App Y (rcQ ?n)))"
    by (rule u_rc_pc4[OF u_rc1b[OF tn] u_rc1c[OF te] U_eq_sym[OF tQn tn] u_rc_LL[OF tn tQn Y]]) (insert rcF_ty[OF te] tYn tYQ, (unfold prop_eval.simps)?, blast+)
  have t1: "\<Gamma> \<turnstile>\<^sub>U Imp (rcF ?e) (Imp (App Y ?n) (App ?C ?n))" by (rule u_rc_pc2[OF s1 w2]) (insert rcF_ty[OF te] tYn tCn, (unfold prop_eval.simps)?, blast+)
  have tGoal: "\<Gamma> \<turnstile> Imp nupS3b (Imp (rcUni r) (Imp (rcF ?e) (Imp (App rc_p Y) (Imp (App Y ?n) (Neg (\<box>\<^sub>o (Neg (App Y ?e)))))))) : Prop"
    using nupS3b_ty[of \<Gamma>] rcUni_ty[OF r] rcF_ty[OF te] rc_pure_ty[OF Y] tYn typed_ObjBox[OF has_type.Neg[OF tYe]] by blast
  show ?thesis by (rule u_rc_pc5[OF pb u_rcUni_inst[OF r tn] u_rcR_elim[OF r tn tC] t1 k tGoal]) (unfold prop_eval.simps, blast)
qed
theorem nup_step4: "[] \<turnstile>\<^sub>U Imp nupS3a (Imp nupS3b (Neg rcExUni))" proof -
  let ?G = "[Prop]" let ?G1 = "[rc_u, Prop]" let ?r = "Var 0"
  have r: "?G \<turnstile> ?r : Prop" by simp
  have r1: "?G1 \<turnstile> Var 1 : Prop" by simp
  have y1: "?G1 \<turnstile> Var 0 : rc_u" by simp
  let ?e = "rcQ ?r" let ?n = "Neg (rcQ ?r)" let ?P = "Conj nupS3b (Conj (rcUni ?r) (rcF ?e))"
  have te: "?G \<turnstile> ?e : Prop" by (rule rcQ_ty[OF r])
  have tn: "?G \<turnstile> ?n : Prop" using te by blast
  have tf: "?G \<turnstile> rcUni ?r : Prop" by (rule rcUni_ty[OF r])
  have tP: "?G \<turnstile> ?P : Prop" using nupS3b_ty[of ?G] rcF_ty[OF te] tf by blast
  have sh: "shift ?P = Conj nupS3b (Conj (rcUni (Var 1)) (rcF (rcQ (Var 1))))" by (simp add: rc_sft rcUni_shift)
  have sh2: "shift ?n = Neg (rcQ (Var 1))" and sh3: "shift ?e = rcQ (Var 1)" by (simp_all add: rc_sft)
  note st = nup_s4_core[OF r1 y1]
  have s: "?G1 \<turnstile>\<^sub>U Imp (shift ?P) (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift ?n)) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (shift ?e)))))))"
    unfolding sh sh2 sh3 proof (rule u_rc_pc1[OF st])
    show "?G1 \<turnstile> Imp (Conj nupS3b (Conj (rcUni (Var 1)) (rcF (rcQ (Var 1))))) (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (Neg (rcQ (Var 1))))
        (Neg (\<box>\<^sub>o (Neg (App (Var 0) (rcQ (Var 1)))))))) : Prop"
      using U_formula[OF st] nupS3b_ty[of ?G1] rcUni_ty[OF r1] rcF_ty[OF rcQ_ty[OF r1]] by (auto elim!: has_type.cases[of _ "Imp _ _"])
  qed (unfold prop_eval.simps, blast)
  note ri = u_rcR_intro[OF te tn tP s]
  note u = u_rcF_iff[OF te] and T = U_modal_T[OF rcB_ty[OF te], unfolded modal_T_def]
  have tA: "Prop # ?G \<turnstile> rcF (rcQ (Var 0)) : Prop" by (rule rcF_ty[OF rcQ_ty]) simp
  have e1: "subst0 ?r (rcF (rcQ (Var 0))) = rcF ?e" by (simp add: subst0_def rcF_def rcQ_def)
  have fe: "?G \<turnstile>\<^sub>U Imp nupS3a (rcF ?e)" using U_proves.H[OF H_proves.UI[OF tA r]] unfolding e1 nupS3a_def .
  have c: "?G \<turnstile>\<^sub>U Imp nupS3a (Imp nupS3b (Neg (rcUni ?r)))"
    by (rule u_rc_pc4[OF ri u T fe]) (insert nupS3a_ty[of ?G] nupS3b_ty[of ?G] tf, (unfold prop_eval.simps)?, blast+)
  let ?Q = "Neg (Conj nupS3a nupS3b)"
  have tQ: "\<Gamma> \<turnstile> ?Q : Prop" for \<Gamma> using nupS3a_ty[of \<Gamma>] nupS3b_ty[of \<Gamma>] by blast
  have shq: "shift ?Q = ?Q" by (simp add: rc_sft)
  have i: "?G \<turnstile>\<^sub>U Imp (rcUni ?r) (shift ?Q)" unfolding shq by (rule u_rc_pc1[OF c]) (insert tf tQ[of ?G], (unfold prop_eval.simps)?, blast+)
  note inst = U_proves.Inst[OF tf tQ i]
  have tE: "[] \<turnstile> rcExUni : Prop" unfolding rcExUni_def by (rule has_type.Exists[OF tf])
  show ?thesis by (rule u_rc_pc1[OF inst[folded rcExUni_def]]) (insert tE nupS3a_ty[of "[]"] nupS3b_ty[of "[]"], (unfold prop_eval.simps)?, blast+)
qed

subsection \<open>4.4 The assembly: NUP from the named steps\<close>
theorem nup_NUP_U: "[] \<turnstile>\<^sub>U Imp rcS (Neg rcExUni)"
  by (rule u_rc_pc2[OF nup_step3 nup_step4]) (insert nup_rcS_ty k_ExUni_ty[of "[]"], (unfold prop_eval.simps)?, blast+)
theorem nup_NUP: "[] ; insert pp_zeroary_exhaustion rc_T0P \<turnstile>\<^sub>CEV\<^sub>s Neg rcExUni" proof -
  have c: "[] \<turnstile>\<^sub>CEV Imp (Conj rcBP (Conj rcBQ (Conj nupS3a nupS3b))) (Neg rcExUni)" by (rule rc_pc1[OF U_sub_CEV[OF nup_step4]])
    (insert rcBP_ty[of "[]"] rcBQ_ty[of "[]"] nupS3a_ty[of "[]"] nupS3b_ty[of "[]"] k_ExUni_ty[of "[]"], (unfold prop_eval.simps)?, blast+)
  show ?thesis by (rule rc_L_m[OF nup_step3_T c])
qed
lemmas nupC_iff_C = nupC_iff[THEN U_sub_CEV] and nup_step3_C = nup_step3[THEN U_sub_CEV] and nup_step4_C = nup_step4[THEN U_sub_CEV]
  and nup_NUP_U_C = nup_NUP_U[THEN U_sub_CEV]

end
