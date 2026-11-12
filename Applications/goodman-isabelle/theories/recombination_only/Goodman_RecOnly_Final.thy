theory Goodman_RecOnly_Final
  imports Goodman_RecOnly_Relative
begin

text \<open>Recombination without Exhaustion, Sections 5 to 7 of the hand proof: the premises, the guard
  (Lemmas 11 and 12), the contradiction (Lemma 13, Theorem 1) and the Recombination corollary. Calculus: Lettie's U;
  the ordinary premises are the antecedent roPrem (Logical Purity and Application instances, and
  PP_u), never necessitated. The set-based statements use the repository's premise relation
  CEV_set_derivable (Assumption, Theorem, Derive_MP only).\<close>

declare has_type.App[rule del]

section \<open>1. Two more closed logical operators, and the premises\<close>

text \<open>Z := \<lambda>x. (a \<and> Y x), and composition Y \<circ> Q.\<close>
definition ro_Z :: oterm where "ro_Z = Lam Prop (Lam rc_u (Lam Prop (Conj (Var 2) (App (Var 1) (Var 0)))))"
definition ro_comp :: oterm where "ro_comp = Lam rc_u (Lam rc_u (Lam Prop (App (Var 2) (App (Var 1) (Var 0)))))"

lemma ro_Z_ty: "\<Gamma> \<turnstile> ro_Z : Prop \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)" by (rule infer_type_sound) (simp add: ro_Z_def lookup_def)
lemma ro_comp_ty: "\<Gamma> \<turnstile> ro_comp : rc_u \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)" by (rule infer_type_sound) (simp add: ro_comp_def lookup_def)
lemma ro_fin_consts: "consts_of ro_Z = {}" "consts_of ro_comp = {}" by (simp_all add: ro_Z_def ro_comp_def)

text \<open>The remaining ordinary premises: Logical Purity at \<Phi>, P, P', Q, Z and composition; Application at
  (u\<rightarrow>t, u), (u\<rightarrow>t, t\<rightarrow>u), (t, u), (t, u\<rightarrow>u) and (u, u\<rightarrow>u).\<close>
definition roHF :: oterm where
  "roHF = Conj (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) ro_Phi) (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o rc_u)) ro_P)
     (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o rc_u)) ro_Pp) (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o rc_u)) ro_Q)
     (Conj (pp_pure (Prop \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) ro_Z) (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) ro_comp)
     (Conj (pp_application_closure rc_c rc_u) (Conj (pp_application_closure rc_c (Prop \<rightarrow>\<^sub>o rc_u))
     (Conj (pp_application_closure Prop rc_u) (Conj (pp_application_closure Prop (rc_u \<rightarrow>\<^sub>o rc_u))
     (pp_application_closure rc_u (rc_u \<rightarrow>\<^sub>o rc_u)))))))))))"

text \<open>All ordinary premises of Theorem 1: roHC (Goodman_RecOnly_Closure, ending with PP_u) and roHF.\<close>
definition roPrem :: oterm where "roPrem = Conj roHC roHF"

lemma roHF_ty: "\<Gamma> \<turnstile> roHF : Prop"
  by (rule infer_type_sound) (simp add: roHF_def ro_Phi_def ro_P_def ro_Pp_def ro_Q_def ro_F_def ro_R_def ro_Z_def ro_comp_def
    ObjBox_def ObjTrue_def pp_application_closure_def pp_pure_def pp_Pure_def lookup_def)
lemma roPrem_ty: "\<Gamma> \<turnstile> roPrem : Prop" unfolding roPrem_def by (intro has_type.Conj roHC_ty roHF_ty)
lemma roHF_shift[simp]: "shift roHF = roHF"
  by (simp add: roHF_def ro_Z_def ro_comp_def pp_application_closure_def pp_pure_def pp_Pure_def shift_def)
lemma roPrem_shift[simp]: "shift roPrem = roPrem" by (simp add: roPrem_def rc_sft)

section \<open>2. Constructing the required pure truth (Section 6 of the hand proof, Lemmas 11 and 12)\<close>

lemmas roA_closed[simp] = roa_closed[OF roPhi_ty ro_rel_subst(10) ro_rel_ren(10)]
lemmas roA_ty = roa_ty[OF roPhi_ty ro_rel_subst(10) ro_rel_ren(10)]

text \<open>\<Phi> is pure: its sole nonlogical parameter is the pure \<pi>.\<close>
theorem ro_Phi_pure: "\<Gamma> \<turnstile>\<^sub>U Imp roPrem (pp_pure rc_u roPhi)"
proof -
  note a = u_rc_ac[OF ro_Phi_ty rc_p_ty, of \<Gamma>]
  have tg: "\<Gamma> \<turnstile> Imp roPrem (pp_pure rc_u roPhi) : Prop" by (intro has_type.Imp roPrem_ty typed_pp_pure roPhi_ty)
  show ?thesis by (rule u_rc_pc1[OF a tg]) (unfold roPrem_def roHC_def roHF_def roPhi_def pp_pure_def prop_eval.simps, blast)
qed

text \<open>\<Phi> preserves pure truths: if b is pure and true, P_b and P'_b are pure, so \<kappa>(b) and \<Phi>(b) hold.\<close>
theorem ro_Phi_pres: "\<Gamma> \<turnstile>\<^sub>U Imp roPrem (roPres roPhi)"
proof -
  let ?D = "Prop # \<Gamma>"
  have v: "?D \<turnstile> Var 0 : Prop" by simp
  have t1: "?D \<turnstile> App ro_P rc_p : Prop \<rightarrow>\<^sub>o rc_u" by (rule has_type.App[OF ro_P_ty rc_p_ty])
  have t2: "?D \<turnstile> App ro_Pp rc_p : Prop \<rightarrow>\<^sub>o rc_u" by (rule has_type.App[OF ro_Pp_ty rc_p_ty])
  note a1 = u_rc_ac[OF ro_P_ty rc_p_ty, of ?D] and a2 = u_rc_ac[OF t1 v] and a3 = u_rc_ac[OF ro_Pp_ty rc_p_ty, of ?D]
    and a4 = u_rc_ac[OF t2 v] and ph = roPhi_iff[OF v]
  have tg: "?D \<turnstile> Imp roPrem (Imp (Conj (pp_pure Prop (Var 0)) (Var 0)) (App roPhi (Var 0))) : Prop"
    by (intro has_type.Imp has_type.Conj roPrem_ty typed_pp_pure v has_type.App[OF roPhi_ty])
  have h: "?D \<turnstile>\<^sub>U Imp roPrem (Imp (Conj (pp_pure Prop (Var 0)) (Var 0)) (App roPhi (Var 0)))"
    by (rule u_rc_pc5[OF a1 a2 a3 a4 ph tg]) (unfold roPrem_def roHC_def roHF_def rok_def roP_def roPp_def pp_pure_def prop_eval.simps, blast)
  show ?thesis using ro_gen[OF roPrem_ty roPrem_shift h] unfolding roPres_def .
qed

text \<open>Lemma 12(a): a is pure and true.\<close>
theorem ro_actual: "\<Gamma> \<turnstile>\<^sub>U Imp roPrem (Conj (pp_pure Prop (roa roPhi)) (roa roPhi))"
proof -
  note c = ro_closure_true[OF roPhi_ty ro_rel_subst(10) ro_rel_ren(10), of \<Gamma>]
  have tg: "\<Gamma> \<turnstile> Imp roPrem (Conj (pp_pure Prop (roa roPhi)) (roa roPhi)) : Prop"
    by (intro has_type.Imp has_type.Conj roPrem_ty typed_pp_pure roA_ty)
  show ?thesis by (rule u_rc_pc3[OF c ro_Phi_pure ro_Phi_pres tg]) (unfold roPrem_def prop_eval.simps, blast)
qed

text \<open>Lemma 12(b): \<box>(a \<longrightarrow> \<kappa>(a)), a theorem of the base logic.\<close>
theorem ro_certificate: "\<Gamma> \<turnstile>\<^sub>U \<box>\<^sub>o (Imp (roa roPhi) (rok (roa roPhi)))"
proof -
  let ?a = "roa roPhi"
  note bx = ro_boxed[OF roPhi_ty ro_rel_subst(10) ro_rel_ren(10), of \<Gamma>] and ph = roPhi_iff[OF roA_ty]
  have ta: "\<Gamma> \<turnstile> ?a : Prop" by (rule roA_ty)
  have g: "\<Gamma> \<turnstile>\<^sub>U Imp (Imp ?a (App roPhi ?a)) (Imp ?a (rok ?a))"
    by (rule u_rc_pc1[OF ph]) (insert ta rok_ty[OF ta] has_type.App[OF roPhi_ty ta], (unfold prop_eval.simps)?, blast+)
  show ?thesis by (rule U_proves.MP[OF bx u_rc_K[OF g]])
qed

text \<open>Lemma 12(c), Lemma 9 at b = a: F_a(Q_a(x)) for every x.\<close>
theorem ro_Fa: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U roF (roa roPhi) (roQ (roa roPhi) x)"
  by (rule U_proves.MP[OF ro_certificate ro_relative[OF roA_ty x]])

section \<open>3. The final contradiction (Section 7 of the hand proof)\<close>

definition roZ :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where "roZ a Y = App (App ro_Z a) Y"
definition roComp :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where "roComp Y Z = App (App ro_comp Y) Z"

lemma roZ_iff: assumes a: "\<Gamma> \<turnstile> a : Prop" and Y: "\<Gamma> \<turnstile> Y : rc_u" and x: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U (App (roZ a Y) x \<longleftrightarrow>\<^sub>o Conj a (App Y x))"
proof -
  have "beta_eta_equiv \<Gamma> Prop (App (roZ a Y) x) (Conj a (App Y x))"
    using ro_be3[OF ro_Z_ty[unfolded ro_Z_def] a Y x] unfolding roZ_def ro_Z_def
    by (simp add: subst0_def eval_nat_numeral flip: shift_def)
  then show ?thesis by (rule U_beta_eta_equiv)
qed

lemma roComp_iff: assumes Y: "\<Gamma> \<turnstile> Y : rc_u" and Z: "\<Gamma> \<turnstile> Z : rc_u" and x: "\<Gamma> \<turnstile> x : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U (App (roComp Y Z) x \<longleftrightarrow>\<^sub>o App Y (App Z x))"
proof -
  have "beta_eta_equiv \<Gamma> Prop (App (roComp Y Z) x) (App Y (App Z x))"
    using ro_be3[OF ro_comp_ty[unfolded ro_comp_def] Y Z x] unfolding roComp_def ro_comp_def
    by (simp add: subst0_def eval_nat_numeral flip: shift_def)
  then show ?thesis by (rule U_beta_eta_equiv)
qed

lemma ro_rcUni_shift[simp]: "shift (rcUni s) = rcUni (shift s)"
  by (simp add: rcUni_def rcR_def shift_def rc_rename_rename rc_rename_R)

text \<open>Universality of r gives R_a(r,y) for every y, through the pure operator Z = \<lambda>x. (a \<and> Y x).\<close>
lemma ro_step1: assumes r: "\<Gamma> \<turnstile> r : Prop" and y: "\<Gamma> \<turnstile> y : Prop" and Y: "\<Gamma> \<turnstile> Y : rc_u"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp roPrem (Imp (rcUni r) (Imp (App rc_p Y) (Imp (App Y y) (Neg (\<box>\<^sub>o (Neg (Conj (roa roPhi) (App Y r))))))))"
proof -
  let ?a = "roa roPhi" let ?Z = "roZ (roa roPhi) Y"
  have ta: "\<Gamma> \<turnstile> ?a : Prop" by (rule roA_ty)
  have tZa: "\<Gamma> \<turnstile> App ro_Z ?a : rc_u \<rightarrow>\<^sub>o rc_u" by (rule has_type.App[OF ro_Z_ty ta])
  have tZ: "\<Gamma> \<turnstile> ?Z : rc_u" unfolding roZ_def by (rule has_type.App[OF tZa Y])
  have tYr: "\<Gamma> \<turnstile> App Y r : Prop" and tYy: "\<Gamma> \<turnstile> App Y y : Prop" by (rule has_type.App[OF Y r], rule has_type.App[OF Y y])
  have tZr: "\<Gamma> \<turnstile> App ?Z r : Prop" by (rule has_type.App[OF tZ r])
  note a1 = u_rc_ac[OF ro_Z_ty ta] and a2 = u_rc_ac[OF tZa Y] and act = ro_actual[of \<Gamma>]
    and zy = roZ_iff[OF ta Y y] and zr = roZ_iff[OF ta Y r] and ui = u_rcUni_inst[OF r y] and el = u_rcR_elim[OF r y tZ]
  have k0: "\<Gamma> \<turnstile>\<^sub>U Imp (Neg (Conj ?a (App Y r))) (Neg (App ?Z r))"
    by (rule u_rc_pc1[OF zr]) (insert ta tYr tZr, (unfold prop_eval.simps)?, blast+)
  note k = u_rc_K[OF k0]
  have tg: "\<Gamma> \<turnstile> Imp roPrem (Imp (rcUni r) (Imp (App rc_p Y) (Imp (App Y y) (Neg (\<box>\<^sub>o (Neg (Conj ?a (App Y r)))))))) : Prop"
    by (intro has_type.Imp has_type.Neg typed_ObjBox has_type.Conj roPrem_ty rcUni_ty r rc_pure_ty Y tYy ta tYr)
  show ?thesis by (rule ro_pc8[OF a1 a2 act zy zr ui el k tg])
    (unfold roPrem_def roHC_def roHF_def roZ_def pp_pure_def prop_eval.simps, blast)
qed

theorem ro_uni_rel: assumes r: "\<Gamma> \<turnstile> r : Prop" and y: "\<Gamma> \<turnstile> y : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (Conj roPrem (rcUni r)) (roR (roa roPhi) r y)"
proof -
  let ?a = "roa roPhi" let ?P = "Conj roPrem (rcUni r)"
  have tP: "\<Gamma> \<turnstile> ?P : Prop" by (intro has_type.Conj roPrem_ty rcUni_ty r)
  have sr: "rc_u # \<Gamma> \<turnstile> shift r : Prop" and sy: "rc_u # \<Gamma> \<turnstile> shift y : Prop" by (intro weaken_shift_type_ok r y)+
  have v0: "rc_u # \<Gamma> \<turnstile> Var 0 : rc_u" by simp
  note st = ro_step1[OF sr sy v0]
  have shP: "shift ?P = Conj roPrem (rcUni (shift r))" by (simp add: rc_sft)
  have s: "rc_u # \<Gamma> \<turnstile>\<^sub>U Imp (shift ?P) (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift y))
      (Neg (\<box>\<^sub>o (Neg (Conj (shift ?a) (App (Var 0) (shift r))))))))"
    unfolding shP roA_closed by (rule u_rc_pc1[OF st]) (insert U_formula[OF st], auto elim!: has_type.cases[of _ "Imp _ _"]
      intro!: has_type.Imp has_type.Conj)
  show ?thesis by (rule roR_intro[OF roA_ty r y tP s])
qed

text \<open>R_a(e, \<not>e) for e = Q_a(r), through the pure operator Y \<circ> Q_a.\<close>
lemma ro_step2: assumes r: "\<Gamma> \<turnstile> r : Prop" and Y: "\<Gamma> \<turnstile> Y : rc_u"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (Conj roPrem (rcUni r)) (Imp (App rc_p Y) (Imp (App Y (Neg (roQ (roa roPhi) r)))
    (Neg (\<box>\<^sub>o (Neg (Conj (roa roPhi) (App Y (roQ (roa roPhi) r))))))))"
proof -
  let ?a = "roa roPhi" let ?e = "roQ (roa roPhi) r" let ?ne = "Neg (roQ (roa roPhi) r)"
  let ?Yc = "roComp Y (roQf (roa roPhi))"
  have ta: "\<Gamma> \<turnstile> ?a : Prop" by (rule roA_ty)
  have te: "\<Gamma> \<turnstile> ?e : Prop" by (rule roQ_ty[OF ta r])
  have tne: "\<Gamma> \<turnstile> ?ne : Prop" using te by blast
  have tQne: "\<Gamma> \<turnstile> roQ ?a ?ne : Prop" by (rule roQ_ty[OF ta tne])
  have tQf: "\<Gamma> \<turnstile> roQf ?a : rc_u" by (rule roQf_ty[OF ta])
  have t0: "\<Gamma> \<turnstile> App ro_Q rc_p : Prop \<rightarrow>\<^sub>o rc_u" by (rule has_type.App[OF ro_Q_ty rc_p_ty])
  have tC1: "\<Gamma> \<turnstile> App ro_comp Y : rc_u \<rightarrow>\<^sub>o rc_u" by (rule has_type.App[OF ro_comp_ty Y])
  have tYc: "\<Gamma> \<turnstile> ?Yc : rc_u" unfolding roComp_def by (rule has_type.App[OF tC1 tQf])
  note a1 = u_rc_ac[OF ro_Q_ty rc_p_ty, of \<Gamma>] and a2 = u_rc_ac[OF t0 ta] and a3 = u_rc_ac[OF ro_comp_ty Y]
    and a4 = u_rc_ac[OF tC1 tQf] and act = ro_actual[of \<Gamma>]
  have tg1: "\<Gamma> \<turnstile> Imp roPrem (Imp (App rc_p Y) (App rc_p ?Yc)) : Prop"
    by (intro has_type.Imp roPrem_ty rc_pure_ty Y tYc)
  have pYc: "\<Gamma> \<turnstile>\<^sub>U Imp roPrem (Imp (App rc_p Y) (App rc_p ?Yc))"
    by (rule u_rc_pc5[OF a1 a2 a3 a4 act tg1]) (unfold roPrem_def roHC_def roHF_def roQf_def roComp_def pp_pure_def prop_eval.simps, blast)
  have c1: "\<Gamma> \<turnstile>\<^sub>U (App ?Yc ?ne \<longleftrightarrow>\<^sub>o App Y (roQ ?a ?ne))" using roComp_iff[OF Y tQf tne] by (simp add: roQ_def)
  have c2: "\<Gamma> \<turnstile>\<^sub>U (App ?Yc r \<longleftrightarrow>\<^sub>o App Y ?e)" using roComp_iff[OF Y tQf r] by (simp add: roQ_def)
  note Fe = ro_Fa[OF r] and Fne = ro_lemC[OF ta te] and Bne = ro_lemB[OF ta tne] and sy = U_eq_sym[OF tQne tne]
    and ll = u_rc_LL[OF tne tQne Y]
  have tYne: "\<Gamma> \<turnstile> App Y ?ne : Prop" and tYcne: "\<Gamma> \<turnstile> App ?Yc ?ne : Prop"
    by (rule has_type.App[OF Y tne], rule has_type.App[OF tYc tne])
  have q1: "\<Gamma> \<turnstile>\<^sub>U Imp (App Y ?ne) (App ?Yc ?ne)"
    by (rule ro_pc6[OF Fe Fne Bne sy ll c1 has_type.Imp[OF tYne tYcne]]) (unfold prop_eval.simps, blast)
  note rr = ro_uni_rel[OF r tne] and el = roR_elim[OF ta r tne tYc]
  have tYe: "\<Gamma> \<turnstile> App Y ?e : Prop" and tYcr: "\<Gamma> \<turnstile> App ?Yc r : Prop" by (rule has_type.App[OF Y te], rule has_type.App[OF tYc r])
  have k0: "\<Gamma> \<turnstile>\<^sub>U Imp (Neg (Conj ?a (App Y ?e))) (Neg (Conj ?a (App ?Yc r)))"
    by (rule u_rc_pc1[OF c2]) (insert ta tYe tYcr, (unfold prop_eval.simps)?, blast+)
  note k = u_rc_K[OF k0]
  have tg: "\<Gamma> \<turnstile> Imp (Conj roPrem (rcUni r)) (Imp (App rc_p Y) (Imp (App Y ?ne) (Neg (\<box>\<^sub>o (Neg (Conj ?a (App Y ?e))))))) : Prop"
    by (intro has_type.Imp has_type.Neg typed_ObjBox has_type.Conj roPrem_ty rcUni_ty r rc_pure_ty Y tYne ta tYe)
  show ?thesis by (rule u_rc_pc5[OF pYc q1 rr el k tg]) (unfold prop_eval.simps, blast)
qed

theorem ro_Rae: assumes r: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (Conj roPrem (rcUni r)) (roR (roa roPhi) (roQ (roa roPhi) r) (Neg (roQ (roa roPhi) r)))"
proof -
  let ?a = "roa roPhi" let ?e = "roQ (roa roPhi) r" let ?P = "Conj roPrem (rcUni r)"
  have ta: "\<Gamma> \<turnstile> ?a : Prop" by (rule roA_ty)
  have te: "\<Gamma> \<turnstile> ?e : Prop" by (rule roQ_ty[OF ta r])
  have tP: "\<Gamma> \<turnstile> ?P : Prop" by (intro has_type.Conj roPrem_ty rcUni_ty r)
  have sr: "rc_u # \<Gamma> \<turnstile> shift r : Prop" by (rule weaken_shift_type_ok[OF r])
  have v0: "rc_u # \<Gamma> \<turnstile> Var 0 : rc_u" by simp
  note st = ro_step2[OF sr v0]
  have s: "rc_u # \<Gamma> \<turnstile>\<^sub>U Imp (shift ?P) (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift (Neg ?e)))
      (Neg (\<box>\<^sub>o (Neg (Conj (shift ?a) (App (Var 0) (shift ?e))))))))"
    using st by (simp add: rc_sft)
  show ?thesis by (rule roR_intro[OF ta te has_type.Neg[OF te] tP s])
qed

text \<open>F_a(e) and the truth of a give C_a(e), whose first conjunct is \<not>R_a(e,\<not>e).\<close>
theorem ro_contra: assumes r: "\<Gamma> \<turnstile> r : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Imp roPrem (Neg (rcUni r))"
proof -
  let ?a = "roa roPhi" let ?e = "roQ (roa roPhi) r"
  have ta: "\<Gamma> \<turnstile> ?a : Prop" by (rule roA_ty)
  have te: "\<Gamma> \<turnstile> ?e : Prop" by (rule roQ_ty[OF ta r])
  have tC: "\<Gamma> \<turnstile> roC ?a ?e : Prop" by (rule roC_ty[OF ta te])
  note Fe = ro_Fa[OF r] and fi = roF_iff[OF ta te] and T = U_modal_T[OF has_type.Imp[OF ta tC], unfolded modal_T_def]
    and act = ro_actual[of \<Gamma>] and Ra = ro_Rae[OF r]
  have tg: "\<Gamma> \<turnstile> Imp roPrem (Neg (rcUni r)) : Prop" by (intro has_type.Imp has_type.Neg roPrem_ty rcUni_ty r)
  show ?thesis by (rule u_rc_pc5[OF Fe fi T act Ra tg]) (unfold roC_def prop_eval.simps, blast)
qed

text \<open>Theorem 1 (local form): the ordinary premises refute the existence of a universal proposition.\<close>
theorem ro_thm1: "[] \<turnstile>\<^sub>U Imp roPrem (Neg rcExUni)"
proof -
  let ?Q = "Neg roPrem"
  have tf: "[Prop] \<turnstile> rcUni (Var 0) : Prop" by (rule rcUni_ty) simp
  have tQ: "\<Gamma> \<turnstile> ?Q : Prop" for \<Gamma> by (intro has_type.Neg roPrem_ty)
  have shq: "shift ?Q = ?Q" by (simp add: rc_sft)
  have c: "[Prop] \<turnstile>\<^sub>U Imp roPrem (Neg (rcUni (Var 0)))" by (rule ro_contra) simp
  have i: "[Prop] \<turnstile>\<^sub>U Imp (rcUni (Var 0)) (shift ?Q)" unfolding shq
    by (rule u_rc_pc1[OF c]) (insert tf tQ[of "[Prop]"] roPrem_ty[of "[Prop]"], (unfold prop_eval.simps)?, blast+)
  note inst = U_proves.Inst[OF tf tQ i]
  have tE: "[] \<turnstile> rcExUni : Prop" by (rule k_ExUni_ty)
  show ?thesis by (rule u_rc_pc1[OF inst[folded rcExUni_def]]) (insert tE roPrem_ty[of "[]"], (unfold prop_eval.simps)?, blast+)
qed

section \<open>4. The statements\<close>

text \<open>The Logical Purity and Application instances used, without PP_u.\<close>
definition roHC0 :: oterm where
  "roHC0 = Conj (pp_pure Prop ObjTrue) (Conj (pp_pure (Prop \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)) ro_and)
     (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o Prop) ro_m) (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) ro_W)
     (Conj (pp_application_closure Prop (Prop \<rightarrow>\<^sub>o Prop)) (Conj (pp_application_closure Prop Prop)
     (Conj (pp_application_closure rc_u Prop) (Conj (pp_application_closure rc_c (rc_u \<rightarrow>\<^sub>o rc_u))
     (pp_application_closure rc_u rc_u))))))))"
definition roLA :: oterm where "roLA = Conj roHC0 roHF"

lemma roLA_ty: "\<Gamma> \<turnstile> roLA : Prop"
  unfolding roLA_def by (intro has_type.Conj roHF_ty) (rule infer_type_sound, simp add: roHC0_def ro_and_def ro_m_def ro_W_def ro_Cl_def
    ObjTrue_def pp_application_closure_def pp_pure_def pp_Pure_def lookup_def)

text \<open>Theorem 1 over H + PE (Lettie's U): Logical Purity and Application instances, and PP_u, imply that
  no proposition is universal.\<close>
theorem ro_thm1_U: "[] \<turnstile>\<^sub>U Imp roLA (Imp (pp_pure rc_c rc_p) (Neg rcExUni))"
proof -
  have tg: "[] \<turnstile> Imp roLA (Imp (pp_pure rc_c rc_p) (Neg rcExUni)) : Prop"
    by (intro has_type.Imp has_type.Neg roLA_ty typed_pp_pure rc_p_ty k_ExUni_ty)
  show ?thesis by (rule u_rc_pc1[OF ro_thm1 tg]) (unfold roLA_def roHC0_def roPrem_def roHC_def prop_eval.simps, blast)
qed

text \<open>Corollary over H + PE: with unique fundamentality (hence a fundamental proposition) and unary
  Recombination, PP_u fails. rcH5 is Lettie's: Logical Purity at the negator, Application at (u, u),
  and unary Recombination. No Exhaustion, Persistence or Purity of Fun.\<close>
theorem ro_cor_U: "[] \<turnstile>\<^sub>U Imp roLA (Imp (pp_unique_fundamental Prop) (Imp rcH5 (Neg pp_target_PP)))"
proof -
  have tg: "[] \<turnstile> Imp roLA (Imp (pp_unique_fundamental Prop) (Imp rcH5 (Neg pp_target_PP))) : Prop"
    by (intro has_type.Imp has_type.Neg roLA_ty rcH5_ty typed_pp_unique_fundamental typed_pp_target_PP)
  show ?thesis by (rule u_rc_pc3[OF ro_thm1_U u_fun_ExUni lo_EF_of_UF tg])
    (unfold pp_target_PP_def pp_purity_of_pure_def prop_eval.simps, blast)
qed

text \<open>The corollary as the hand proof states it: a fundamental proposition exists (k_EF), with unary
  Recombination.\<close>
theorem ro_cor_EF_U: "[] \<turnstile>\<^sub>U Imp roLA (Imp k_EF (Imp rcH5 (Neg pp_target_PP)))"
proof -
  have tE: "[] \<turnstile> k_EF : Prop" unfolding k_EF_def by (rule has_type.Exists, rule typed_pp_fun) simp
  have tg: "[] \<turnstile> Imp roLA (Imp k_EF (Imp rcH5 (Neg pp_target_PP))) : Prop"
    by (intro has_type.Imp has_type.Neg roLA_ty rcH5_ty tE typed_pp_target_PP)
  show ?thesis by (rule u_rc_pc2[OF ro_thm1_U u_fun_ExUni tg])
    (unfold pp_target_PP_def pp_purity_of_pure_def prop_eval.simps, blast)
qed

subsection \<open>The same results in the repository's ordinary-premise relation over C\<close>

lemma ro_L_m: "[] ; T \<turnstile>\<^sub>CEV\<^sub>s A \<Longrightarrow> [] \<turnstile>\<^sub>CEV Imp A B \<Longrightarrow> [] ; T \<turnstile>\<^sub>CEV\<^sub>s B"
  by (rule CEV_set_derivable.Derive_MP[OF _ CEV_set_derivable.Theorem])

lemma ro_L_cj: assumes a: "[] ; T \<turnstile>\<^sub>CEV\<^sub>s A" and b: "[] ; T \<turnstile>\<^sub>CEV\<^sub>s B" shows "[] ; T \<turnstile>\<^sub>CEV\<^sub>s Conj A B"
proof -
  have ta: "[] \<turnstile> A : Prop" and tb: "[] \<turnstile> B : Prop" by (rule CEV_set_derivable_formula[OF a], rule CEV_set_derivable_formula[OF b])
  have c: "[] \<turnstile>\<^sub>CEV Imp A (Imp B (Conj A B))"
    by (rule CEV_prop_tautology) (insert ta tb, unfold prop_tautology_def prop_eval.simps, blast)
  show ?thesis by (rule CEV_set_derivable.Derive_MP[OF b ro_L_m[OF a c]])
qed

text \<open>Any premise set containing the Logical Purity and Application schemas derives the premises roLA.\<close>
lemma ro_LA_derivable:
  assumes LP: "pp_purity_schema \<subseteq> S" and AC: "pp_application_closure_schema \<subseteq> S"
  shows "[] ; S \<turnstile>\<^sub>CEV\<^sub>s roLA"
proof -
  have lp: "[] ; S \<turnstile>\<^sub>CEV\<^sub>s pp_pure \<sigma> M" if "[] \<turnstile> M : \<sigma>" "consts_of M = {}" for \<sigma> M
  proof -
    have "pp_pure \<sigma> M \<in> S" using LP that unfolding pp_purity_schema_def pp_logical_vocabulary_def by blast
    then show ?thesis by (rule CEV_set_derivable.Assumption) (rule typed_pp_pure[OF that(1)])
  qed
  have ac: "[] ; S \<turnstile>\<^sub>CEV\<^sub>s pp_application_closure \<sigma> \<tau>" for \<sigma> \<tau>
  proof -
    have "pp_application_closure \<sigma> \<tau> \<in> S" using AC unfolding pp_application_closure_schema_def by blast
    then show ?thesis by (rule CEV_set_derivable.Assumption) (rule typed_pp_application_closure)
  qed
  have top: "[] ; S \<turnstile>\<^sub>CEV\<^sub>s pp_pure Prop ObjTrue" by (rule lp[OF typed_ObjTrue]) (simp add: ObjTrue_def)
  show ?thesis unfolding roLA_def roHC0_def roHF_def
    by (intro ro_L_cj top ac lp ro_and_ty ro_m_ty ro_W_ty ro_Phi_ty ro_P_ty ro_Pp_ty ro_Q_ty ro_Z_ty ro_comp_ty
      ro_consts ro_rel_consts ro_fin_consts)
qed

definition ro_T0P :: "oterm set" where
  "ro_T0P = insert pp_target_PP (pp_purity_schema \<union> pp_application_closure_schema)"

text \<open>Theorem 1 in the ordinary-premise relation over C.\<close>
theorem ro_thm1_CEVs: "[] ; ro_T0P \<turnstile>\<^sub>CEV\<^sub>s Neg rcExUni"
proof -
  have la: "[] ; ro_T0P \<turnstile>\<^sub>CEV\<^sub>s roLA" by (rule ro_LA_derivable) (auto simp: ro_T0P_def)
  have pp: "[] ; ro_T0P \<turnstile>\<^sub>CEV\<^sub>s pp_pure rc_c rc_p"
    by (rule CEV_set_derivable.Assumption) (simp_all add: ro_T0P_def pp_target_PP_def pp_purity_of_pure_def typed_pp_pure rc_p_ty)
  show ?thesis by (rule CEV_set_derivable.Derive_MP[OF pp ro_L_m[OF la U_sub_CEV[OF ro_thm1_U]]])
qed

text \<open>The Recombination corollary for any premise set with Logical Purity, Application, unique
  fundamentality and unary Recombination.\<close>
lemma ro_cor_set:
  assumes LP: "pp_purity_schema \<subseteq> S" and AC: "pp_application_closure_schema \<subseteq> S"
    and UF: "pp_unique_fundamental Prop \<in> S" and R1: "pp_unary_recombination \<in> S"
  shows "[] ; S \<turnstile>\<^sub>CEV\<^sub>s Neg pp_target_PP"
proof -
  have la: "[] ; S \<turnstile>\<^sub>CEV\<^sub>s roLA" by (rule ro_LA_derivable[OF LP AC])
  have uf: "[] ; S \<turnstile>\<^sub>CEV\<^sub>s pp_unique_fundamental Prop" by (rule CEV_set_derivable.Assumption[OF UF typed_pp_unique_fundamental])
  have kc: "[] ; S \<turnstile>\<^sub>CEV\<^sub>s pp_pure (rc_u \<rightarrow>\<^sub>o rc_u) k_C"
  proof -
    have "pp_pure (rc_u \<rightarrow>\<^sub>o rc_u) k_C \<in> S" using LP k_C_ty[of "[]"] k_C_consts unfolding pp_purity_schema_def pp_logical_vocabulary_def by blast
    then show ?thesis by (rule CEV_set_derivable.Assumption) (rule typed_pp_pure[OF k_C_ty])
  qed
  have uu: "[] ; S \<turnstile>\<^sub>CEV\<^sub>s pp_application_closure rc_u rc_u"
    using AC by (intro CEV_set_derivable.Assumption typed_pp_application_closure) (auto simp: pp_application_closure_schema_def)
  have r1: "[] ; S \<turnstile>\<^sub>CEV\<^sub>s pp_unary_recombination" by (rule CEV_set_derivable.Assumption[OF R1 typed_pp_unary_recombination])
  have h5: "[] ; S \<turnstile>\<^sub>CEV\<^sub>s rcH5" unfolding rcH5_def by (intro ro_L_cj kc uu r1)
  note c = U_sub_CEV[OF ro_cor_U]
  show ?thesis by (rule CEV_set_derivable.Derive_MP[OF h5 CEV_set_derivable.Derive_MP[OF uf ro_L_m[OF la c]]])
qed

text \<open>Goodman's question, Recombination-only reading, with ordinary premises: the repository's
  Recombination background (Logical Purity, Application, unique fundamentality, no fundamentals
  at other types, zeroary and unary Recombination, no Exhaustion) refutes PP_u.\<close>
theorem ro_recombination_refutes_PP: "[] ; pp_recombination_background_axioms \<turnstile>\<^sub>CEV\<^sub>s Neg pp_target_PP"
  by (rule ro_cor_set) (auto simp: pp_recombination_background_axioms_def pp_background_axioms_def)

theorem ro_recombination_PP_inconsistent: "[] ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sub>s ObjFalse"
proof -
  have n: "[] ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sub>s Neg pp_target_PP"
    by (rule ro_cor_set) (auto simp: pp_recombination_PP_axioms_def pp_recombination_background_axioms_def pp_background_axioms_def)
  have p: "[] ; pp_recombination_PP_axioms \<turnstile>\<^sub>CEV\<^sub>s pp_target_PP"
    by (rule CEV_set_derivable.Assumption) (simp_all add: pp_recombination_PP_axioms_def typed_pp_target_PP)
  have t: "[] \<turnstile>\<^sub>CEV Imp pp_target_PP (Imp (Neg pp_target_PP) ObjFalse)"
    by (rule CEV_prop_tautology) (insert typed_pp_target_PP typed_ObjFalse[of "[]"], unfold prop_tautology_def prop_eval.simps, blast)
  show ?thesis by (rule CEV_set_derivable.Derive_MP[OF n ro_L_m[OF p t]])
qed

end
