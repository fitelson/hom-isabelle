theory Goodman_RecOnly_Closure
  imports PoP_Main.PoP_G100_Kernel
begin

text \<open>Recombination without Exhaustion: the closure lemma for pure truths (Lemmas 1 and 2 in Section 3
  and Lemma 10 in Section 6 of reports/RECOMBINATION_WITHOUT_EXHAUSTION_HAND_PROOF_2026-11-11). Built on Jacob Lettie's kernel
  (PoP_Main, unmodified). Calculus: Lettie's U. The parameter \<pi> is the constant rc_p;
  the operator \<Theta> is an arbitrary closed term T of type u. Every added principle used for Lemma 10
  is an antecedent of the theorem, so no added principle is necessitated.\<close>

declare has_type.App[rule del]

section \<open>0. Tools\<close>

lemma ro_lift_Var: "lift_subst Var = Var"
proof (rule ext)
  fix n show "lift_subst Var n = Var n" by (cases n) simp_all
qed

lemma ro_subst_Var[simp]: "subst Var M = M"
  by (induction M) (simp_all add: ro_lift_Var)

lemma ro_subst0_shift[simp]: "subst0 x (shift M) = M"
  by (simp add: subst0_def shift_def rc_subst_rename)

lemma ro_subst0_shift'[simp]: "subst (case_nat x Var) (shift M) = M"
  using ro_subst0_shift unfolding subst0_def .

lemma ro_subst0_rename[simp]: "subst (case_nat x Var) (rename Suc M) = M"
  using ro_subst0_shift unfolding subst0_def shift_def .

lemma ro_shift_true[simp]: "shift ObjTrue = ObjTrue" by (simp add: ObjTrue_def shift_def)
lemma ro_subst_true[simp]: "subst s ObjTrue = ObjTrue" by (simp add: ObjTrue_def)
lemma ro_rename_true[simp]: "rename \<rho> ObjTrue = ObjTrue" by (simp add: ObjTrue_def)

lemma ro_ui: assumes "\<sigma> # \<Gamma> \<turnstile> A : Prop" and "\<Gamma> \<turnstile> t : \<sigma>" and "subst0 t A = B"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (Forall \<sigma> A) B"
  using U_proves.H[OF H_proves.UI[OF assms(1,2)]] assms(3) by simp

lemma ro_gen: assumes P: "\<Gamma> \<turnstile> P : Prop" and s: "shift P = P" and h: "\<sigma> # \<Gamma> \<turnstile>\<^sub>U Imp P Q"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp P (Forall \<sigma> Q)"
proof -
  have tQ: "\<sigma> # \<Gamma> \<turnstile> Q : Prop" using U_formula[OF h] by (auto elim: has_type.cases)
  show ?thesis by (rule U_proves.Gen[OF P tQ]) (simp add: s h)
qed

lemma ro_gen0: assumes h: "\<sigma> # \<Gamma> \<turnstile>\<^sub>U Q" shows "\<Gamma> \<turnstile>\<^sub>U Forall \<sigma> Q"
proof -
  have tQ: "\<sigma> # \<Gamma> \<turnstile> Q : Prop" by (rule U_formula[OF h])
  have i: "\<sigma> # \<Gamma> \<turnstile>\<^sub>U Imp ObjTrue Q" by (rule u_rc_pc1[OF h has_type.Imp[OF typed_ObjTrue tQ]]) simp
  have "\<Gamma> \<turnstile>\<^sub>U Imp ObjTrue (Forall \<sigma> Q)" by (rule ro_gen[OF typed_ObjTrue ro_shift_true i])
  then show ?thesis by (rule U_proves.MP[OF U_true])
qed

lemma ro_pc6: assumes a1: "\<Gamma> \<turnstile>\<^sub>U A1" and a2: "\<Gamma> \<turnstile>\<^sub>U A2" and a3: "\<Gamma> \<turnstile>\<^sub>U A3" and a4: "\<Gamma> \<turnstile>\<^sub>U A4"
  and a5: "\<Gamma> \<turnstile>\<^sub>U A5" and a6: "\<Gamma> \<turnstile>\<^sub>U A6" and b: "\<Gamma> \<turnstile> B : Prop"
  and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow> prop_eval v A4 \<Longrightarrow> prop_eval v A5 \<Longrightarrow>
    prop_eval v A6 \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> \<turnstile>\<^sub>U B"
proof -
  have "\<Gamma> \<turnstile>\<^sub>U Imp A6 B" by (rule u_rc_pc5[OF a1 a2 a3 a4 a5 has_type.Imp[OF U_formula[OF a6] b]]) (use t in simp)
  then show ?thesis by (rule U_proves.MP[OF a6])
qed

lemma ro_pc7: assumes a1: "\<Gamma> \<turnstile>\<^sub>U A1" and a2: "\<Gamma> \<turnstile>\<^sub>U A2" and a3: "\<Gamma> \<turnstile>\<^sub>U A3" and a4: "\<Gamma> \<turnstile>\<^sub>U A4"
  and a5: "\<Gamma> \<turnstile>\<^sub>U A5" and a6: "\<Gamma> \<turnstile>\<^sub>U A6" and a7: "\<Gamma> \<turnstile>\<^sub>U A7" and b: "\<Gamma> \<turnstile> B : Prop"
  and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow> prop_eval v A4 \<Longrightarrow> prop_eval v A5 \<Longrightarrow>
    prop_eval v A6 \<Longrightarrow> prop_eval v A7 \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> \<turnstile>\<^sub>U B"
proof -
  have "\<Gamma> \<turnstile>\<^sub>U Imp A7 B" by (rule ro_pc6[OF a1 a2 a3 a4 a5 a6 has_type.Imp[OF U_formula[OF a7] b]]) (use t in simp)
  then show ?thesis by (rule U_proves.MP[OF a7])
qed

lemma ro_pc8: assumes a1: "\<Gamma> \<turnstile>\<^sub>U A1" and a2: "\<Gamma> \<turnstile>\<^sub>U A2" and a3: "\<Gamma> \<turnstile>\<^sub>U A3" and a4: "\<Gamma> \<turnstile>\<^sub>U A4"
  and a5: "\<Gamma> \<turnstile>\<^sub>U A5" and a6: "\<Gamma> \<turnstile>\<^sub>U A6" and a7: "\<Gamma> \<turnstile>\<^sub>U A7" and a8: "\<Gamma> \<turnstile>\<^sub>U A8" and b: "\<Gamma> \<turnstile> B : Prop"
  and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow> prop_eval v A4 \<Longrightarrow> prop_eval v A5 \<Longrightarrow>
    prop_eval v A6 \<Longrightarrow> prop_eval v A7 \<Longrightarrow> prop_eval v A8 \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> \<turnstile>\<^sub>U B"
proof -
  have "\<Gamma> \<turnstile>\<^sub>U Imp A8 B" by (rule ro_pc7[OF a1 a2 a3 a4 a5 a6 a7 has_type.Imp[OF U_formula[OF a8] b]]) (use t in simp)
  then show ?thesis by (rule U_proves.MP[OF a8])
qed

text \<open>Beta for a closed combinator of one, two or three arguments.\<close>

lemma ro_be1: assumes L: "\<Gamma> \<turnstile> Lam \<sigma>1 B : \<sigma>1 \<rightarrow>\<^sub>o \<tau>" and a1: "\<Gamma> \<turnstile> a1 : \<sigma>1"
  shows "beta_eta_equiv \<Gamma> \<tau> (App (Lam \<sigma>1 B) a1) (subst0 a1 B)"
  by (rule rc_be1[OF has_type.App[OF L a1]])

lemma ro_be2: assumes L: "\<Gamma> \<turnstile> Lam \<sigma>1 (Lam \<sigma>2 B) : \<sigma>1 \<rightarrow>\<^sub>o (\<sigma>2 \<rightarrow>\<^sub>o \<tau>)" and a1: "\<Gamma> \<turnstile> a1 : \<sigma>1"
  and a2: "\<Gamma> \<turnstile> a2 : \<sigma>2"
  shows "beta_eta_equiv \<Gamma> \<tau> (App (App (Lam \<sigma>1 (Lam \<sigma>2 B)) a1) a2)
    (subst0 a2 (subst (lift_subst (case_nat a1 Var)) B))"
proof -
  have s1: "beta_eta_equiv \<Gamma> (\<sigma>2 \<rightarrow>\<^sub>o \<tau>) (App (Lam \<sigma>1 (Lam \<sigma>2 B)) a1) (Lam \<sigma>2 (subst (lift_subst (case_nat a1 Var)) B))"
    using ro_be1[OF L a1] by (simp add: subst0_def)
  have s2: "beta_eta_equiv \<Gamma> \<tau> (App (App (Lam \<sigma>1 (Lam \<sigma>2 B)) a1) a2) (App (Lam \<sigma>2 (subst (lift_subst (case_nat a1 Var)) B)) a2)"
    by (rule rc_be_app[OF s1 refl a2])
  show ?thesis by (rule beta_eta_equiv.Trans[OF s2 rc_be1[OF beta_eta_equiv_right_type[OF s2]]])
qed

lemma ro_be3: assumes L: "\<Gamma> \<turnstile> Lam \<sigma>1 (Lam \<sigma>2 (Lam \<sigma>3 B)) : \<sigma>1 \<rightarrow>\<^sub>o (\<sigma>2 \<rightarrow>\<^sub>o (\<sigma>3 \<rightarrow>\<^sub>o \<tau>))"
  and a1: "\<Gamma> \<turnstile> a1 : \<sigma>1" and a2: "\<Gamma> \<turnstile> a2 : \<sigma>2" and a3: "\<Gamma> \<turnstile> a3 : \<sigma>3"
  shows "beta_eta_equiv \<Gamma> \<tau> (App (App (App (Lam \<sigma>1 (Lam \<sigma>2 (Lam \<sigma>3 B))) a1) a2) a3)
    (subst0 a3 (subst (lift_subst (case_nat a2 Var)) (subst (lift_subst (lift_subst (case_nat a1 Var))) B)))"
proof -
  have s1: "beta_eta_equiv \<Gamma> (\<sigma>2 \<rightarrow>\<^sub>o (\<sigma>3 \<rightarrow>\<^sub>o \<tau>)) (App (Lam \<sigma>1 (Lam \<sigma>2 (Lam \<sigma>3 B))) a1)
      (Lam \<sigma>2 (Lam \<sigma>3 (subst (lift_subst (lift_subst (case_nat a1 Var))) B)))"
    using ro_be1[OF L a1] by (simp add: subst0_def)
  have t1: "\<Gamma> \<turnstile> Lam \<sigma>2 (Lam \<sigma>3 (subst (lift_subst (lift_subst (case_nat a1 Var))) B)) : \<sigma>2 \<rightarrow>\<^sub>o (\<sigma>3 \<rightarrow>\<^sub>o \<tau>)"
    by (rule beta_eta_equiv_right_type[OF s1])
  have s2: "beta_eta_equiv \<Gamma> (\<sigma>3 \<rightarrow>\<^sub>o \<tau>) (App (App (Lam \<sigma>1 (Lam \<sigma>2 (Lam \<sigma>3 B))) a1) a2)
      (App (Lam \<sigma>2 (Lam \<sigma>3 (subst (lift_subst (lift_subst (case_nat a1 Var))) B))) a2)"
    by (rule rc_be_app[OF s1 refl a2])
  have s3: "beta_eta_equiv \<Gamma> (\<sigma>3 \<rightarrow>\<^sub>o \<tau>) (App (App (Lam \<sigma>1 (Lam \<sigma>2 (Lam \<sigma>3 B))) a1) a2)
      (Lam \<sigma>3 (subst (lift_subst (case_nat a2 Var)) (subst (lift_subst (lift_subst (case_nat a1 Var))) B)))"
    using beta_eta_equiv.Trans[OF s2 ro_be1[OF t1 a2]] by (simp add: subst0_def)
  have s4: "beta_eta_equiv \<Gamma> \<tau> (App (App (App (Lam \<sigma>1 (Lam \<sigma>2 (Lam \<sigma>3 B))) a1) a2) a3)
      (App (Lam \<sigma>3 (subst (lift_subst (case_nat a2 Var)) (subst (lift_subst (lift_subst (case_nat a1 Var))) B))) a3)"
    by (rule rc_be_app[OF s3 refl a3])
  show ?thesis by (rule beta_eta_equiv.Trans[OF s4 rc_be1[OF beta_eta_equiv_right_type[OF s4]]])
qed

lemma ro_pure_be: assumes "beta_eta_equiv \<Gamma> \<sigma> M M'"
  shows "\<Gamma> \<turnstile>\<^sub>U (pp_pure \<sigma> M \<longleftrightarrow>\<^sub>o pp_pure \<sigma> M')"
  unfolding pp_pure_def by (rule U_beta_eta_equiv[OF k7_be_arg[OF assms typed_pp_Pure]])

section \<open>1. The terms m, Cl, W, G and conjunction\<close>

definition ro_and :: oterm where "ro_and = Lam Prop (Lam Prop (Conj (Var 1) (Var 0)))"

text \<open>m(S) := \<forall>p (S p \<longrightarrow> p).\<close>
definition ro_m :: oterm where "ro_m = Lam rc_u (Forall Prop (Imp (App (Var 1) (Var 0)) (Var 0)))"

text \<open>Cl(X), with the parameters c (for \<pi>) and T (for \<Theta>) abstracted: (Cl1) to (Cl5).\<close>
definition ro_Cl :: oterm where
  "ro_Cl = Lam rc_c (Lam rc_u (Lam rc_u
     (Conj (App (Var 0) ObjTrue)
     (Conj (Forall Prop (Forall Prop (Imp (Conj (App (Var 2) (Var 1)) (App (Var 2) (Var 0))) (App (Var 2) (Conj (Var 1) (Var 0))))))
     (Conj (Forall Prop (Imp (App (Var 1) (Var 0)) (App (Var 1) (App (Var 2) (Var 0)))))
     (Conj (Forall rc_u (Imp (App (Var 3) (Var 0)) (App (Var 1) (App (Var 3) (Var 0)))))
           (Forall rc_u (Imp (Conj (App (Var 3) (Var 0)) (Forall Prop (Imp (App (Var 1) (Var 0)) (App (Var 2) (Var 0)))))
              (App (Var 1) (App ro_m (Var 0)))))))))))"

text \<open>W := \<lambda>q. \<forall>X (Cl(X) \<longrightarrow> X q), with c and T abstracted.\<close>
definition ro_W :: oterm where
  "ro_W = Lam rc_c (Lam rc_u (Lam Prop (Forall rc_u (Imp (App (App (App ro_Cl (Var 3)) (Var 2)) (Var 0)) (App (Var 0) (Var 1))))))"

text \<open>G := \<lambda>p. Pure_t(p) \<and> p. Not assumed pure.\<close>
definition ro_G :: oterm where "ro_G = Lam Prop (Conj (pp_pure Prop (Var 0)) (Var 0))"

lemma ro_and_ty: "\<Gamma> \<turnstile> ro_and : Prop \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)"
  by (rule infer_type_sound) (simp add: ro_and_def lookup_def)
lemma ro_m_ty: "\<Gamma> \<turnstile> ro_m : rc_u \<rightarrow>\<^sub>o Prop"
  by (rule infer_type_sound) (simp add: ro_m_def lookup_def)
lemma ro_Cl_ty: "\<Gamma> \<turnstile> ro_Cl : rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o Prop))"
  by (rule infer_type_sound) (simp add: ro_Cl_def ro_m_def ObjTrue_def lookup_def)
lemma ro_W_ty: "\<Gamma> \<turnstile> ro_W : rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)"
  by (rule infer_type_sound) (simp add: ro_W_def ro_Cl_def ro_m_def ObjTrue_def lookup_def)
lemma ro_G_ty: "\<Gamma> \<turnstile> ro_G : rc_u"
  by (rule infer_type_sound) (simp add: ro_G_def pp_pure_def pp_Pure_def lookup_def)

lemma ro_consts: "consts_of ro_and = {}" "consts_of ro_m = {}" "consts_of ro_Cl = {}" "consts_of ro_W = {}"
  by (simp_all add: ro_and_def ro_m_def ro_Cl_def ro_W_def ObjTrue_def)

lemma ro_closed[simp]:
  "subst s ro_and = ro_and" "subst s ro_m = ro_m" "subst s ro_Cl = ro_Cl" "subst s ro_W = ro_W" "subst s ro_G = ro_G"
  by (simp_all add: ro_and_def ro_m_def ro_Cl_def ro_W_def ro_G_def pp_pure_def pp_Pure_def eval_nat_numeral)

lemma ro_rename_closed[simp]:
  "rename \<rho> ro_and = ro_and" "rename \<rho> ro_m = ro_m" "rename \<rho> ro_Cl = ro_Cl" "rename \<rho> ro_W = ro_W"
  "rename \<rho> ro_G = ro_G"
  by (simp_all add: ro_and_def ro_m_def ro_Cl_def ro_W_def ro_G_def pp_pure_def pp_Pure_def eval_nat_numeral)

lemma ro_shift_closed[simp]:
  "shift ro_and = ro_and" "shift ro_m = ro_m" "shift ro_Cl = ro_Cl" "shift ro_W = ro_W" "shift ro_G = ro_G"
  by (simp_all add: shift_def)

lemma ro_rename_p[simp]: "rename \<rho> rc_p = rc_p" by (simp add: pp_Pure_def)

definition rom :: "oterm \<Rightarrow> oterm" where "rom S = App ro_m S"

lemma rom_ty: "\<Gamma> \<turnstile> S : rc_u \<Longrightarrow> \<Gamma> \<turnstile> rom S : Prop"
  unfolding rom_def by (rule has_type.App[OF ro_m_ty])

lemma ro_m_iff: assumes S: "\<Gamma> \<turnstile> S : rc_u"
  shows "\<Gamma> \<turnstile>\<^sub>U (rom S \<longleftrightarrow>\<^sub>o Forall Prop (Imp (App (shift S) (Var 0)) (Var 0)))"
proof -
  have "beta_eta_equiv \<Gamma> Prop (rom S) (Forall Prop (Imp (App (shift S) (Var 0)) (Var 0)))"
    using ro_be1[OF ro_m_ty[unfolded ro_m_def] S] by (simp add: rom_def ro_m_def subst0_def flip: shift_def)
  then show ?thesis by (rule U_beta_eta_equiv)
qed

lemma ro_G_iff: assumes p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U (App ro_G p \<longleftrightarrow>\<^sub>o Conj (pp_pure Prop p) p)"
proof -
  have "beta_eta_equiv \<Gamma> Prop (App ro_G p) (Conj (pp_pure Prop p) p)"
    using ro_be1[OF ro_G_ty[unfolded ro_G_def] p] by (simp add: ro_G_def subst0_def pp_pure_def pp_Pure_def)
  then show ?thesis by (rule U_beta_eta_equiv)
qed

lemma ro_and_be: assumes p: "\<Gamma> \<turnstile> p : Prop" and q: "\<Gamma> \<turnstile> q : Prop"
  shows "beta_eta_equiv \<Gamma> Prop (App (App ro_and p) q) (Conj p q)"
  using ro_be2[OF ro_and_ty[unfolded ro_and_def] p q] by (simp add: ro_and_def subst0_def)


lemma rom_subst[simp]: "subst s (rom M) = rom (subst s M)" by (simp add: rom_def)
lemma rom_rename[simp]: "rename \<rho> (rom M) = rom (rename \<rho> M)" by (simp add: rom_def)
lemma rom_shift[simp]: "shift (rom M) = rom (shift M)" by (simp add: rom_def shift_def)

section \<open>2. Cl, W and a, for a closed operator T (the hand proof's \<Theta>)\<close>

definition roCl :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where "roCl T X = App (App (App ro_Cl rc_p) T) X"
definition roW :: "oterm \<Rightarrow> oterm" where "roW T = App (App ro_W rc_p) T"
definition roa :: "oterm \<Rightarrow> oterm" where "roa T = Conj (rom (roW T)) (App rc_p (roW T))"

definition roCl1 :: "oterm \<Rightarrow> oterm" where "roCl1 X = App X ObjTrue"
definition roCl2 :: "oterm \<Rightarrow> oterm" where
  "roCl2 X = Forall Prop (Forall Prop (Imp (Conj (App (shift (shift X)) (Var 1)) (App (shift (shift X)) (Var 0)))
     (App (shift (shift X)) (Conj (Var 1) (Var 0)))))"
definition roCl3 :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "roCl3 T X = Forall Prop (Imp (App (shift X) (Var 0)) (App (shift X) (App T (Var 0))))"
definition roCl4 :: "oterm \<Rightarrow> oterm" where
  "roCl4 X = Forall rc_u (Imp (App rc_p (Var 0)) (App (shift X) (App rc_p (Var 0))))"
definition roCl5 :: "oterm \<Rightarrow> oterm" where
  "roCl5 X = Forall rc_u (Imp (Conj (App rc_p (Var 0)) (Forall Prop (Imp (App (Var 1) (Var 0)) (App (shift (shift X)) (Var 0)))))
     (App (shift X) (rom (Var 0))))"
definition roClB :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "roClB T X = Conj (roCl1 X) (Conj (roCl2 X) (Conj (roCl3 T X) (Conj (roCl4 X) (roCl5 X))))"

text \<open>The ordinary premises of Lemma 10: Logical Purity at \<top>, conjunction, m and W; Application at
  (t, t\<rightarrow>t), (t, t), (u, t), (u\<rightarrow>t, u\<rightarrow>u) and (u, u); and PP_u.\<close>
definition roHC :: oterm where
  "roHC = Conj (pp_pure Prop ObjTrue) (Conj (pp_pure (Prop \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)) ro_and)
     (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o Prop) ro_m) (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) ro_W)
     (Conj (pp_application_closure Prop (Prop \<rightarrow>\<^sub>o Prop)) (Conj (pp_application_closure Prop Prop)
     (Conj (pp_application_closure rc_u Prop) (Conj (pp_application_closure rc_c (rc_u \<rightarrow>\<^sub>o rc_u))
     (Conj (pp_application_closure rc_u rc_u) (pp_pure rc_c rc_p)))))))))"

text \<open>\<Theta> preserves pure truths: \<forall>p ((Pure_t(p) \<and> p) \<longrightarrow> \<Theta> p).\<close>
definition roPres :: "oterm \<Rightarrow> oterm" where
  "roPres T = Forall Prop (Imp (Conj (pp_pure Prop (Var 0)) (Var 0)) (App T (Var 0)))"

definition roH :: "oterm \<Rightarrow> oterm" where "roH T = Conj roHC (Conj (pp_pure rc_u T) (roPres T))"

lemma roHC_ty: "\<Gamma> \<turnstile> roHC : Prop"
  by (rule infer_type_sound) (simp add: roHC_def ro_and_def ro_m_def ro_W_def ro_Cl_def ObjTrue_def pp_application_closure_def
    pp_pure_def pp_Pure_def lookup_def)

lemma roHC_shift[simp]: "shift roHC = roHC"
  by (simp add: roHC_def pp_application_closure_def pp_pure_def pp_Pure_def shift_def)

context
  fixes T :: oterm
  assumes T_ty: "\<And>\<Gamma>. \<Gamma> \<turnstile> T : rc_u" and T_subst: "\<And>s. subst s T = T" and T_rename: "\<And>\<rho>. rename \<rho> T = T"
begin

lemma T_shift: "shift T = T" by (simp add: shift_def T_rename)

lemma T_inf: "infer_type \<Gamma> T = Some rc_u" by (rule infer_type_complete[OF T_ty])

lemma roW_ty: "\<Gamma> \<turnstile> roW T : rc_u" unfolding roW_def by (rule has_type.App[OF has_type.App[OF ro_W_ty rc_p_ty] T_ty])
lemma roCl_ty: "\<Gamma> \<turnstile> X : rc_u \<Longrightarrow> \<Gamma> \<turnstile> roCl T X : Prop"
  unfolding roCl_def by (rule has_type.App[OF has_type.App[OF has_type.App[OF ro_Cl_ty rc_p_ty] T_ty]])
lemma roa_ty: "\<Gamma> \<turnstile> roa T : Prop"
  unfolding roa_def by (intro has_type.Conj rom_ty roW_ty rc_pure_ty)

lemma roW_closed[simp]: "subst s (roW T) = roW T" "rename \<rho> (roW T) = roW T" "shift (roW T) = roW T"
  by (simp_all add: roW_def T_subst T_rename shift_def)
lemma roa_closed[simp]: "subst s (roa T) = roa T" "rename \<rho> (roa T) = roa T" "shift (roa T) = roa T"
  by (simp_all add: roa_def shift_def)
lemma roCl_subst[simp]: "subst s (roCl T X) = roCl T (subst s X)" "shift (roCl T X) = roCl T (shift X)"
  "rename \<rho> (roCl T X) = roCl T (rename \<rho> X)"
  by (simp_all add: roCl_def T_subst T_rename shift_def)

lemma roPres_closed[simp]: "shift (roPres T) = roPres T"
  by (simp add: roPres_def pp_pure_def pp_Pure_def shift_def T_rename)
lemma roH_closed[simp]: "shift (roH T) = roH T"
  by (simp add: roH_def rc_sft pp_pure_def pp_Pure_def T_shift)
lemma roPres_ty: "\<Gamma> \<turnstile> roPres T : Prop"
  by (rule infer_type_sound) (simp add: roPres_def pp_pure_def pp_Pure_def lookup_def T_inf)
lemma roH_ty: "\<Gamma> \<turnstile> roH T : Prop"
  unfolding roH_def by (intro has_type.Conj roHC_ty roPres_ty typed_pp_pure T_ty)

subsection \<open>Unfolding Cl and W\<close>

lemma ro_Cl_be: assumes X: "\<Gamma> \<turnstile> X : rc_u" shows "beta_eta_equiv \<Gamma> Prop (roCl T X) (roClB T X)"
  using ro_be3[OF ro_Cl_ty[unfolded ro_Cl_def] rc_p_ty T_ty X]
  unfolding roCl_def ro_Cl_def
  by (simp add: roClB_def roCl1_def roCl2_def roCl3_def roCl4_def roCl5_def rom_def subst0_def T_subst T_rename T_shift
    eval_nat_numeral flip: shift_def)

lemma ro_Cl_iff: assumes X: "\<Gamma> \<turnstile> X : rc_u" shows "\<Gamma> \<turnstile>\<^sub>U (roCl T X \<longleftrightarrow>\<^sub>o roClB T X)"
  by (rule U_beta_eta_equiv[OF ro_Cl_be[OF X]])

lemma ro_W_iff: assumes q: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U (App (roW T) q \<longleftrightarrow>\<^sub>o Forall rc_u (Imp (roCl T (Var 0)) (App (Var 0) (shift q))))"
proof -
  have "beta_eta_equiv \<Gamma> Prop (App (roW T) q) (Forall rc_u (Imp (roCl T (Var 0)) (App (Var 0) (shift q))))"
    using ro_be3[OF ro_W_ty[unfolded ro_W_def] rc_p_ty T_ty q]
    unfolding roW_def ro_W_def roCl_def
    by (simp add: subst0_def T_subst T_rename T_shift eval_nat_numeral flip: shift_def)
  then show ?thesis by (rule U_beta_eta_equiv)
qed

lemma ro_W_elim: assumes X: "\<Gamma> \<turnstile> X : rc_u" and q: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (App (roW T) q) (Imp (roCl T X) (App X q))"
proof -
  note i = ro_W_iff[OF q]
  have tA: "rc_u # \<Gamma> \<turnstile> Imp (roCl T (Var 0)) (App (Var 0) (shift q)) : Prop"
    by (intro has_type.Imp roCl_ty has_type.App[OF _ weaken_shift_type_ok[OF q]]) simp_all
  have u: "\<Gamma> \<turnstile>\<^sub>U Imp (Forall rc_u (Imp (roCl T (Var 0)) (App (Var 0) (shift q)))) (Imp (roCl T X) (App X q))"
    by (rule ro_ui[OF tA X]) (simp add: subst0_def)
  show ?thesis by (rule u_rc_pc2[OF i u]) (insert U_formula[OF i] U_formula[OF u], auto elim!: has_type.cases[of _ "Imp _ _"]
    has_type.cases[of _ "Conj _ _"] intro!: has_type.Imp)
qed

lemma ro_W_intro: assumes P: "\<Gamma> \<turnstile> P : Prop" and q: "\<Gamma> \<turnstile> q : Prop"
  and h: "rc_u # \<Gamma> \<turnstile>\<^sub>U Imp (shift P) (Imp (roCl T (Var 0)) (App (Var 0) (shift q)))"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp P (App (roW T) q)"
proof -
  have tQ: "rc_u # \<Gamma> \<turnstile> Imp (roCl T (Var 0)) (App (Var 0) (shift q)) : Prop"
    by (intro has_type.Imp roCl_ty has_type.App[OF _ weaken_shift_type_ok[OF q]]) simp_all
  note g = U_proves.Gen[OF P tQ h] and i = ro_W_iff[OF q]
  have tW: "\<Gamma> \<turnstile> App (roW T) q : Prop" by (rule has_type.App[OF roW_ty q])
  show ?thesis by (rule u_rc_pc2[OF g i has_type.Imp[OF P tW]]) (unfold prop_eval.simps, blast)
qed

subsection \<open>Instances of the closure conditions\<close>

lemma ro_Cl2_inst: assumes X: "\<Gamma> \<turnstile> X : rc_u" and p: "\<Gamma> \<turnstile> p : Prop" and q: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (roCl2 X) (Imp (Conj (App X p) (App X q)) (App X (Conj p q)))"
proof -
  let ?B = "Forall Prop (Imp (Conj (App (shift (shift X)) (Var 1)) (App (shift (shift X)) (Var 0)))
     (App (shift (shift X)) (Conj (Var 1) (Var 0))))"
  let ?B1 = "Imp (Conj (App (shift X) (shift p)) (App (shift X) (Var 0))) (App (shift X) (Conj (shift p) (Var 0)))"
  have X1: "Prop # \<Gamma> \<turnstile> shift X : rc_u" and X2: "Prop # Prop # \<Gamma> \<turnstile> shift (shift X) : rc_u"
    and p1: "Prop # \<Gamma> \<turnstile> shift p : Prop" by (intro weaken_shift_type_ok X p)+
  have tB: "Prop # \<Gamma> \<turnstile> ?B : Prop"
    by (rule infer_type_sound) (simp add: infer_type_complete[OF X2] lookup_def)
  have tB1: "Prop # \<Gamma> \<turnstile> ?B1 : Prop"
    by (rule infer_type_sound) (simp add: infer_type_complete[OF X1] infer_type_complete[OF p1] lookup_def)
  have u1: "\<Gamma> \<turnstile>\<^sub>U Imp (Forall Prop ?B) (Forall Prop ?B1)"
    by (rule ro_ui[OF tB p]) (simp add: subst0_def flip: shift_def)
  have u2: "\<Gamma> \<turnstile>\<^sub>U Imp (Forall Prop ?B1) (Imp (Conj (App X p) (App X q)) (App X (Conj p q)))"
    by (rule ro_ui[OF tB1 q]) (simp add: subst0_def)
  show ?thesis unfolding roCl2_def
    by (rule u_rc_pc2[OF u1 u2]) (insert U_formula[OF u1] U_formula[OF u2], auto elim!: has_type.cases[of _ "Imp _ _"] intro!: has_type.Imp)
qed

lemma ro_Cl3_inst: assumes X: "\<Gamma> \<turnstile> X : rc_u" and p: "\<Gamma> \<turnstile> p : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (roCl3 T X) (Imp (App X p) (App X (App T p)))"
proof -
  have X1: "Prop # \<Gamma> \<turnstile> shift X : rc_u" by (rule weaken_shift_type_ok[OF X])
  have tB: "Prop # \<Gamma> \<turnstile> Imp (App (shift X) (Var 0)) (App (shift X) (App T (Var 0))) : Prop"
    by (rule infer_type_sound) (simp add: infer_type_complete[OF X1] T_inf lookup_def)
  show ?thesis unfolding roCl3_def by (rule ro_ui[OF tB p]) (simp add: subst0_def T_subst)
qed

lemma ro_Cl4_inst: assumes X: "\<Gamma> \<turnstile> X : rc_u" and S: "\<Gamma> \<turnstile> S : rc_u"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (roCl4 X) (Imp (App rc_p S) (App X (App rc_p S)))"
proof -
  have X1: "rc_u # \<Gamma> \<turnstile> shift X : rc_u" by (rule weaken_shift_type_ok[OF X])
  have tB: "rc_u # \<Gamma> \<turnstile> Imp (App rc_p (Var 0)) (App (shift X) (App rc_p (Var 0))) : Prop"
    by (rule infer_type_sound) (simp add: infer_type_complete[OF X1] pp_Pure_def lookup_def)
  show ?thesis unfolding roCl4_def by (rule ro_ui[OF tB S]) (simp add: subst0_def)
qed

lemma ro_Cl5_inst: assumes X: "\<Gamma> \<turnstile> X : rc_u" and S: "\<Gamma> \<turnstile> S : rc_u"
  shows "\<Gamma> \<turnstile>\<^sub>U Imp (roCl5 X) (Imp (Conj (App rc_p S) (Forall Prop (Imp (App (shift S) (Var 0)) (App (shift X) (Var 0)))))
    (App X (rom S)))"
proof -
  have X2: "Prop # rc_u # \<Gamma> \<turnstile> shift (shift X) : rc_u" and X1: "rc_u # \<Gamma> \<turnstile> shift X : rc_u"
    by (intro weaken_shift_type_ok X)+
  have tB: "rc_u # \<Gamma> \<turnstile> Imp (Conj (App rc_p (Var 0)) (Forall Prop (Imp (App (Var 1) (Var 0)) (App (shift (shift X)) (Var 0)))))
     (App (shift X) (rom (Var 0))) : Prop"
    by (rule infer_type_sound) (simp add: infer_type_complete[OF X1] infer_type_complete[OF X2] rom_def ro_m_def pp_Pure_def lookup_def)
  show ?thesis unfolding roCl5_def by (rule ro_ui[OF tB S]) (simp add: subst0_def flip: shift_def)
qed

subsection \<open>First, the base logic proves Cl(W)\<close>

lemma ro_ClW_1: "\<Gamma> \<turnstile>\<^sub>U roCl1 (roW T)"
proof -
  have v: "rc_u # \<Gamma> \<turnstile> Var 0 : rc_u" by simp
  note c = ro_Cl_iff[OF v]
  have tg: "rc_u # \<Gamma> \<turnstile> Imp ObjTrue (Imp (roCl T (Var 0)) (App (Var 0) ObjTrue)) : Prop"
    by (intro has_type.Imp typed_ObjTrue roCl_ty has_type.App[OF v typed_ObjTrue]) simp
  have h: "rc_u # \<Gamma> \<turnstile>\<^sub>U Imp (shift ObjTrue) (Imp (roCl T (Var 0)) (App (Var 0) (shift ObjTrue)))"
    unfolding ro_shift_true by (rule u_rc_pc1[OF c tg]) (unfold roClB_def roCl1_def prop_eval.simps, blast)
  have "\<Gamma> \<turnstile>\<^sub>U Imp ObjTrue (App (roW T) ObjTrue)" by (rule ro_W_intro[OF typed_ObjTrue typed_ObjTrue h])
  then show ?thesis unfolding roCl1_def by (rule U_proves.MP[OF U_true])
qed

lemma ro_ClW_2: "\<Gamma> \<turnstile>\<^sub>U roCl2 (roW T)"
proof -
  let ?W = "roW T" let ?D = "Prop # Prop # \<Gamma>" let ?D1 = "rc_u # Prop # Prop # \<Gamma>"
  have v0: "?D1 \<turnstile> Var 0 : rc_u" and v1: "?D1 \<turnstile> Var 1 : Prop" and v2: "?D1 \<turnstile> Var 2 : Prop"
    by (simp_all add: lookup_def eval_nat_numeral)
  note e1 = ro_W_elim[OF v0 v2] and e2 = ro_W_elim[OF v0 v1] and c = ro_Cl_iff[OF v0]
    and i = ro_Cl2_inst[OF v0 v2 v1]
  have tg: "?D1 \<turnstile> Imp (Conj (App ?W (Var 2)) (App ?W (Var 1))) (Imp (roCl T (Var 0)) (App (Var 0) (Conj (Var 2) (Var 1)))) : Prop"
    by (intro has_type.Imp has_type.Conj roCl_ty has_type.App[OF roW_ty] has_type.App[OF v0] v1 v2 v0)
  have h: "?D1 \<turnstile>\<^sub>U Imp (Conj (App ?W (Var 2)) (App ?W (Var 1))) (Imp (roCl T (Var 0)) (App (Var 0) (Conj (Var 2) (Var 1))))"
    by (rule u_rc_pc4[OF e1 e2 c i tg]) (unfold roClB_def prop_eval.simps, blast)
  have w0: "?D \<turnstile> Var 0 : Prop" and w1: "?D \<turnstile> Var 1 : Prop" by simp_all
  have tP: "?D \<turnstile> Conj (App ?W (Var 1)) (App ?W (Var 0)) : Prop"
    by (intro has_type.Conj has_type.App[OF roW_ty] w0 w1)
  have tq: "?D \<turnstile> Conj (Var 1) (Var 0) : Prop" by (intro has_type.Conj w0 w1)
  have d: "?D \<turnstile>\<^sub>U Imp (Conj (App ?W (Var 1)) (App ?W (Var 0))) (App ?W (Conj (Var 1) (Var 0)))"
  proof (rule ro_W_intro[OF tP tq])
    have s1: "shift (Conj (App ?W (Var 1)) (App ?W (Var 0))) = Conj (App ?W (Var 2)) (App ?W (Var 1))"
      and s2: "shift (Conj (Var 1) (Var 0)) = Conj (Var 2) (Var 1)" by (simp_all add: shift_def)
    show "?D1 \<turnstile>\<^sub>U Imp (shift (Conj (App ?W (Var 1)) (App ?W (Var 0)))) (Imp (roCl T (Var 0)) (App (Var 0) (shift (Conj (Var 1) (Var 0)))))"
      unfolding s1 s2 by (rule h)
  qed
  show ?thesis using ro_gen0[OF ro_gen0[OF d]] unfolding roCl2_def by simp
qed

lemma ro_ClW_3: "\<Gamma> \<turnstile>\<^sub>U roCl3 T (roW T)"
proof -
  let ?W = "roW T" let ?D = "Prop # \<Gamma>" let ?D1 = "rc_u # Prop # \<Gamma>"
  have v0: "?D1 \<turnstile> Var 0 : rc_u" and v1: "?D1 \<turnstile> Var 1 : Prop" by simp_all
  have tT1: "?D1 \<turnstile> App T (Var 1) : Prop" by (rule has_type.App[OF T_ty v1])
  note e = ro_W_elim[OF v0 v1] and c = ro_Cl_iff[OF v0] and i = ro_Cl3_inst[OF v0 v1]
  have tg: "?D1 \<turnstile> Imp (App ?W (Var 1)) (Imp (roCl T (Var 0)) (App (Var 0) (App T (Var 1)))) : Prop"
    by (intro has_type.Imp roCl_ty has_type.App[OF roW_ty] has_type.App[OF v0] v1 v0 tT1)
  have h: "?D1 \<turnstile>\<^sub>U Imp (App ?W (Var 1)) (Imp (roCl T (Var 0)) (App (Var 0) (App T (Var 1))))"
    by (rule u_rc_pc3[OF e c i tg]) (unfold roClB_def prop_eval.simps, blast)
  have w0: "?D \<turnstile> Var 0 : Prop" by simp
  have d: "?D \<turnstile>\<^sub>U Imp (App ?W (Var 0)) (App ?W (App T (Var 0)))"
  proof (rule ro_W_intro[OF has_type.App[OF roW_ty w0] has_type.App[OF T_ty w0]])
    have s1: "shift (App ?W (Var 0)) = App ?W (Var 1)" and s2: "shift (App T (Var 0)) = App T (Var 1)"
      by (simp_all add: shift_def T_rename)
    show "?D1 \<turnstile>\<^sub>U Imp (shift (App ?W (Var 0))) (Imp (roCl T (Var 0)) (App (Var 0) (shift (App T (Var 0)))))"
      unfolding s1 s2 by (rule h)
  qed
  show ?thesis using ro_gen0[OF d] unfolding roCl3_def by simp
qed

lemma ro_ClW_4: "\<Gamma> \<turnstile>\<^sub>U roCl4 (roW T)"
proof -
  let ?W = "roW T" let ?D = "rc_u # \<Gamma>" let ?D1 = "rc_u # rc_u # \<Gamma>"
  have v0: "?D1 \<turnstile> Var 0 : rc_u" and v1: "?D1 \<turnstile> Var 1 : rc_u" by simp_all
  note c = ro_Cl_iff[OF v0] and i = ro_Cl4_inst[OF v0 v1]
  have tg: "?D1 \<turnstile> Imp (App rc_p (Var 1)) (Imp (roCl T (Var 0)) (App (Var 0) (App rc_p (Var 1)))) : Prop"
    by (intro has_type.Imp roCl_ty rc_pure_ty has_type.App[OF v0] v1 v0)
  have h: "?D1 \<turnstile>\<^sub>U Imp (App rc_p (Var 1)) (Imp (roCl T (Var 0)) (App (Var 0) (App rc_p (Var 1))))"
    by (rule u_rc_pc2[OF c i tg]) (unfold roClB_def prop_eval.simps, blast)
  have w0: "?D \<turnstile> Var 0 : rc_u" by simp
  have d: "?D \<turnstile>\<^sub>U Imp (App rc_p (Var 0)) (App ?W (App rc_p (Var 0)))"
  proof (rule ro_W_intro[OF rc_pure_ty[OF w0] rc_pure_ty[OF w0]])
    have s1: "shift (App rc_p (Var 0)) = App rc_p (Var 1)" by (simp add: shift_def)
    show "?D1 \<turnstile>\<^sub>U Imp (shift (App rc_p (Var 0))) (Imp (roCl T (Var 0)) (App (Var 0) (shift (App rc_p (Var 0)))))"
      unfolding s1 by (rule h)
  qed
  show ?thesis using ro_gen0[OF d] unfolding roCl4_def by simp
qed

lemma ro_ClW_5: "\<Gamma> \<turnstile>\<^sub>U roCl5 (roW T)"
proof -
  let ?W = "roW T" let ?D = "rc_u # \<Gamma>" let ?D1 = "rc_u # rc_u # \<Gamma>" let ?D2 = "Prop # rc_u # rc_u # \<Gamma>"
  let ?F = "Forall Prop (Imp (App (Var 2) (Var 0)) (App ?W (Var 0)))"
  have v0: "?D1 \<turnstile> Var 0 : rc_u" and v1: "?D1 \<turnstile> Var 1 : rc_u" by simp_all
  have x0: "?D2 \<turnstile> Var 0 : Prop" and x1: "?D2 \<turnstile> Var 1 : rc_u" and x2: "?D2 \<turnstile> Var 2 : rc_u"
    by (simp_all add: lookup_def eval_nat_numeral)
  have tA: "Prop # ?D2 \<turnstile> Imp (App (Var 3) (Var 0)) (App ?W (Var 0)) : Prop"
    by (intro has_type.Imp has_type.App[OF roW_ty]) (simp_all add: lookup_def eval_nat_numeral has_type.App)
  have u1: "?D2 \<turnstile>\<^sub>U Imp (Forall Prop (Imp (App (Var 3) (Var 0)) (App ?W (Var 0)))) (Imp (App (Var 2) (Var 0)) (App ?W (Var 0)))"
    by (rule ro_ui[OF tA x0]) (simp add: subst0_def eval_nat_numeral)
  note e = ro_W_elim[OF x1 x0]
  have tg1: "?D2 \<turnstile> Imp (Conj (Forall Prop (Imp (App (Var 3) (Var 0)) (App ?W (Var 0)))) (roCl T (Var 1))) (Imp (App (Var 2) (Var 0)) (App (Var 1) (Var 0))) : Prop"
    using U_formula[OF u1] U_formula[OF e] by (auto elim!: has_type.cases[of _ "Imp _ _"] intro!: has_type.Imp has_type.Conj)
  have a0: "?D2 \<turnstile>\<^sub>U Imp (Conj (Forall Prop (Imp (App (Var 3) (Var 0)) (App ?W (Var 0)))) (roCl T (Var 1))) (Imp (App (Var 2) (Var 0)) (App (Var 1) (Var 0)))"
    by (rule u_rc_pc2[OF u1 e tg1]) (unfold prop_eval.simps, blast)
  have tP': "?D1 \<turnstile> Conj ?F (roCl T (Var 0)) : Prop"
    using U_formula[OF u1] by (intro has_type.Conj has_type.Forall roCl_ty v0) (auto elim!: has_type.cases[of _ "Imp _ _"] intro!: has_type.Imp
      simp: lookup_def eval_nat_numeral has_type.App)
  have tQ': "?D2 \<turnstile> Imp (App (Var 2) (Var 0)) (App (Var 1) (Var 0)) : Prop"
    using tg1 by (auto elim!: has_type.cases[of _ "Imp _ _"])
  have shP: "shift (Conj ?F (roCl T (Var 0))) = Conj (Forall Prop (Imp (App (Var 3) (Var 0)) (App ?W (Var 0)))) (roCl T (Var 1))"
    by (simp add: shift_def eval_nat_numeral)
  have stepA: "?D1 \<turnstile>\<^sub>U Imp (Conj ?F (roCl T (Var 0))) (Forall Prop (Imp (App (Var 2) (Var 0)) (App (Var 1) (Var 0))))"
    by (rule U_proves.Gen[OF tP' tQ']) (unfold shP, rule a0)
  have i5: "?D1 \<turnstile>\<^sub>U Imp (roCl5 (Var 0)) (Imp (Conj (App rc_p (Var 1)) (Forall Prop (Imp (App (Var 2) (Var 0)) (App (Var 1) (Var 0)))))
      (App (Var 0) (rom (Var 1))))"
    using ro_Cl5_inst[OF v0 v1] by (simp add: shift_def eval_nat_numeral)
  note c = ro_Cl_iff[OF v0]
  have tg: "?D1 \<turnstile> Imp (Conj (App rc_p (Var 1)) ?F) (Imp (roCl T (Var 0)) (App (Var 0) (rom (Var 1)))) : Prop"
    using tP' U_formula[OF i5] by (auto elim!: has_type.cases[of _ "Imp _ _"] has_type.cases[of _ "Conj _ _"] intro!: has_type.Imp has_type.Conj)
  have h: "?D1 \<turnstile>\<^sub>U Imp (Conj (App rc_p (Var 1)) ?F) (Imp (roCl T (Var 0)) (App (Var 0) (rom (Var 1))))"
    by (rule u_rc_pc3[OF stepA i5 c tg]) (unfold roClB_def prop_eval.simps, blast)
  have w0: "?D \<turnstile> Var 0 : rc_u" by simp
  have tP: "?D \<turnstile> Conj (App rc_p (Var 0)) (Forall Prop (Imp (App (Var 1) (Var 0)) (App ?W (Var 0)))) : Prop"
  proof -
    have a: "Prop # ?D \<turnstile> App (Var 1) (Var 0) : Prop" by (rule has_type.App[of _ _ Prop]) simp_all
    show ?thesis by (intro has_type.Conj has_type.Forall has_type.Imp rc_pure_ty[OF w0] a has_type.App[OF roW_ty]) simp
  qed
  have d: "?D \<turnstile>\<^sub>U Imp (Conj (App rc_p (Var 0)) (Forall Prop (Imp (App (Var 1) (Var 0)) (App ?W (Var 0))))) (App ?W (rom (Var 0)))"
  proof (rule ro_W_intro[OF tP rom_ty[OF w0]])
    have s1: "shift (Conj (App rc_p (Var 0)) (Forall Prop (Imp (App (Var 1) (Var 0)) (App ?W (Var 0))))) = Conj (App rc_p (Var 1)) ?F"
      and s2: "shift (rom (Var 0)) = rom (Var 1)" by (simp_all add: shift_def eval_nat_numeral)
    show "?D1 \<turnstile>\<^sub>U Imp (shift (Conj (App rc_p (Var 0)) (Forall Prop (Imp (App (Var 1) (Var 0)) (App ?W (Var 0)))))) (Imp (roCl T (Var 0)) (App (Var 0) (shift (rom (Var 0)))))"
      unfolding s1 s2 by (rule h)
  qed
  show ?thesis using ro_gen0[OF d] unfolding roCl5_def by simp
qed

theorem ro_ClW: "\<Gamma> \<turnstile>\<^sub>U roCl T (roW T)"
proof -
  note c = ro_Cl_iff[OF roW_ty]
  show ?thesis by (rule ro_pc6[OF ro_ClW_1 ro_ClW_2 ro_ClW_3 ro_ClW_4 ro_ClW_5 c roCl_ty[OF roW_ty]])
    (unfold roClB_def prop_eval.simps, blast)
qed

subsection \<open>Second, a \<longrightarrow> \<Theta> a is a theorem of the base logic, and Necessitation applies\<close>

theorem ro_base: "\<Gamma> \<turnstile>\<^sub>U Imp (roa T) (App T (roa T))"
proof -
  let ?W = "roW T" let ?a = "roa T"
  have tW: "\<Gamma> \<turnstile> ?W : rc_u" by (rule roW_ty)
  have tm: "\<Gamma> \<turnstile> rom ?W : Prop" by (rule rom_ty[OF tW])
  have tp: "\<Gamma> \<turnstile> App rc_p ?W : Prop" by (rule rc_pure_ty[OF tW])
  have ta: "\<Gamma> \<turnstile> ?a : Prop" by (rule roa_ty)
  have tTa: "\<Gamma> \<turnstile> App T ?a : Prop" by (rule has_type.App[OF T_ty ta])
  have s4: "\<Gamma> \<turnstile>\<^sub>U Imp (App rc_p ?W) (App ?W (App rc_p ?W))" by (rule U_proves.MP[OF ro_ClW_4 ro_Cl4_inst[OF tW tW]])
  have i5: "\<Gamma> \<turnstile>\<^sub>U Imp (Conj (App rc_p ?W) (Forall Prop (Imp (App ?W (Var 0)) (App ?W (Var 0))))) (App ?W (rom ?W))"
    using U_proves.MP[OF ro_ClW_5 ro_Cl5_inst[OF tW tW]] by simp
  have v: "Prop # \<Gamma> \<turnstile> App ?W (Var 0) : Prop" by (rule has_type.App[OF roW_ty]) simp
  have rf: "\<Gamma> \<turnstile>\<^sub>U Forall Prop (Imp (App ?W (Var 0)) (App ?W (Var 0)))"
    by (rule ro_gen0[OF U_taut]) (insert v, unfold prop_tautology_def prop_eval.simps, blast)
  have s5: "\<Gamma> \<turnstile>\<^sub>U Imp (App rc_p ?W) (App ?W (rom ?W))"
    by (rule u_rc_pc2[OF i5 rf]) (insert tp has_type.App[OF tW tm], auto)
  have s2: "\<Gamma> \<turnstile>\<^sub>U Imp (Conj (App ?W (rom ?W)) (App ?W (App rc_p ?W))) (App ?W (Conj (rom ?W) (App rc_p ?W)))"
    by (rule U_proves.MP[OF ro_ClW_2 ro_Cl2_inst[OF tW tm tp]])
  have s3: "\<Gamma> \<turnstile>\<^sub>U Imp (App ?W ?a) (App ?W (App T ?a))" by (rule U_proves.MP[OF ro_ClW_3 ro_Cl3_inst[OF tW ta]])
  have mi: "\<Gamma> \<turnstile>\<^sub>U (rom ?W \<longleftrightarrow>\<^sub>o Forall Prop (Imp (App ?W (Var 0)) (Var 0)))" using ro_m_iff[OF tW] by simp
  have tB: "Prop # \<Gamma> \<turnstile> Imp (App ?W (Var 0)) (Var 0) : Prop" by (intro has_type.Imp v) simp
  have u: "\<Gamma> \<turnstile>\<^sub>U Imp (Forall Prop (Imp (App ?W (Var 0)) (Var 0))) (Imp (App ?W (App T ?a)) (App T ?a))"
    by (rule ro_ui[OF tB tTa]) (simp add: subst0_def)
  show ?thesis by (rule ro_pc6[OF s4 s5 s2 s3 mi u has_type.Imp[OF ta tTa]]) (unfold roa_def prop_eval.simps, blast)
qed

theorem ro_boxed: "\<Gamma> \<turnstile>\<^sub>U \<box>\<^sub>o (Imp (roa T) (App T (roa T)))" by (rule U_nec[OF ro_base])

subsection \<open>Third, the ordinary premises make a pure and true\<close>

text \<open>Cl(G) for G = \<lambda>p. Pure_t(p) \<and> p, under the premises roH T (none of them necessitated).\<close>

lemma ro_ClG_1: "\<Gamma> \<turnstile>\<^sub>U Imp (roH T) (roCl1 ro_G)"
proof -
  note g = ro_G_iff[OF typed_ObjTrue[of \<Gamma>]]
  have tg: "\<Gamma> \<turnstile> Imp (roH T) (App ro_G ObjTrue) : Prop" by (intro has_type.Imp roH_ty has_type.App[OF ro_G_ty typed_ObjTrue])
  show ?thesis unfolding roCl1_def by (rule u_rc_pc2[OF g U_true tg]) (unfold roH_def roHC_def prop_eval.simps, blast)
qed

lemma ro_ClG_2: "\<Gamma> \<turnstile>\<^sub>U Imp (roH T) (roCl2 ro_G)"
proof -
  let ?G = ro_G let ?D = "Prop # Prop # \<Gamma>"
  have w0: "?D \<turnstile> Var 0 : Prop" and w1: "?D \<turnstile> Var 1 : Prop" by simp_all
  have tc: "?D \<turnstile> Conj (Var 1) (Var 0) : Prop" by (intro has_type.Conj w0 w1)
  have ta1: "?D \<turnstile> App ro_and (Var 1) : Prop \<rightarrow>\<^sub>o Prop" by (rule has_type.App[OF ro_and_ty w1])
  note g1 = ro_G_iff[OF w1] and g0 = ro_G_iff[OF w0] and gc = ro_G_iff[OF tc]
    and a1 = u_rc_ac[OF ro_and_ty w1] and a2 = u_rc_ac[OF ta1 w0] and be = ro_pure_be[OF ro_and_be[OF w1 w0]]
  have tg: "?D \<turnstile> Imp (roH T) (Imp (Conj (App ?G (Var 1)) (App ?G (Var 0))) (App ?G (Conj (Var 1) (Var 0)))) : Prop"
    by (intro has_type.Imp has_type.Conj roH_ty has_type.App[OF ro_G_ty] w0 w1 tc)
  have h: "?D \<turnstile>\<^sub>U Imp (roH T) (Imp (Conj (App ?G (Var 1)) (App ?G (Var 0))) (App ?G (Conj (Var 1) (Var 0))))"
    by (rule ro_pc6[OF g1 g0 gc a1 a2 be tg]) (unfold roH_def roHC_def prop_eval.simps, blast)
  have "\<Gamma> \<turnstile>\<^sub>U Imp (roH T) (Forall Prop (Forall Prop (Imp (Conj (App ?G (Var 1)) (App ?G (Var 0))) (App ?G (Conj (Var 1) (Var 0))))))"
    by (rule ro_gen[OF roH_ty roH_closed ro_gen[OF roH_ty roH_closed h]])
  then show ?thesis unfolding roCl2_def by simp
qed

lemma ro_ClG_3: "\<Gamma> \<turnstile>\<^sub>U Imp (roH T) (roCl3 T ro_G)"
proof -
  let ?G = ro_G let ?D = "Prop # \<Gamma>"
  have w0: "?D \<turnstile> Var 0 : Prop" by simp
  have tT: "?D \<turnstile> App T (Var 0) : Prop" by (rule has_type.App[OF T_ty w0])
  have tB: "Prop # ?D \<turnstile> Imp (Conj (pp_pure Prop (Var 0)) (Var 0)) (App T (Var 0)) : Prop"
    by (intro has_type.Imp has_type.Conj typed_pp_pure has_type.App[OF T_ty]) simp_all
  have pr: "?D \<turnstile>\<^sub>U Imp (roPres T) (Imp (Conj (pp_pure Prop (Var 0)) (Var 0)) (App T (Var 0)))"
    unfolding roPres_def by (rule ro_ui[OF tB w0]) (simp add: subst0_def pp_pure_def pp_Pure_def T_subst)
  note g0 = ro_G_iff[OF w0] and gT = ro_G_iff[OF tT] and ac = u_rc_ac[OF T_ty w0]
  have tg: "?D \<turnstile> Imp (roH T) (Imp (App ?G (Var 0)) (App ?G (App T (Var 0)))) : Prop"
    by (intro has_type.Imp roH_ty has_type.App[OF ro_G_ty] w0 tT)
  have h: "?D \<turnstile>\<^sub>U Imp (roH T) (Imp (App ?G (Var 0)) (App ?G (App T (Var 0))))"
    by (rule u_rc_pc4[OF pr g0 gT ac tg]) (unfold roH_def roHC_def prop_eval.simps, blast)
  show ?thesis using ro_gen[OF roH_ty roH_closed h] unfolding roCl3_def by simp
qed

lemma ro_ClG_4: "\<Gamma> \<turnstile>\<^sub>U Imp (roH T) (roCl4 ro_G)"
proof -
  let ?G = ro_G let ?D = "rc_u # \<Gamma>"
  have w0: "?D \<turnstile> Var 0 : rc_u" by simp
  have tp: "?D \<turnstile> App rc_p (Var 0) : Prop" by (rule rc_pure_ty[OF w0])
  note ac = u_rc_ac[OF rc_p_ty w0] and gp = ro_G_iff[OF tp]
  have tg: "?D \<turnstile> Imp (roH T) (Imp (App rc_p (Var 0)) (App ?G (App rc_p (Var 0)))) : Prop"
    by (intro has_type.Imp roH_ty has_type.App[OF ro_G_ty] tp)
  have h: "?D \<turnstile>\<^sub>U Imp (roH T) (Imp (App rc_p (Var 0)) (App ?G (App rc_p (Var 0))))"
    by (rule u_rc_pc2[OF ac gp tg]) (unfold roH_def roHC_def pp_pure_def prop_eval.simps, blast)
  show ?thesis using ro_gen[OF roH_ty roH_closed h] unfolding roCl4_def by simp
qed

lemma ro_ClG_5: "\<Gamma> \<turnstile>\<^sub>U Imp (roH T) (roCl5 ro_G)"
proof -
  let ?G = ro_G let ?D = "rc_u # \<Gamma>" let ?D1 = "Prop # rc_u # \<Gamma>"
  let ?P = "Forall Prop (Imp (App (Var 1) (Var 0)) (App ?G (Var 0)))"
  have w0: "?D \<turnstile> Var 0 : rc_u" by simp
  have x0: "?D1 \<turnstile> Var 0 : Prop" by simp
  have tA: "Prop # ?D1 \<turnstile> Imp (App (Var 2) (Var 0)) (App ?G (Var 0)) : Prop"
  proof -
    have "Prop # ?D1 \<turnstile> App (Var 2) (Var 0) : Prop" by (rule has_type.App[of _ _ Prop]) (simp_all add: lookup_def eval_nat_numeral)
    then show ?thesis by (intro has_type.Imp has_type.App[OF ro_G_ty]) simp_all
  qed
  have shP: "shift ?P = Forall Prop (Imp (App (Var 2) (Var 0)) (App ?G (Var 0)))" by (simp add: shift_def eval_nat_numeral)
  have u1: "?D1 \<turnstile>\<^sub>U Imp (shift ?P) (Imp (App (Var 1) (Var 0)) (App ?G (Var 0)))"
    unfolding shP by (rule ro_ui[OF tA x0]) (simp add: subst0_def eval_nat_numeral)
  note g = ro_G_iff[OF x0]
  have tQ: "?D1 \<turnstile> Imp (App (Var 1) (Var 0)) (Var 0) : Prop"
  proof -
    have "?D1 \<turnstile> App (Var 1) (Var 0) : Prop" by (rule has_type.App[of _ _ Prop]) simp_all
    then show ?thesis by (intro has_type.Imp) simp_all
  qed
  have tP: "?D \<turnstile> ?P : Prop"
  proof -
    have a: "?D1 \<turnstile> App (Var 1) (Var 0) : Prop" by (rule has_type.App[of _ _ Prop]) simp_all
    show ?thesis by (intro has_type.Forall has_type.Imp a has_type.App[OF ro_G_ty]) simp
  qed
  have tSP: "?D1 \<turnstile> shift ?P : Prop" by (rule weaken_shift_type_ok[OF tP])
  have h0: "?D1 \<turnstile>\<^sub>U Imp (shift ?P) (Imp (App (Var 1) (Var 0)) (Var 0))"
    by (rule u_rc_pc2[OF u1 g has_type.Imp[OF tSP tQ]]) (unfold prop_eval.simps, blast)
  have stepA: "?D \<turnstile>\<^sub>U Imp ?P (Forall Prop (Imp (App (Var 1) (Var 0)) (Var 0)))"
    by (rule U_proves.Gen[OF tP tQ h0])
  have mi: "?D \<turnstile>\<^sub>U (rom (Var 0) \<longleftrightarrow>\<^sub>o Forall Prop (Imp (App (Var 1) (Var 0)) (Var 0)))" using ro_m_iff[OF w0] by (simp add: shift_def)
  note ac = u_rc_ac[OF ro_m_ty w0] and gm = ro_G_iff[OF rom_ty[OF w0]]
  have tg: "?D \<turnstile> Imp (roH T) (Imp (Conj (App rc_p (Var 0)) ?P) (App ?G (rom (Var 0)))) : Prop"
    by (intro has_type.Imp has_type.Conj roH_ty rc_pure_ty[OF w0] tP has_type.App[OF ro_G_ty] rom_ty[OF w0])
  have h: "?D \<turnstile>\<^sub>U Imp (roH T) (Imp (Conj (App rc_p (Var 0)) ?P) (App ?G (rom (Var 0))))"
    by (rule u_rc_pc4[OF stepA mi ac gm tg]) (unfold roH_def roHC_def rom_def pp_pure_def prop_eval.simps, blast)
  show ?thesis using ro_gen[OF roH_ty roH_closed h] unfolding roCl5_def by simp
qed

theorem ro_ClG: "\<Gamma> \<turnstile>\<^sub>U Imp (roH T) (roCl T ro_G)"
proof -
  note c = ro_Cl_iff[OF ro_G_ty]
  have tg: "\<Gamma> \<turnstile> Imp (roH T) (roCl T ro_G) : Prop" by (intro has_type.Imp roH_ty roCl_ty ro_G_ty)
  show ?thesis by (rule ro_pc6[OF ro_ClG_1 ro_ClG_2 ro_ClG_3 ro_ClG_4 ro_ClG_5 c tg]) (unfold roClB_def prop_eval.simps, blast)
qed

text \<open>W \<subseteq> G, hence m(W).\<close>

theorem ro_mW: "\<Gamma> \<turnstile>\<^sub>U Imp (roH T) (rom (roW T))"
proof -
  let ?W = "roW T" let ?D = "Prop # \<Gamma>"
  have x0: "?D \<turnstile> Var 0 : Prop" by simp
  note e = ro_W_elim[OF ro_G_ty x0] and cg = ro_ClG[of ?D] and g = ro_G_iff[OF x0]
  have tg: "?D \<turnstile> Imp (roH T) (Imp (App ?W (Var 0)) (Var 0)) : Prop" by (intro has_type.Imp roH_ty has_type.App[OF roW_ty] x0)
  have h: "?D \<turnstile>\<^sub>U Imp (roH T) (Imp (App ?W (Var 0)) (Var 0))"
    by (rule u_rc_pc3[OF e cg g tg]) (unfold prop_eval.simps, blast)
  note f = ro_gen[OF roH_ty roH_closed h]
  have mi: "\<Gamma> \<turnstile>\<^sub>U (rom ?W \<longleftrightarrow>\<^sub>o Forall Prop (Imp (App ?W (Var 0)) (Var 0)))" using ro_m_iff[OF roW_ty] by simp
  have tg2: "\<Gamma> \<turnstile> Imp (roH T) (rom ?W) : Prop" by (intro has_type.Imp roH_ty rom_ty roW_ty)
  show ?thesis by (rule u_rc_pc2[OF f mi tg2]) (unfold prop_eval.simps, blast)
qed

text \<open>\<pi>(W): W is a closed logical term applied to the pure parameters \<pi> and \<Theta>.\<close>

theorem ro_piW: "\<Gamma> \<turnstile>\<^sub>U Imp (roH T) (App rc_p (roW T))"
proof -
  have t1: "\<Gamma> \<turnstile> App ro_W rc_p : rc_u \<rightarrow>\<^sub>o rc_u" by (rule has_type.App[OF ro_W_ty rc_p_ty])
  note a1 = u_rc_ac[OF ro_W_ty rc_p_ty, of \<Gamma>] and a2 = u_rc_ac[OF t1 T_ty]
  have tg: "\<Gamma> \<turnstile> Imp (roH T) (App rc_p (roW T)) : Prop" by (intro has_type.Imp roH_ty rc_pure_ty roW_ty)
  show ?thesis by (rule u_rc_pc2[OF a1 a2 tg]) (unfold roH_def roHC_def roW_def pp_pure_def prop_eval.simps, blast)
qed

theorem ro_pure_a: "\<Gamma> \<turnstile>\<^sub>U Imp (roH T) (pp_pure Prop (roa T))"
proof -
  let ?W = "roW T"
  have tm: "\<Gamma> \<turnstile> rom ?W : Prop" by (rule rom_ty[OF roW_ty])
  have tp: "\<Gamma> \<turnstile> App rc_p ?W : Prop" by (rule rc_pure_ty[OF roW_ty])
  have t3: "\<Gamma> \<turnstile> App ro_and (rom ?W) : Prop \<rightarrow>\<^sub>o Prop" by (rule has_type.App[OF ro_and_ty tm])
  note p1 = u_rc_ac[OF ro_m_ty roW_ty, of \<Gamma>] and p2 = u_rc_ac[OF rc_p_ty roW_ty, of \<Gamma>]
    and p3 = u_rc_ac[OF ro_and_ty tm] and p4 = u_rc_ac[OF t3 tp] and be = ro_pure_be[OF ro_and_be[OF tm tp]]
  have tg: "\<Gamma> \<turnstile> Imp (roH T) (pp_pure Prop (roa T)) : Prop" by (intro has_type.Imp roH_ty typed_pp_pure roa_ty)
  show ?thesis by (rule ro_pc6[OF p1 p2 p3 p4 be ro_piW tg]) (unfold roH_def roHC_def roa_def rom_def pp_pure_def prop_eval.simps, blast)
qed

text \<open>Lemma 10: a is pure and true.\<close>

theorem ro_closure_true:
  "\<Gamma> \<turnstile>\<^sub>U Imp roHC (Imp (pp_pure rc_u T) (Imp (roPres T) (Conj (pp_pure Prop (roa T)) (roa T))))"
proof -
  have tg: "\<Gamma> \<turnstile> Imp roHC (Imp (pp_pure rc_u T) (Imp (roPres T) (Conj (pp_pure Prop (roa T)) (roa T)))) : Prop"
    by (intro has_type.Imp has_type.Conj roHC_ty typed_pp_pure T_ty roPres_ty roa_ty)
  show ?thesis by (rule u_rc_pc3[OF ro_mW ro_piW ro_pure_a tg]) (unfold roH_def roa_def prop_eval.simps, blast)
qed

end

end
