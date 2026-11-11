theory PoP_G100_Kernel
  imports Goodman_Legacy_01.Bacon_PP_Question Bacon_Source_Vocabulary_Development.Bacon_Source_Syntax
begin

text \<open>Purity of Pure: The Main Theory
  Helm and the Purity of Pure team, a group of Claude Opus 5.5 sessions
  This theory holds four kernel results, on two theories of Branden Fitelson's library. Loupe consolidated it, with
  Jacob, on 2026-11-08, from nine theories by Dowel and Loupe; none of this text is Branden Fitelson's. Each section
  below holds one source theory, cut to what the four results reach, its formal text unchanged. The four results:
  cfp2, the paper theory C_FP proves the negation of PP_u in the local calculus; u_S, the restricted calculus U (H
  with the Rule of Equivalence at type t alone) proves S -> not ExUni; k7_HT1, C_FP refutes PP_tau at each type tau
  other than t built from t alone (k7_tonly tau); cfp6, the S6 list proves zeroary Exhaustion. u_S_C, at the end,
  carries u_S to C. The model of C_FP (k6) rests on HOL-ZF and sits in the companion theory PoP_G100_Kernel_ZF_Model.\<close>

section \<open>1. Terms and combinators\<close>

text \<open>By Dowel, with Jacob, 2026-11-05; not Branden Fitelson's. The sketch's
  terms in de Bruijn oterm, as closed logical combinators, with their
  typings and their beta unfoldings as CEV biconditionals. Q is F -> x, and
  F is box (not R1 and not R2), as in the kernel theorem rd_no_PP_root.\<close>

abbreviation rc_u :: otype where "rc_u \<equiv> Prop \<rightarrow>\<^sub>o Prop"

abbreviation rc_c :: otype where "rc_c \<equiv> rc_u \<rightarrow>\<^sub>o Prop"

abbreviation rc_p :: oterm where "rc_p \<equiv> pp_Pure rc_u"

subsection \<open>1.1 Substitution through a shift\<close>

lemma rc_lift_ren_comp: "lift_ren \<rho> (lift_ren \<tau> n) = lift_ren (\<lambda>k. \<rho> (\<tau> k)) n"
  by (cases n) simp_all

lemma rc_rename_rename: "rename \<rho> (rename \<tau> M) = rename (\<lambda>n. \<rho> (\<tau> n)) M"
  by (induction M arbitrary: \<rho> \<tau>) (simp_all add: rc_lift_ren_comp)

lemma rc_subst_rename: "subst s (rename \<rho> M) = subst (\<lambda>n. s (\<rho> n)) M"
proof (induction M arbitrary: s \<rho>)
  case (Lam \<sigma> M)
  have e: "(\<lambda>n. lift_subst s (lift_ren \<rho> n)) = lift_subst (\<lambda>n. s (\<rho> n))"
    by (rule ext, case_tac n) simp_all
  show ?case by (simp add: Lam.IH e)
next
  case (Forall \<sigma> M)
  have e: "(\<lambda>n. lift_subst s (lift_ren \<rho> n)) = lift_subst (\<lambda>n. s (\<rho> n))"
    by (rule ext, case_tac n) simp_all
  show ?case by (simp add: Forall.IH e)
next
  case (Exists \<sigma> M)
  have e: "(\<lambda>n. lift_subst s (lift_ren \<rho> n)) = lift_subst (\<lambda>n. s (\<rho> n))"
    by (rule ext, case_tac n) simp_all
  show ?case by (simp add: Exists.IH e)
qed simp_all

lemma rc_rename_subst: "rename \<rho> (subst s M) = subst (\<lambda>n. rename \<rho> (s n)) M"
proof (induction M arbitrary: s \<rho>)
  case (Lam \<sigma> M)
  have e: "(\<lambda>n. rename (lift_ren \<rho>) (lift_subst s n)) = lift_subst (\<lambda>n. rename \<rho> (s n))"
    by (rule ext, case_tac n) (simp_all add: rc_rename_rename)
  show ?case by (simp add: Lam.IH e)
next
  case (Forall \<sigma> M)
  have e: "(\<lambda>n. rename (lift_ren \<rho>) (lift_subst s n)) = lift_subst (\<lambda>n. rename \<rho> (s n))"
    by (rule ext, case_tac n) (simp_all add: rc_rename_rename)
  show ?case by (simp add: Forall.IH e)
next
  case (Exists \<sigma> M)
  have e: "(\<lambda>n. rename (lift_ren \<rho>) (lift_subst s n)) = lift_subst (\<lambda>n. rename \<rho> (s n))"
    by (rule ext, case_tac n) (simp_all add: rc_rename_rename)
  show ?case by (simp add: Exists.IH e)
qed simp_all

lemma rc_lift_shift[simp]: "subst (lift_subst s) (shift M) = shift (subst s M)"
  unfolding shift_def by (simp add: rc_subst_rename rc_rename_subst)

lemma rc_subst_box[simp]: "subst s (\<box>\<^sub>o A) = \<box>\<^sub>o (subst s A)"
  by (simp add: ObjBox_def ObjTrue_def)

lemma rc_shift_box[simp]: "shift (\<box>\<^sub>o A) = \<box>\<^sub>o (shift A)"
  by (simp add: ObjBox_def ObjTrue_def shift_def)

lemma rc_rename_p[simp]: "rename \<rho> rc_p = rc_p" by (simp add: pp_Pure_def)

lemma rc_subst_p[simp]: "subst s rc_p = rc_p" by (simp add: pp_Pure_def)

lemma rc_shift_p[simp]: "shift rc_p = rc_p" by (simp add: pp_Pure_def shift_def)

subsection \<open>1.2 The combinators\<close>

definition rc_R :: oterm where
  "rc_R = Lam rc_c (Lam Prop (Lam Prop (Forall rc_u
    (Imp (App (Var 3) (Var 0)) (Imp (App (Var 0) (Var 1)) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (Var 2))))))))))"

definition rc_F :: oterm where
  "rc_F = Lam rc_c (Lam Prop (\<box>\<^sub>o (Conj (Neg (App (App (App rc_R (Var 1)) (Var 0)) (Neg (Var 0))))
    (Neg (App (App (App rc_R (Var 1)) (Neg (Var 0))) (Var 0))))))"

definition rc_Q :: oterm where
  "rc_Q = Lam rc_c (Lam Prop (Imp (App (App rc_F (Var 1)) (Var 0)) (Var 0)))"

definition rc_P :: oterm where
  "rc_P = Lam rc_c (Lam Prop (Conj (Neg (Var 0)) (Neg (App (App rc_F (Var 1)) (Var 0)))))"

definition rc_Pp :: oterm where
  "rc_Pp = Lam rc_c (Lam Prop (Conj (Var 0) (Neg (App (App rc_F (Var 1)) (Var 0)))))"

definition rc_X :: oterm where
  "rc_X = Lam rc_c (Lam rc_u (Lam Prop (Neg (App (Var 1) (App (App rc_Q (Var 2)) (Var 0))))))"

lemma rc_R_ty: "\<Gamma> \<turnstile> rc_R : rc_c \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop))"
  by (rule infer_type_sound) (simp add: rc_R_def ObjBox_def ObjTrue_def lookup_def)

lemma rc_F_ty: "\<Gamma> \<turnstile> rc_F : rc_c \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)"
  by (rule infer_type_sound) (simp add: rc_F_def rc_R_def ObjBox_def ObjTrue_def lookup_def)

lemma rc_Q_ty: "\<Gamma> \<turnstile> rc_Q : rc_c \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)"
  by (rule infer_type_sound) (simp add: rc_Q_def rc_F_def rc_R_def ObjBox_def ObjTrue_def lookup_def)

lemma rc_P_ty: "\<Gamma> \<turnstile> rc_P : rc_c \<rightarrow>\<^sub>o rc_u"
  by (rule infer_type_sound) (simp add: rc_P_def rc_F_def rc_R_def ObjBox_def ObjTrue_def lookup_def)

lemma rc_Pp_ty: "\<Gamma> \<turnstile> rc_Pp : rc_c \<rightarrow>\<^sub>o rc_u"
  by (rule infer_type_sound) (simp add: rc_Pp_def rc_F_def rc_R_def ObjBox_def ObjTrue_def lookup_def)

lemma rc_consts:
  "consts_of rc_R = {}" "consts_of rc_F = {}" "consts_of rc_Q = {}" "consts_of rc_P = {}" "consts_of rc_Pp = {}"
  "consts_of rc_X = {}"
  by (simp_all add: rc_X_def rc_Q_def rc_P_def rc_Pp_def rc_F_def rc_R_def ObjBox_def ObjTrue_def)

lemma rc_closed[simp]:
  "subst s rc_R = rc_R" "subst s rc_F = rc_F" "subst s rc_Q = rc_Q" "subst s rc_P = rc_P" "subst s rc_Pp = rc_Pp"
  "subst s rc_X = rc_X"
  by (simp_all add: rc_X_def rc_Q_def rc_P_def rc_Pp_def rc_F_def rc_R_def ObjBox_def ObjTrue_def eval_nat_numeral)

lemma rc_shift_closed[simp]:
  "shift rc_R = rc_R" "shift rc_F = rc_F" "shift rc_Q = rc_Q" "shift rc_P = rc_P" "shift rc_Pp = rc_Pp"
  "shift rc_X = rc_X"
  by (simp_all add: rc_X_def rc_Q_def rc_P_def rc_Pp_def rc_F_def rc_R_def ObjBox_def ObjTrue_def eval_nat_numeral shift_def)

definition rcR :: "oterm \<Rightarrow> oterm \<Rightarrow> oterm" where "rcR a b = App (App (App rc_R rc_p) a) b"

definition rcF :: "oterm \<Rightarrow> oterm" where "rcF x = App (App rc_F rc_p) x"

definition rcQ :: "oterm \<Rightarrow> oterm" where "rcQ x = App (App rc_Q rc_p) x"

definition rcP :: oterm where "rcP = App rc_P rc_p"

definition rcPp :: oterm where "rcPp = App rc_Pp rc_p"

lemma rc_p_ty: "\<Gamma> \<turnstile> rc_p : rc_c" by (rule typed_pp_Pure)

lemma rcR_ty: "\<Gamma> \<turnstile> a : Prop \<Longrightarrow> \<Gamma> \<turnstile> b : Prop \<Longrightarrow> \<Gamma> \<turnstile> rcR a b : Prop"
  unfolding rcR_def by (intro has_type.App[OF has_type.App[OF has_type.App[OF rc_R_ty rc_p_ty]]])

lemma rcF_ty: "\<Gamma> \<turnstile> x : Prop \<Longrightarrow> \<Gamma> \<turnstile> rcF x : Prop"
  unfolding rcF_def by (intro has_type.App[OF has_type.App[OF rc_F_ty rc_p_ty]])

lemma rcQ_ty: "\<Gamma> \<turnstile> x : Prop \<Longrightarrow> \<Gamma> \<turnstile> rcQ x : Prop"
  unfolding rcQ_def by (intro has_type.App[OF has_type.App[OF rc_Q_ty rc_p_ty]])

lemma rcP_ty: "\<Gamma> \<turnstile> rcP : rc_u" unfolding rcP_def by (rule has_type.App[OF rc_P_ty rc_p_ty])

lemma rcPp_ty: "\<Gamma> \<turnstile> rcPp : rc_u" unfolding rcPp_def by (rule has_type.App[OF rc_Pp_ty rc_p_ty])

lemma rc_shift_App[simp]: "shift (App F A) = App (shift F) (shift A)" by (simp add: shift_def)

lemma rc_shift_R[simp]: "shift (rcR a b) = rcR (shift a) (shift b)" by (simp add: rcR_def)

lemma rc_shift_F[simp]: "shift (rcF a) = rcF (shift a)" by (simp add: rcF_def)

lemma rc_shift_Q[simp]: "shift (rcQ a) = rcQ (shift a)" by (simp add: rcQ_def)

subsection \<open>1.3 Beta\<close>

lemma rc_be1:
  assumes "\<Gamma> \<turnstile> App (Lam \<sigma> M) a : \<tau>"
  shows "beta_eta_equiv \<Gamma> \<tau> (App (Lam \<sigma> M) a) (subst0 a M)"
proof -
  have "\<sigma> # \<Gamma> \<turnstile> M : \<tau>" and "\<Gamma> \<turnstile> a : \<sigma>" using assms by (auto elim: has_type.cases)
  then have "\<Gamma> \<turnstile> subst0 a M : \<tau>" by (rule subst0_preserves_typing)
  then show ?thesis using assms by (intro beta_eta_equiv.Beta compatible_step.root beta_contract.beta)
qed

lemma rc_be_app:
  assumes "beta_eta_equiv \<Gamma> \<rho> F F'" and "\<rho> = \<sigma> \<rightarrow>\<^sub>o \<tau>" and "\<Gamma> \<turnstile> a : \<sigma>"
  shows "beta_eta_equiv \<Gamma> \<tau> (App F a) (App F' a)"
  using assms
proof (induction rule: beta_eta_equiv.induct)
  case (Refl \<Gamma> M \<rho>)
  have m: "\<Gamma> \<turnstile> M : \<sigma> \<rightarrow>\<^sub>o \<tau>" using Refl.hyps Refl.prems(1) by simp
  show ?case by (rule beta_eta_equiv.Refl[OF has_type.App[OF m Refl.prems(2)]])
next
  case (Beta \<Gamma> M \<rho> N)
  have m: "\<Gamma> \<turnstile> M : \<sigma> \<rightarrow>\<^sub>o \<tau>" and n: "\<Gamma> \<turnstile> N : \<sigma> \<rightarrow>\<^sub>o \<tau>" using Beta.hyps(1,2) Beta.prems(1) by simp_all
  show ?case by (rule beta_eta_equiv.Beta[OF has_type.App[OF m Beta.prems(2)] has_type.App[OF n Beta.prems(2)]
    compatible_step.App_left[OF Beta.hyps(3)]])
next
  case (Eta \<Gamma> M \<rho> N)
  have m: "\<Gamma> \<turnstile> M : \<sigma> \<rightarrow>\<^sub>o \<tau>" and n: "\<Gamma> \<turnstile> N : \<sigma> \<rightarrow>\<^sub>o \<tau>" using Eta.hyps(1,2) Eta.prems(1) by simp_all
  show ?case by (rule beta_eta_equiv.Eta[OF has_type.App[OF m Eta.prems(2)] has_type.App[OF n Eta.prems(2)]
    compatible_step.App_left[OF Eta.hyps(3)]])
next
  case (Sym \<Gamma> \<rho> M N)
  show ?case by (rule beta_eta_equiv.Sym[OF Sym.IH[OF Sym.prems]])
next
  case (Trans \<Gamma> \<rho> M N P)
  show ?case by (rule beta_eta_equiv.Trans[OF Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed

lemma rc_be2:
  assumes t1: "\<Gamma> \<turnstile> App (Lam \<rho> (Lam \<sigma> B)) p : \<sigma> \<rightarrow>\<^sub>o \<tau>" and x: "\<Gamma> \<turnstile> x : \<sigma>"
  shows "beta_eta_equiv \<Gamma> \<tau> (App (App (Lam \<rho> (Lam \<sigma> B)) p) x) (subst0 x (subst (lift_subst (case_nat p Var)) B))"
proof -
  have s1: "beta_eta_equiv \<Gamma> (\<sigma> \<rightarrow>\<^sub>o \<tau>) (App (Lam \<rho> (Lam \<sigma> B)) p) (Lam \<sigma> (subst (lift_subst (case_nat p Var)) B))"
    using rc_be1[OF t1] by (simp add: subst0_def)
  have s2: "beta_eta_equiv \<Gamma> \<tau> (App (App (Lam \<rho> (Lam \<sigma> B)) p) x) (App (Lam \<sigma> (subst (lift_subst (case_nat p Var)) B)) x)"
    by (rule rc_be_app[OF s1 refl x])
  show ?thesis by (rule beta_eta_equiv.Trans[OF s2 rc_be1[OF beta_eta_equiv_right_type[OF s2]]])
qed

section \<open>2. The steps of the sketch, derived in CEV\<close>

text \<open>By Dowel, with Jacob, 2026-11-05; not Branden Fitelson's. The four steps
  of the sketch under test (from Caltrop's notes) as CEV theorems: a line-
  by-line derivation, free of the frontier theorem and of completeness.\<close>

declare has_type.App[rule del]

subsection \<open>2.1 Tools\<close>

lemma weaken_shift_type_ok: "\<Gamma> \<turnstile> M : \<tau> \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile> shift M : \<tau>"
  unfolding shift_def by (rule renaming_preserves_typing) simp_all

lemma rc_pc1:
  assumes a: "\<Gamma> \<turnstile>\<^sub>CEV A" and b: "\<Gamma> \<turnstile> B : Prop" and t: "\<And>v. prop_eval v A \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV B"
proof -
  have "prop_tautology \<Gamma> (Imp A B)" unfolding prop_tautology_def using CEV_proves_formula[OF a] b t by auto
  then show ?thesis by (rule CEV_proves.MP[OF a CEV_prop_tautology])
qed

lemma rc_pc2:
  assumes a1: "\<Gamma> \<turnstile>\<^sub>CEV A1" and a2: "\<Gamma> \<turnstile>\<^sub>CEV A2" and b: "\<Gamma> \<turnstile> B : Prop"
    and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV B"
proof -
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp A2 B" by (rule rc_pc1[OF a1 has_type.Imp[OF CEV_proves_formula[OF a2] b]]) (use t in simp)
  then show ?thesis by (rule CEV_proves.MP[OF a2])
qed

lemma rc_pc3:
  assumes a1: "\<Gamma> \<turnstile>\<^sub>CEV A1" and a2: "\<Gamma> \<turnstile>\<^sub>CEV A2" and a3: "\<Gamma> \<turnstile>\<^sub>CEV A3" and b: "\<Gamma> \<turnstile> B : Prop"
    and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV B"
proof -
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp A3 B" by (rule rc_pc2[OF a1 a2 has_type.Imp[OF CEV_proves_formula[OF a3] b]]) (use t in simp)
  then show ?thesis by (rule CEV_proves.MP[OF a3])
qed

lemma rc_pc4:
  assumes a1: "\<Gamma> \<turnstile>\<^sub>CEV A1" and a2: "\<Gamma> \<turnstile>\<^sub>CEV A2" and a3: "\<Gamma> \<turnstile>\<^sub>CEV A3" and a4: "\<Gamma> \<turnstile>\<^sub>CEV A4"
    and b: "\<Gamma> \<turnstile> B : Prop"
    and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow> prop_eval v A4 \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV B"
proof -
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp A4 B" by (rule rc_pc3[OF a1 a2 a3 has_type.Imp[OF CEV_proves_formula[OF a4] b]]) (use t in simp)
  then show ?thesis by (rule CEV_proves.MP[OF a4])
qed

lemma rc_pc5:
  assumes a1: "\<Gamma> \<turnstile>\<^sub>CEV A1" and a2: "\<Gamma> \<turnstile>\<^sub>CEV A2" and a3: "\<Gamma> \<turnstile>\<^sub>CEV A3" and a4: "\<Gamma> \<turnstile>\<^sub>CEV A4"
    and a5: "\<Gamma> \<turnstile>\<^sub>CEV A5" and b: "\<Gamma> \<turnstile> B : Prop"
    and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow> prop_eval v A4 \<Longrightarrow> prop_eval v A5 \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV B"
proof -
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp A5 B" by (rule rc_pc4[OF a1 a2 a3 a4 has_type.Imp[OF CEV_proves_formula[OF a5] b]]) (use t in simp)
  then show ?thesis by (rule CEV_proves.MP[OF a5])
qed

lemma rc_K:
  assumes h: "\<Gamma> \<turnstile>\<^sub>CEV Imp A B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (\<box>\<^sub>o A) (\<box>\<^sub>o B)"
proof -
  have ta: "\<Gamma> \<turnstile> A : Prop" and tb: "\<Gamma> \<turnstile> B : Prop" using CEV_proves_formula[OF h] by (auto elim: has_type.cases)
  show ?thesis by (rule CEV_proves.MP[OF CEV_necessitation[OF h] CEV_modal_K[OF ta tb, unfolded modal_K_def]])
qed

subsection \<open>2.2 The sketch's first step\<close>

abbreviation rcB :: "oterm \<Rightarrow> oterm" where
  "rcB x \<equiv> Conj (Neg (rcR x (Neg x))) (Neg (rcR (Neg x) x))"

lemma rcB_ty: "\<Gamma> \<turnstile> x : Prop \<Longrightarrow> \<Gamma> \<turnstile> rcB x : Prop"
  by (intro has_type.Conj has_type.Neg rcR_ty) (simp_all add: has_type.Neg)

subsection \<open>2.3 The sketch's second step\<close>

lemma rc_pure_ty: "\<Gamma> \<turnstile> Y : rc_u \<Longrightarrow> \<Gamma> \<turnstile> App rc_p Y : Prop" by (rule has_type.App[OF rc_p_ty])

subsection \<open>2.4 The instances of the axioms\<close>

lemma rc_ac:
  assumes F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" and a: "\<Gamma> \<turnstile> a : \<sigma>"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (pp_application_closure \<sigma> \<tau>)
    (Imp (Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) (pp_pure \<sigma> a)) (pp_pure \<tau> (App F a)))"
proof -
  let ?A2 = "\<lambda>f. Imp (Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) f) (pp_pure \<sigma> (Var 0))) (pp_pure \<tau> (App f (Var 0)))"
  have ty: "\<Gamma> \<turnstile> pp_application_closure \<sigma> \<tau> : Prop"
    by (rule infer_type_sound) (simp add: pp_application_closure_def pp_pure_def pp_Pure_def lookup_def)
  have d: "pp_application_closure \<sigma> \<tau> = Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Forall \<sigma> (?A2 (Var 1)))"
    by (simp add: pp_application_closure_def)
  have t1: "(\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile> Forall \<sigma> (?A2 (Var 1)) : Prop" using ty unfolding d by (auto elim: has_type.cases)
  have e1: "subst0 F (Forall \<sigma> (?A2 (Var 1))) = Forall \<sigma> (?A2 (shift F))"
    by (simp add: subst0_def pp_pure_def pp_Pure_def flip: shift_def)
  have ui1: "\<Gamma> \<turnstile>\<^sub>CEV Imp (pp_application_closure \<sigma> \<tau>) (Forall \<sigma> (?A2 (shift F)))"
    unfolding d e1[symmetric] using t1 F by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)
  have t2: "\<Gamma> \<turnstile> Forall \<sigma> (?A2 (shift F)) : Prop" using subst0_preserves_typing[OF t1 F] unfolding e1 .
  have t3: "\<sigma> # \<Gamma> \<turnstile> ?A2 (shift F) : Prop" using t2 by (auto elim: has_type.cases)
  have e2: "subst0 a (?A2 (shift F)) = Imp (Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) (pp_pure \<sigma> a)) (pp_pure \<tau> (App F a))"
    by (simp add: subst0_def pp_pure_def pp_Pure_def)
  have ui2: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Forall \<sigma> (?A2 (shift F))) (Imp (Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) (pp_pure \<sigma> a)) (pp_pure \<tau> (App F a)))"
    unfolding e2[symmetric] using t3 a by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)
  have tr: "\<Gamma> \<turnstile> Imp (Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) (pp_pure \<sigma> a)) (pp_pure \<tau> (App F a)) : Prop"
    using subst0_preserves_typing[OF t3 a] unfolding e2 .
  show ?thesis by (rule rc_pc2[OF ui1 ui2 has_type.Imp[OF ty tr]]) (unfold prop_eval.simps, blast)
qed

subsection \<open>2.5 The sketch's fourth step\<close>

lemma rc_sft: "shift (Conj A B) = Conj (shift A) (shift B)" "shift (Neg A) = Neg (shift A)"
  "shift (Var n) = Var (Suc n)" "shift (Const c \<sigma>) = Const c \<sigma>"
  by (simp_all add: shift_def)

section \<open>3. Purity of closed terms refutes a fun' point\<close>

text \<open>By Dowel, with Jacob, 2026-11-05; not Branden Fitelson's. The trim of rc_core, after
  Adze: no Fun, no UF, no Recombination. Purity of closed terms, Application closure
  and PP refute the existence of a fun' point, (a) in the axiom extension of CEV and
  in C+[T], and (b) in the local relation of CEV, with zeroary Exhaustion named.\<close>

section \<open>4. The core lemmas, and universal propositions\<close>

text \<open>By Dowel, with Jacob, 2026-11-05; not Branden Fitelson's. Two core lemmas, at the
  existence core and at rc_core1 with Persistence at type u at P and P'; and
  universality, where Uni(s) says s can have every pure property any proposition has.\<close>

abbreviation rcBP :: oterm where "rcBP \<equiv> \<box>\<^sub>o (App rc_p rcP)"

abbreviation rcBQ :: oterm where "rcBQ \<equiv> \<box>\<^sub>o (App rc_p rcPp)"

lemma rcBP_ty: "\<Gamma> \<turnstile> rcBP : Prop" and rcBQ_ty: "\<Gamma> \<turnstile> rcBQ : Prop"
  by (rule typed_ObjBox[OF rc_pure_ty[OF rcP_ty]], rule typed_ObjBox[OF rc_pure_ty[OF rcPp_ty]])

subsection \<open>4.1 The operator W, and universality\<close>

definition rc_W :: oterm where
  "rc_W = Lam rc_c (Lam rc_u (Lam Prop (App (Var 1) (App (App rc_Q (Var 2)) (Var 0)))))"

definition rcW :: "oterm \<Rightarrow> oterm" where "rcW Y = App (App rc_W rc_p) Y"

definition rcUni :: "oterm \<Rightarrow> oterm" where "rcUni s = Forall Prop (rcR (shift s) (Var 0))"

definition rcExUni :: oterm where "rcExUni = Exists Prop (rcUni (Var 0))"

lemma rc_W_ty: "\<Gamma> \<turnstile> rc_W : rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)"
  by (rule infer_type_sound) (simp add: rc_W_def rc_Q_def rc_F_def rc_R_def ObjBox_def ObjTrue_def lookup_def)

lemma rc_W_consts: "consts_of rc_W = {}" by (simp add: rc_W_def rc_Q_def rc_F_def rc_R_def ObjBox_def ObjTrue_def)

lemma rcW_ty: "\<Gamma> \<turnstile> Y : rc_u \<Longrightarrow> \<Gamma> \<turnstile> rcW Y : rc_u"
  unfolding rcW_def by (rule has_type.App[OF has_type.App[OF rc_W_ty rc_p_ty]])

lemma rcUni_ty: "\<Gamma> \<turnstile> s : Prop \<Longrightarrow> \<Gamma> \<turnstile> rcUni s : Prop"
  unfolding rcUni_def by (intro has_type.Forall rcR_ty weaken_shift_type_ok) simp_all

lemma rc_rename_R: "rename \<rho> rc_R = rc_R"
  by (simp add: rc_R_def ObjBox_def ObjTrue_def eval_nat_numeral)

lemma rcUni_shift: "shift (rcUni (Var 0)) = rcUni (Var 1)"
  by (simp add: rcUni_def rcR_def shift_def rc_rename_R)

definition rcHU :: oterm where
  "rcHU = Conj (pp_pure (rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) rc_W) (Conj (pp_pure rc_c rc_p)
    (Conj (pp_application_closure rc_c (rc_u \<rightarrow>\<^sub>o rc_u)) (pp_application_closure rc_u rc_u)))"

lemma rcHU_ty: "\<Gamma> \<turnstile> rcHU : Prop"
  by (rule infer_type_sound) (simp add: rcHU_def rc_W_def rc_Q_def rc_F_def rc_R_def pp_application_closure_def
    pp_pure_def pp_Pure_def ObjBox_def ObjTrue_def lookup_def)

lemma rcHU_shift[simp]: "shift rcHU = rcHU"
proof -
  have x: "rename Suc rc_W = rc_W" by (simp add: rc_W_def rc_Q_def rc_F_def rc_R_def ObjBox_def ObjTrue_def eval_nat_numeral)
  show ?thesis by (simp add: rcHU_def pp_application_closure_def pp_pure_def pp_Pure_def shift_def x)
qed

section \<open>5. The restricted calculus U\<close>

text \<open>By Loupe, with Jacob, 2026-11-06; not Branden Fitelson's. A restricted calculus U: H, closed under MP, Gen, Inst
  and the Rule of Equivalence AT TYPE t ALONE. None of C's six axioms; no vector rule, so no Modalized Functionality
  as a rule. rc_coreU rebuilt in U. Past u_tools, the proofs are Dowel's text with the calculus renamed.\<close>

inductive U_proves :: "ctx \<Rightarrow> oterm \<Rightarrow> bool" ("_ \<turnstile>\<^sub>U _" [50, 50] 50) where
  H: "\<Gamma> \<turnstile>\<^sub>H A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>U A"
| PE: "\<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> B : Prop \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>U (A \<longleftrightarrow>\<^sub>o B) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>U Eq Prop A B"
| MP: "\<Gamma> \<turnstile>\<^sub>U A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>U Imp A B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>U B"
| Gen: "\<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile> Q : Prop \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile>\<^sub>U Imp (shift P) Q \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>U Imp P (Forall \<sigma> Q)"
| Inst: "\<sigma> # \<Gamma> \<turnstile> P : Prop \<Longrightarrow> \<Gamma> \<turnstile> Q : Prop \<Longrightarrow> \<sigma> # \<Gamma> \<turnstile>\<^sub>U Imp P (shift Q) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>U Imp (Exists \<sigma> P) Q"

lemma U_sub_CEV: "\<Gamma> \<turnstile>\<^sub>U A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV A" by (induction rule: U_proves.induct) (auto intro: CEV_proves.CE CE_proves.C C_proves.H CEV_zeroary_equivalence CEV_proves.MP CEV_proves.Gen CEV_proves.Inst)

lemma U_formula: "\<Gamma> \<turnstile>\<^sub>U A \<Longrightarrow> \<Gamma> \<turnstile> A : Prop" by (induction rule: U_proves.induct) (auto intro: H_proves_formula elim: has_type.cases)

lemma U_taut: "prop_tautology \<Gamma> A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>U A" by (intro U_proves.H H_proves.PC)

lemma U_true: "\<Gamma> \<turnstile>\<^sub>U ObjTrue" by (rule U_proves.H[OF H_proves_ObjTrue])

lemma U_beta_eta_equiv: "beta_eta_equiv \<Gamma> Prop A B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>U (A \<longleftrightarrow>\<^sub>o B)" by (rule U_proves.H[OF H_beta_eta_equiv])

lemma u_rc_pc1: assumes a: "\<Gamma> \<turnstile>\<^sub>U A" and b: "\<Gamma> \<turnstile> B : Prop" and t: "\<And>v. prop_eval v A \<Longrightarrow> prop_eval v B" shows "\<Gamma> \<turnstile>\<^sub>U B" proof -
  have "prop_tautology \<Gamma> (Imp A B)" unfolding prop_tautology_def using U_formula[OF a] b t by auto
  then show ?thesis by (rule U_proves.MP[OF a U_taut]) qed

lemma u_rc_pc2: assumes a1: "\<Gamma> \<turnstile>\<^sub>U A1" and a2: "\<Gamma> \<turnstile>\<^sub>U A2" and b: "\<Gamma> \<turnstile> B : Prop" and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v B" shows "\<Gamma> \<turnstile>\<^sub>U B" proof -
  have "\<Gamma> \<turnstile>\<^sub>U Imp A2 B" by (rule u_rc_pc1[OF a1 has_type.Imp[OF U_formula[OF a2] b]]) (use t in simp)
  then show ?thesis by (rule U_proves.MP[OF a2]) qed

lemma u_rc_pc3: assumes a1: "\<Gamma> \<turnstile>\<^sub>U A1" and a2: "\<Gamma> \<turnstile>\<^sub>U A2" and a3: "\<Gamma> \<turnstile>\<^sub>U A3" and b: "\<Gamma> \<turnstile> B : Prop" and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow> prop_eval v B" shows "\<Gamma> \<turnstile>\<^sub>U B" proof -
  have "\<Gamma> \<turnstile>\<^sub>U Imp A3 B" by (rule u_rc_pc2[OF a1 a2 has_type.Imp[OF U_formula[OF a3] b]]) (use t in simp)
  then show ?thesis by (rule U_proves.MP[OF a3]) qed

lemma u_rc_pc4: assumes a1: "\<Gamma> \<turnstile>\<^sub>U A1" and a2: "\<Gamma> \<turnstile>\<^sub>U A2" and a3: "\<Gamma> \<turnstile>\<^sub>U A3" and a4: "\<Gamma> \<turnstile>\<^sub>U A4" and b: "\<Gamma> \<turnstile> B : Prop" and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow> prop_eval v A4 \<Longrightarrow> prop_eval v B" shows "\<Gamma> \<turnstile>\<^sub>U B" proof -
  have "\<Gamma> \<turnstile>\<^sub>U Imp A4 B" by (rule u_rc_pc3[OF a1 a2 a3 has_type.Imp[OF U_formula[OF a4] b]]) (use t in simp)
  then show ?thesis by (rule U_proves.MP[OF a4]) qed

lemma u_rc_pc5: assumes a1: "\<Gamma> \<turnstile>\<^sub>U A1" and a2: "\<Gamma> \<turnstile>\<^sub>U A2" and a3: "\<Gamma> \<turnstile>\<^sub>U A3" and a4: "\<Gamma> \<turnstile>\<^sub>U A4" and a5: "\<Gamma> \<turnstile>\<^sub>U A5" and b: "\<Gamma> \<turnstile> B : Prop" and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow> prop_eval v A4 \<Longrightarrow> prop_eval v A5 \<Longrightarrow> prop_eval v B" shows "\<Gamma> \<turnstile>\<^sub>U B" proof -
  have "\<Gamma> \<turnstile>\<^sub>U Imp A5 B" by (rule u_rc_pc4[OF a1 a2 a3 a4 has_type.Imp[OF U_formula[OF a5] b]]) (use t in simp)
  then show ?thesis by (rule U_proves.MP[OF a5]) qed

lemma u_rc_LL: assumes "\<Gamma> \<turnstile> a : \<sigma>" and "\<Gamma> \<turnstile> b : \<sigma>" and "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o Prop" shows "\<Gamma> \<turnstile>\<^sub>U Imp (Eq \<sigma> a b) (Imp (App F a) (App F b))" using assms by (intro U_proves.H H_proves.LL)

lemma u_rc_beta_iff: assumes "\<Gamma> \<turnstile> App (Lam Prop C) a : Prop" shows "\<Gamma> \<turnstile>\<^sub>U (App (Lam Prop C) a \<longleftrightarrow>\<^sub>o subst0 a C)" by (rule U_beta_eta_equiv[OF rc_be1[OF assms]])

lemma u_rc_eq_of_iff: assumes "\<Gamma> \<turnstile> A : Prop" "\<Gamma> \<turnstile> B : Prop" "\<Gamma> \<turnstile>\<^sub>U (A \<longleftrightarrow>\<^sub>o B)" shows "\<Gamma> \<turnstile>\<^sub>U Eq Prop A B" using assms by (rule U_proves.PE)

lemma u_beta: assumes "\<Gamma> \<turnstile> App (Lam \<sigma> C) a : Prop" shows "\<Gamma> \<turnstile>\<^sub>U (App (Lam \<sigma> C) a \<longleftrightarrow>\<^sub>o subst0 a C)" by (rule U_beta_eta_equiv[OF rc_be1[OF assms]])

lemma U_eq_sym: assumes M: "\<Gamma> \<turnstile> M : \<sigma>" and N: "\<Gamma> \<turnstile> N : \<sigma>" shows "\<Gamma> \<turnstile>\<^sub>U Imp (Eq \<sigma> M N) (Eq \<sigma> N M)" proof -
  let ?F = "Lam \<sigma> (Eq \<sigma> (Var 0) (shift M))"
  have tF: "\<Gamma> \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o Prop" by (intro has_type.Lam has_type.Eq weaken_shift_type_ok[OF M]) simp
  have l: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq \<sigma> M N) (Imp (App ?F M) (App ?F N))" by (rule u_rc_LL[OF M N tF])
  have b1: "\<Gamma> \<turnstile>\<^sub>U (App ?F M \<longleftrightarrow>\<^sub>o Eq \<sigma> M M)" using u_beta[OF has_type.App[OF tF M]] by (simp add: subst0_def)
  have b2: "\<Gamma> \<turnstile>\<^sub>U (App ?F N \<longleftrightarrow>\<^sub>o Eq \<sigma> N M)" using u_beta[OF has_type.App[OF tF N]] by (simp add: subst0_def)
  have r: "\<Gamma> \<turnstile>\<^sub>U Eq \<sigma> M M" by (intro U_proves.H H_proves.Ref M)
  show ?thesis by (rule u_rc_pc4[OF l b1 b2 r]) (insert M N, (unfold prop_eval.simps)?, auto intro!: has_type.Imp has_type.Eq) qed

lemma U_eq_trans: assumes M: "\<Gamma> \<turnstile> M : \<sigma>" and N: "\<Gamma> \<turnstile> N : \<sigma>" and P: "\<Gamma> \<turnstile> P : \<sigma>" shows "\<Gamma> \<turnstile>\<^sub>U Imp (Eq \<sigma> M N) (Imp (Eq \<sigma> N P) (Eq \<sigma> M P))" proof -
  let ?F = "Lam \<sigma> (Eq \<sigma> (shift M) (Var 0))"
  have tF: "\<Gamma> \<turnstile> ?F : \<sigma> \<rightarrow>\<^sub>o Prop" by (intro has_type.Lam has_type.Eq weaken_shift_type_ok[OF M]) simp
  have l: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq \<sigma> N P) (Imp (App ?F N) (App ?F P))" by (rule u_rc_LL[OF N P tF])
  have b1: "\<Gamma> \<turnstile>\<^sub>U (App ?F N \<longleftrightarrow>\<^sub>o Eq \<sigma> M N)" using u_beta[OF has_type.App[OF tF N]] by (simp add: subst0_def)
  have b2: "\<Gamma> \<turnstile>\<^sub>U (App ?F P \<longleftrightarrow>\<^sub>o Eq \<sigma> M P)" using u_beta[OF has_type.App[OF tF P]] by (simp add: subst0_def)
  show ?thesis by (rule u_rc_pc3[OF l b1 b2]) (insert M N P, (unfold prop_eval.simps)?, auto intro!: has_type.Imp has_type.Eq) qed

lemma U_nec: assumes h: "\<Gamma> \<turnstile>\<^sub>U A" shows "\<Gamma> \<turnstile>\<^sub>U \<box>\<^sub>o A" unfolding ObjBox_def by (rule u_rc_eq_of_iff[OF U_formula[OF h] typed_ObjTrue u_rc_pc2[OF h U_true]]) (insert U_formula[OF h] typed_ObjTrue[of \<Gamma>], (unfold prop_eval.simps)?, blast+)

lemma U_modal_T: assumes A: "\<Gamma> \<turnstile> A : Prop" shows "\<Gamma> \<turnstile>\<^sub>U modal_T A" proof -
  let ?F = "Lam Prop (Var 0)" note T = typed_ObjTrue[of \<Gamma>]
  have tF: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop" by (intro has_type.Lam) simp
  have l: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop ObjTrue A) (Imp (App ?F ObjTrue) (App ?F A))" by (rule u_rc_LL[OF T A tF])
  have b1: "\<Gamma> \<turnstile>\<^sub>U (App ?F ObjTrue \<longleftrightarrow>\<^sub>o ObjTrue)" using u_beta[OF has_type.App[OF tF T]] by (simp add: subst0_def)
  have b2: "\<Gamma> \<turnstile>\<^sub>U (App ?F A \<longleftrightarrow>\<^sub>o A)" using u_beta[OF has_type.App[OF tF A]] by (simp add: subst0_def)
  show ?thesis unfolding modal_T_def ObjBox_def by (rule u_rc_pc5[OF U_eq_sym[OF A T] l b1 b2 U_true]) (insert A T, (unfold prop_eval.simps)?, auto intro!: has_type.Imp has_type.Eq) qed

lemma U_modal_K: assumes A: "\<Gamma> \<turnstile> A : Prop" and B: "\<Gamma> \<turnstile> B : Prop" shows "\<Gamma> \<turnstile>\<^sub>U modal_K A B" proof -
  let ?F = "Lam Prop (Eq Prop (Imp (Var 0) (shift B)) ObjTrue)" let ?I = "Imp ObjTrue B" note T = typed_ObjTrue[of \<Gamma>]
  have tF: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop" by (intro has_type.Lam has_type.Eq has_type.Imp weaken_shift_type_ok[OF B] typed_ObjTrue) simp
  have tI: "\<Gamma> \<turnstile> ?I : Prop" using T B by (intro has_type.Imp)
  have l: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop A ObjTrue) (Imp (App ?F A) (App ?F ObjTrue))" by (rule u_rc_LL[OF A T tF])
  have b1: "\<Gamma> \<turnstile>\<^sub>U (App ?F A \<longleftrightarrow>\<^sub>o Eq Prop (Imp A B) ObjTrue)" using u_beta[OF has_type.App[OF tF A]] by (simp add: subst0_def ObjTrue_def)
  have b2: "\<Gamma> \<turnstile>\<^sub>U (App ?F ObjTrue \<longleftrightarrow>\<^sub>o Eq Prop ?I ObjTrue)" using u_beta[OF has_type.App[OF tF T]] by (simp add: subst0_def ObjTrue_def)
  have e: "\<Gamma> \<turnstile>\<^sub>U Eq Prop B ?I" by (rule u_rc_eq_of_iff[OF B tI u_rc_pc1[OF U_true]]) (insert B tI, (unfold prop_eval.simps)?, auto intro!: has_type.Imp has_type.Conj)
  have t: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop B ?I) (Imp (Eq Prop ?I ObjTrue) (Eq Prop B ObjTrue))" by (rule U_eq_trans[OF B tI T])
  show ?thesis unfolding modal_K_def ObjBox_def by (rule u_rc_pc5[OF l b1 b2 e t]) (insert A B T, (unfold prop_eval.simps)?, auto intro!: has_type.Imp has_type.Eq) qed

lemma U_modal_4: assumes A: "\<Gamma> \<turnstile> A : Prop" shows "\<Gamma> \<turnstile>\<^sub>U modal_4 A" proof -
  let ?F = "Lam Prop (Eq Prop (Eq Prop (Var 0) ObjTrue) ObjTrue)" note T = typed_ObjTrue[of \<Gamma>]
  have tF: "\<Gamma> \<turnstile> ?F : Prop \<rightarrow>\<^sub>o Prop" by (intro has_type.Lam has_type.Eq typed_ObjTrue) simp_all
  have l: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop ObjTrue A) (Imp (App ?F ObjTrue) (App ?F A))" by (rule u_rc_LL[OF T A tF])
  have b1: "\<Gamma> \<turnstile>\<^sub>U (App ?F ObjTrue \<longleftrightarrow>\<^sub>o Eq Prop (Eq Prop ObjTrue ObjTrue) ObjTrue)" using u_beta[OF has_type.App[OF tF T]] by (simp add: subst0_def ObjTrue_def)
  have b2: "\<Gamma> \<turnstile>\<^sub>U (App ?F A \<longleftrightarrow>\<^sub>o Eq Prop (Eq Prop A ObjTrue) ObjTrue)" using u_beta[OF has_type.App[OF tF A]] by (simp add: subst0_def ObjTrue_def)
  have r: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (Eq Prop ObjTrue ObjTrue) ObjTrue" using U_nec[OF U_proves.H[OF H_proves.Ref[OF T]]] unfolding ObjBox_def .
  show ?thesis unfolding modal_4_def ObjBox_def by (rule u_rc_pc5[OF U_eq_sym[OF A T] l b1 b2 r]) (insert A T, (unfold prop_eval.simps)?, auto intro!: has_type.Imp has_type.Eq) qed

lemma u_rc_K: assumes h: "\<Gamma> \<turnstile>\<^sub>U Imp A B" shows "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o A) (\<box>\<^sub>o B)" proof -
  have ta: "\<Gamma> \<turnstile> A : Prop" and tb: "\<Gamma> \<turnstile> B : Prop" using U_formula[OF h] by (auto elim: has_type.cases)
  show ?thesis by (rule U_proves.MP[OF U_nec[OF h] U_modal_K[OF ta tb, unfolded modal_K_def]]) qed

lemma u_rc_congr: assumes C: "Prop # \<Gamma> \<turnstile> C : Prop" and ta: "\<Gamma> \<turnstile> a : Prop" and tb: "\<Gamma> \<turnstile> b : Prop" and eq: "\<Gamma> \<turnstile>\<^sub>U Eq Prop a b" shows "\<Gamma> \<turnstile>\<^sub>U (subst0 a C \<longleftrightarrow>\<^sub>o subst0 b C)" proof -
  have tF: "\<Gamma> \<turnstile> Lam Prop C : Prop \<rightarrow>\<^sub>o Prop" by (rule has_type.Lam[OF C])
  have sa: "\<Gamma> \<turnstile> subst0 a C : Prop" by (rule subst0_preserves_typing[OF C ta])
  have sb: "\<Gamma> \<turnstile> subst0 b C : Prop" by (rule subst0_preserves_typing[OF C tb])
  have eba: "\<Gamma> \<turnstile>\<^sub>U Eq Prop b a" by (rule U_proves.MP[OF eq U_eq_sym[OF ta tb]])
  have l1: "\<Gamma> \<turnstile>\<^sub>U Imp (App (Lam Prop C) a) (App (Lam Prop C) b)" by (rule U_proves.MP[OF eq u_rc_LL[OF ta tb tF]])
  have l2: "\<Gamma> \<turnstile>\<^sub>U Imp (App (Lam Prop C) b) (App (Lam Prop C) a)" by (rule U_proves.MP[OF eba u_rc_LL[OF tb ta tF]])
  have ba: "\<Gamma> \<turnstile>\<^sub>U (App (Lam Prop C) a \<longleftrightarrow>\<^sub>o subst0 a C)" by (rule u_rc_beta_iff[OF has_type.App[OF tF ta]])
  have bb: "\<Gamma> \<turnstile>\<^sub>U (App (Lam Prop C) b \<longleftrightarrow>\<^sub>o subst0 b C)" by (rule u_rc_beta_iff[OF has_type.App[OF tF tb]])
  show ?thesis by (rule u_rc_pc4[OF l1 l2 ba bb has_type.Conj[OF has_type.Imp[OF sa sb] has_type.Imp[OF sb sa]]]) (unfold prop_eval.simps, blast) qed

lemma u_rc_box_iff_eq: assumes ta: "\<Gamma> \<turnstile> A : Prop" and tb: "\<Gamma> \<turnstile> B : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o (A \<longleftrightarrow>\<^sub>o B)) (Eq Prop A B)" proof -
  let ?E = "A \<longleftrightarrow>\<^sub>o B" and ?T = "ObjTrue" and ?C = "Eq Prop (Conj (shift A) (Var 0)) (Conj (shift B) (Var 0))"
  have tE: "\<Gamma> \<turnstile> ?E : Prop" using ta tb by auto
  have tT: "\<Gamma> \<turnstile> ?T : Prop" by (rule typed_ObjTrue)
  have tAT: "\<Gamma> \<turnstile> Conj A ?T : Prop" using ta tT by auto
  have tBT: "\<Gamma> \<turnstile> Conj B ?T : Prop" using tb tT by auto
  have tAE: "\<Gamma> \<turnstile> Conj A ?E : Prop" using ta tE by auto
  have tBE: "\<Gamma> \<turnstile> Conj B ?E : Prop" using tb tE by auto
  have tF: "\<Gamma> \<turnstile> Lam Prop ?C : Prop \<rightarrow>\<^sub>o Prop" by (intro has_type.Lam has_type.Eq has_type.Conj weaken_shift_type_ok[OF ta] weaken_shift_type_ok[OF tb]) simp_all
  have ll: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop ?E ?T) (Imp (App (Lam Prop ?C) ?E) (App (Lam Prop ?C) ?T))" by (rule u_rc_LL[OF tE tT tF])
  have b1: "\<Gamma> \<turnstile>\<^sub>U (App (Lam Prop ?C) ?E \<longleftrightarrow>\<^sub>o Eq Prop (Conj A ?E) (Conj B ?E))" using u_rc_beta_iff[OF has_type.App[OF tF tE]] by (simp add: subst0_def)
  have b2: "\<Gamma> \<turnstile>\<^sub>U (App (Lam Prop ?C) ?T \<longleftrightarrow>\<^sub>o Eq Prop (Conj A ?T) (Conj B ?T))" using u_rc_beta_iff[OF has_type.App[OF tF tT]] by (simp add: subst0_def)
  have thE: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (Conj A ?E) (Conj B ?E)" by (rule u_rc_eq_of_iff[OF tAE tBE U_taut]) (insert tAE tBE, (unfold prop_tautology_def prop_eval.simps)?, blast+)
  have e1: "\<Gamma> \<turnstile>\<^sub>U Eq Prop A (Conj A ?T)" by (rule u_rc_eq_of_iff[OF ta tAT u_rc_pc1[OF U_true]]) (insert ta tAT, (unfold prop_eval.simps)?, blast+)
  have e2: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (Conj B ?T) B" by (rule u_rc_eq_of_iff[OF tBT tb u_rc_pc1[OF U_true]]) (insert tb tBT, (unfold prop_eval.simps)?, blast+)
  have t1: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop A (Conj A ?T)) (Imp (Eq Prop (Conj A ?T) (Conj B ?T)) (Eq Prop A (Conj B ?T)))" by (rule U_eq_trans[OF ta tAT tBT])
  have t2: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop A (Conj B ?T)) (Imp (Eq Prop (Conj B ?T) B) (Eq Prop A B))" by (rule U_eq_trans[OF ta tBT tb])
  have s: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop ?E ?T) (Eq Prop (Conj A ?T) (Conj B ?T))" by (rule u_rc_pc4[OF thE ll b1 b2]) (insert tE tT tAT tBT, (unfold prop_eval.simps)?, blast+)
  have r: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop ?E ?T) (Eq Prop A B)" by (rule u_rc_pc5[OF s e1 e2 t1 t2]) (insert tE tT ta tb, (unfold prop_eval.simps)?, blast+)
  show ?thesis using r by (simp add: ObjBox_def) qed

lemma u_rcR_iff: assumes a: "\<Gamma> \<turnstile> a : Prop" and b: "\<Gamma> \<turnstile> b : Prop" shows "\<Gamma> \<turnstile>\<^sub>U (rcR a b \<longleftrightarrow>\<^sub>o Forall rc_u (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift b)) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (shift a))))))))" proof -
  let ?B = "\<lambda>q. Forall rc_u (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (Var 1)) (Neg (\<box>\<^sub>o (Neg (App (Var 0) q))))))"
  have t1: "\<Gamma> \<turnstile> App rc_R rc_p : Prop \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)" by (rule has_type.App[OF rc_R_ty rc_p_ty])
  have s1: "beta_eta_equiv \<Gamma> (Prop \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)) (App rc_R rc_p) (Lam Prop (Lam Prop (?B (Var 2))))" using rc_be1[OF t1[unfolded rc_R_def]] unfolding rc_R_def by (simp add: subst0_def eval_nat_numeral)
  have s2: "beta_eta_equiv \<Gamma> (Prop \<rightarrow>\<^sub>o Prop) (App (App rc_R rc_p) a) (App (Lam Prop (Lam Prop (?B (Var 2)))) a)" by (rule rc_be_app[OF s1 refl a])
  have t2: "\<Gamma> \<turnstile> App (Lam Prop (Lam Prop (?B (Var 2)))) a : Prop \<rightarrow>\<^sub>o Prop" by (rule beta_eta_equiv_right_type[OF s2])
  have s3: "beta_eta_equiv \<Gamma> (Prop \<rightarrow>\<^sub>o Prop) (App (App rc_R rc_p) a) (Lam Prop (?B (shift (shift a))))" using beta_eta_equiv.Trans[OF s2 rc_be1[OF t2]] by (simp add: subst0_def eval_nat_numeral shift_def)
  have s4: "beta_eta_equiv \<Gamma> Prop (rcR a b) (App (Lam Prop (?B (shift (shift a)))) b)" unfolding rcR_def by (rule rc_be_app[OF s3 refl b])
  have t3: "\<Gamma> \<turnstile> App (Lam Prop (?B (shift (shift a)))) b : Prop" by (rule beta_eta_equiv_right_type[OF s4])
  have s5: "beta_eta_equiv \<Gamma> Prop (rcR a b) (Forall rc_u (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift b)) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (shift a))))))))" using beta_eta_equiv.Trans[OF s4 rc_be1[OF t3]] by (simp add: subst0_def flip: shift_def)
  show ?thesis by (rule U_beta_eta_equiv[OF s5]) qed

lemma u_rcF_iff: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U (rcF x \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (Conj (Neg (rcR x (Neg x))) (Neg (rcR (Neg x) x))))" proof -
  have e: "beta_eta_equiv \<Gamma> Prop (rcF x) (\<box>\<^sub>o (Conj (Neg (rcR x (Neg x))) (Neg (rcR (Neg x) x))))" using rc_be2[OF has_type.App[OF rc_F_ty rc_p_ty, unfolded rc_F_def] x] by (simp add: rcF_def rc_F_def rcR_def subst0_def flip: shift_def)
  show ?thesis by (rule U_beta_eta_equiv[OF e]) qed

lemma u_rcQ_iff: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U (rcQ x \<longleftrightarrow>\<^sub>o Imp (rcF x) x)" proof -
  have e: "beta_eta_equiv \<Gamma> Prop (rcQ x) (Imp (rcF x) x)" using rc_be2[OF has_type.App[OF rc_Q_ty rc_p_ty, unfolded rc_Q_def] x] by (simp add: rcQ_def rc_Q_def rcF_def subst0_def flip: shift_def)
  show ?thesis by (rule U_beta_eta_equiv[OF e]) qed

lemma u_rcP_iff: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U (App rcP x \<longleftrightarrow>\<^sub>o Conj (Neg x) (Neg (rcF x)))" proof -
  have e: "beta_eta_equiv \<Gamma> Prop (App rcP x) (Conj (Neg x) (Neg (rcF x)))" using rc_be2[OF has_type.App[OF rc_P_ty rc_p_ty, unfolded rc_P_def] x] by (simp add: rcP_def rc_P_def rcF_def subst0_def flip: shift_def)
  show ?thesis by (rule U_beta_eta_equiv[OF e]) qed

lemma u_rcPp_iff: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U (App rcPp x \<longleftrightarrow>\<^sub>o Conj x (Neg (rcF x)))" proof -
  have e: "beta_eta_equiv \<Gamma> Prop (App rcPp x) (Conj x (Neg (rcF x)))" using rc_be2[OF has_type.App[OF rc_Pp_ty rc_p_ty, unfolded rc_Pp_def] x] by (simp add: rcPp_def rc_Pp_def rcF_def subst0_def flip: shift_def)
  show ?thesis by (rule U_beta_eta_equiv[OF e]) qed

lemma u_rc1a: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Imp (rcF x) (\<box>\<^sub>o (rcF x))" proof -
  have tF: "\<Gamma> \<turnstile> rcF x : Prop" by (rule rcF_ty[OF x])
  have tB: "\<Gamma> \<turnstile> rcB x : Prop" by (rule rcB_ty[OF x])
  note ib = u_rcF_iff[OF x]
  have h1: "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o (rcB x)) (rcF x)" by (rule u_rc_pc1[OF ib]) (insert tF typed_ObjBox[OF tB], (unfold prop_eval.simps)?, blast+)
  have h2: "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o (\<box>\<^sub>o (rcB x))) (\<box>\<^sub>o (rcF x))" by (rule u_rc_K[OF h1])
  have h3: "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o (rcB x)) (\<box>\<^sub>o (\<box>\<^sub>o (rcB x)))" by (rule U_modal_4[OF tB, unfolded modal_4_def])
  show ?thesis by (rule u_rc_pc3[OF ib h3 h2]) (insert tF typed_ObjBox[OF tF], (unfold prop_eval.simps)?, blast+) qed

lemma u_rc1b: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Imp (rcF x) (Eq Prop (rcQ x) x)" proof -
  have tF: "\<Gamma> \<turnstile> rcF x : Prop" by (rule rcF_ty[OF x])
  have tQ: "\<Gamma> \<turnstile> rcQ x : Prop" by (rule rcQ_ty[OF x])
  have h1: "\<Gamma> \<turnstile>\<^sub>U Imp (rcF x) (rcQ x \<longleftrightarrow>\<^sub>o x)" by (rule u_rc_pc1[OF u_rcQ_iff[OF x]]) (insert tF tQ x, (unfold prop_eval.simps)?, blast+)
  have h2: "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o (rcF x)) (\<box>\<^sub>o (rcQ x \<longleftrightarrow>\<^sub>o x))" by (rule u_rc_K[OF h1])
  show ?thesis by (rule u_rc_pc3[OF u_rc1a[OF x] h2 u_rc_box_iff_eq[OF tQ x]]) (insert tF tQ x, (unfold prop_eval.simps)?, blast+) qed

lemma u_rc1c: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U (rcF (Neg x) \<longleftrightarrow>\<^sub>o rcF x)" proof -
  have tn: "\<Gamma> \<turnstile> Neg x : Prop" using x by auto
  have tnn: "\<Gamma> \<turnstile> Neg (Neg x) : Prop" using x by auto
  have sn: "Prop # \<Gamma> \<turnstile> shift (Neg x) : Prop" by (rule weaken_shift_type_ok[OF tn])
  have e: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (Neg (Neg x)) x" by (rule u_rc_eq_of_iff[OF tnn x U_taut]) (insert tnn x, (unfold prop_tautology_def prop_eval.simps)?, blast+)
  have C1: "Prop # \<Gamma> \<turnstile> rcR (shift (Neg x)) (Var 0) : Prop" by (rule rcR_ty[OF sn]) simp
  have C2: "Prop # \<Gamma> \<turnstile> rcR (Var 0) (shift (Neg x)) : Prop" by (rule rcR_ty[OF _ sn]) simp
  have c1: "\<Gamma> \<turnstile>\<^sub>U (rcR (Neg x) (Neg (Neg x)) \<longleftrightarrow>\<^sub>o rcR (Neg x) x)" using u_rc_congr[OF C1 tnn x e] by (simp add: rcR_def subst0_def)
  have c2: "\<Gamma> \<turnstile>\<^sub>U (rcR (Neg (Neg x)) (Neg x) \<longleftrightarrow>\<^sub>o rcR x (Neg x))" using u_rc_congr[OF C2 tnn x e] by (simp add: rcR_def subst0_def)
  have tB1: "\<Gamma> \<turnstile> rcB (Neg x) : Prop" by (rule rcB_ty[OF tn])
  have tB2: "\<Gamma> \<turnstile> rcB x : Prop" by (rule rcB_ty[OF x])
  have eB: "\<Gamma> \<turnstile>\<^sub>U Eq Prop (rcB (Neg x)) (rcB x)" by (rule u_rc_eq_of_iff[OF tB1 tB2 u_rc_pc2[OF c1 c2]]) (insert tB1 tB2, (unfold prop_eval.simps)?, blast+)
  have bx: "\<Gamma> \<turnstile>\<^sub>U (\<box>\<^sub>o (rcB (Neg x)) \<longleftrightarrow>\<^sub>o \<box>\<^sub>o (rcB x))" using u_rc_congr[of \<Gamma> "\<box>\<^sub>o (Var 0)", OF typed_ObjBox[OF Var_typed_iff[THEN iffD2]] tB1 tB2 eB] by (simp add: subst0_def)
  show ?thesis by (rule u_rc_pc3[OF u_rcF_iff[OF tn] bx u_rcF_iff[OF x]]) (insert rcF_ty[OF tn] rcF_ty[OF x], (unfold prop_eval.simps)?, blast+) qed

lemma u_rc_noP: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Disj (rcQ x) (rcF (rcQ x))" proof -
  have tQ: "\<Gamma> \<turnstile> rcQ x : Prop" by (rule rcQ_ty[OF x])
  have tFx: "\<Gamma> \<turnstile> rcF x : Prop" by (rule rcF_ty[OF x])
  have tFQ: "\<Gamma> \<turnstile> rcF (rcQ x) : Prop" by (rule rcF_ty[OF tQ])
  have tf: "\<Gamma> \<turnstile> App rc_F rc_p : Prop \<rightarrow>\<^sub>o Prop" by (rule has_type.App[OF rc_F_ty rc_p_ty])
  have d: "\<Gamma> \<turnstile>\<^sub>U Imp (Neg (rcQ x)) (rcF x)" by (rule u_rc_pc1[OF u_rcQ_iff[OF x]]) (insert tQ tFx, (unfold prop_eval.simps)?, blast+)
  have ll: "\<Gamma> \<turnstile>\<^sub>U Imp (Eq Prop x (rcQ x)) (Imp (rcF x) (rcF (rcQ x)))" unfolding rcF_def by (rule u_rc_LL[OF x tQ tf])
  show ?thesis by (rule u_rc_pc4[OF d u_rc1b[OF x] U_eq_sym[OF tQ x] ll]) (insert tQ tFQ, (unfold prop_eval.simps)?, blast+) qed

lemma u_rcR_elim: assumes a: "\<Gamma> \<turnstile> a : Prop" and b: "\<Gamma> \<turnstile> b : Prop" and Y: "\<Gamma> \<turnstile> Y : rc_u" shows "\<Gamma> \<turnstile>\<^sub>U Imp (rcR a b) (Imp (App rc_p Y) (Imp (App Y b) (Neg (\<box>\<^sub>o (Neg (App Y a))))))" proof -
  let ?A = "Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift b)) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (shift a))))))"
  note ib = u_rcR_iff[OF a b]
  have f: "\<Gamma> \<turnstile> Forall rc_u ?A : Prop" using U_formula[OF ib] by (auto elim: has_type.cases)
  have ty: "rc_u # \<Gamma> \<turnstile> ?A : Prop" using f by (auto elim: has_type.cases)
  have ui: "\<Gamma> \<turnstile>\<^sub>U Imp (Forall rc_u ?A) (subst0 Y ?A)" using ty Y by (intro U_proves.H H_proves.UI)
  have e: "subst0 Y ?A = Imp (App rc_p Y) (Imp (App Y b) (Neg (\<box>\<^sub>o (Neg (App Y a)))))" by (simp add: subst0_def)
  have tR: "\<Gamma> \<turnstile> rcR a b : Prop" by (rule rcR_ty[OF a b])
  have tS: "\<Gamma> \<turnstile> subst0 Y ?A : Prop" by (rule subst0_preserves_typing[OF ty Y])
  show ?thesis using u_rc_pc2[OF ib ui has_type.Imp[OF tR tS]] unfolding e by simp qed

lemma u_rcR_intro: assumes a: "\<Gamma> \<turnstile> a : Prop" and b: "\<Gamma> \<turnstile> b : Prop" and tP: "\<Gamma> \<turnstile> P : Prop" and h: "rc_u # \<Gamma> \<turnstile>\<^sub>U Imp (shift P) (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift b)) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (shift a)))))))" shows "\<Gamma> \<turnstile>\<^sub>U Imp P (rcR a b)" proof -
  have ty: "rc_u # \<Gamma> \<turnstile> Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift b)) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (shift a)))))) : Prop" using U_formula[OF h] by (auto elim: has_type.cases)
  note gen = U_proves.Gen[OF tP ty h]
  show ?thesis by (rule u_rc_pc2[OF gen u_rcR_iff[OF a b]]) (insert tP rcR_ty[OF a b], (unfold prop_eval.simps)?, blast+) qed

theorem u_rc2: assumes x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o (App rc_p rcP)) (Imp (\<box>\<^sub>o (App rc_p rcPp)) (rcF (rcQ x)))" proof -
  let ?q = "rcQ x" let ?n = "Neg (rcQ x)" let ?a = "App rc_p rcP" let ?b = "App rc_p rcPp"
  have tq: "\<Gamma> \<turnstile> ?q : Prop" by (rule rcQ_ty[OF x])
  have tn: "\<Gamma> \<turnstile> ?n : Prop" using tq by auto
  have tP: "\<Gamma> \<turnstile> rcP : rc_u" and tPp: "\<Gamma> \<turnstile> rcPp : rc_u" by (rule rcP_ty, rule rcPp_ty)
  have ta: "\<Gamma> \<turnstile> ?a : Prop" and tb: "\<Gamma> \<turnstile> ?b : Prop" by (rule rc_pure_ty[OF tP], rule rc_pure_ty[OF tPp])
  have tFq: "\<Gamma> \<turnstile> rcF ?q : Prop" by (rule rcF_ty[OF tq])
  have tB: "\<Gamma> \<turnstile> rcB ?q : Prop" by (rule rcB_ty[OF tq])
  have tR1: "\<Gamma> \<turnstile> rcR ?q ?n : Prop" by (rule rcR_ty[OF tq tn])
  have tR2: "\<Gamma> \<turnstile> rcR ?n ?q : Prop" by (rule rcR_ty[OF tn tq])
  have tPq: "\<Gamma> \<turnstile> App rcP ?q : Prop" and tPn: "\<Gamma> \<turnstile> App rcP ?n : Prop" by (rule has_type.App[OF tP tq], rule has_type.App[OF tP tn])
  have tPpq: "\<Gamma> \<turnstile> App rcPp ?q : Prop" and tPpn: "\<Gamma> \<turnstile> App rcPp ?n : Prop" by (rule has_type.App[OF tPp tq], rule has_type.App[OF tPp tn])
  note t0 = u_rc_noP[OF x] and fneg = u_rc1c[OF tq] and u = u_rcF_iff[OF tq]
  note T = U_modal_T[OF tB, unfolded modal_T_def]
  have s1: "\<Gamma> \<turnstile>\<^sub>U Imp (rcF ?q) (rcB ?q)" by (rule u_rc_pc2[OF u T]) (insert tFq tB, (unfold prop_eval.simps)?, blast+)
  have n1: "\<Gamma> \<turnstile>\<^sub>U Neg (App rcP ?q)" by (rule u_rc_pc2[OF t0 u_rcP_iff[OF tq]]) (insert tPq, (unfold prop_eval.simps)?, blast+)
  have n2: "\<Gamma> \<turnstile>\<^sub>U Neg (App rcPp ?n)" by (rule u_rc_pc3[OF t0 fneg u_rcPp_iff[OF tn]]) (insert tPpn, (unfold prop_eval.simps)?, blast+)
  note b1 = U_nec[OF n1] and b2 = U_nec[OF n2]
  have s3: "\<Gamma> \<turnstile>\<^sub>U Imp (Conj ?q (Neg (rcF ?q))) (App rcP ?n)" by (rule u_rc_pc2[OF u_rcP_iff[OF tn] fneg]) (insert tq tFq tPn, (unfold prop_eval.simps)?, blast+)
  have s4: "\<Gamma> \<turnstile>\<^sub>U Imp (Conj ?q (Neg (rcF ?q))) (App rcPp ?q)" by (rule u_rc_pc1[OF u_rcPp_iff[OF tq]]) (insert tq tFq tPpq, (unfold prop_eval.simps)?, blast+)
  have s5: "\<Gamma> \<turnstile>\<^sub>U Imp ?a (Neg (rcR ?q ?n))" by (rule u_rc_pc5[OF u_rcR_elim[OF tq tn tP] b1 s1 t0 s3]) (insert ta tR1, (unfold prop_eval.simps)?, blast+)
  have s6: "\<Gamma> \<turnstile>\<^sub>U Imp ?b (Neg (rcR ?n ?q))" by (rule u_rc_pc5[OF u_rcR_elim[OF tn tq tPp] b2 s1 t0 s4]) (insert tb tR2, (unfold prop_eval.simps)?, blast+)
  have G0: "\<Gamma> \<turnstile>\<^sub>U Imp (Conj ?a ?b) (rcB ?q)" by (rule u_rc_pc2[OF s5 s6]) (insert ta tb tB, (unfold prop_eval.simps)?, blast+)
  have k0: "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o (Conj ?a ?b)) (\<box>\<^sub>o (rcB ?q))" by (rule u_rc_K[OF G0])
  have c0: "\<Gamma> \<turnstile>\<^sub>U Imp ?a (Imp ?b (Conj ?a ?b))" by (rule U_taut) (insert ta tb, (unfold prop_tautology_def prop_eval.simps)?, blast+)
  have c1: "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o ?a) (\<box>\<^sub>o (Imp ?b (Conj ?a ?b)))" by (rule u_rc_K[OF c0])
  have c2: "\<Gamma> \<turnstile>\<^sub>U Imp (\<box>\<^sub>o (Imp ?b (Conj ?a ?b))) (Imp (\<box>\<^sub>o ?b) (\<box>\<^sub>o (Conj ?a ?b)))" using ta tb by (intro U_modal_K[unfolded modal_K_def]) auto
  show ?thesis by (rule u_rc_pc4[OF c1 c2 k0 u]) (insert typed_ObjBox[OF ta] typed_ObjBox[OF tb] tFq, (unfold prop_eval.simps)?, blast+) qed

lemma u_rc_ac: assumes F: "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" and a: "\<Gamma> \<turnstile> a : \<sigma>" shows "\<Gamma> \<turnstile>\<^sub>U Imp (pp_application_closure \<sigma> \<tau>) (Imp (Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) (pp_pure \<sigma> a)) (pp_pure \<tau> (App F a)))" proof -
  let ?A2 = "\<lambda>f. Imp (Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) f) (pp_pure \<sigma> (Var 0))) (pp_pure \<tau> (App f (Var 0)))"
  have ty: "\<Gamma> \<turnstile> pp_application_closure \<sigma> \<tau> : Prop" by (rule infer_type_sound) (simp add: pp_application_closure_def pp_pure_def pp_Pure_def lookup_def)
  have d: "pp_application_closure \<sigma> \<tau> = Forall (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Forall \<sigma> (?A2 (Var 1)))" by (simp add: pp_application_closure_def)
  have t1: "(\<sigma> \<rightarrow>\<^sub>o \<tau>) # \<Gamma> \<turnstile> Forall \<sigma> (?A2 (Var 1)) : Prop" using ty unfolding d by (auto elim: has_type.cases)
  have e1: "subst0 F (Forall \<sigma> (?A2 (Var 1))) = Forall \<sigma> (?A2 (shift F))" by (simp add: subst0_def pp_pure_def pp_Pure_def flip: shift_def)
  have ui1: "\<Gamma> \<turnstile>\<^sub>U Imp (pp_application_closure \<sigma> \<tau>) (Forall \<sigma> (?A2 (shift F)))" unfolding d e1[symmetric] using t1 F by (intro U_proves.H H_proves.UI)
  have t2: "\<Gamma> \<turnstile> Forall \<sigma> (?A2 (shift F)) : Prop" using subst0_preserves_typing[OF t1 F] unfolding e1 .
  have t3: "\<sigma> # \<Gamma> \<turnstile> ?A2 (shift F) : Prop" using t2 by (auto elim: has_type.cases)
  have e2: "subst0 a (?A2 (shift F)) = Imp (Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) (pp_pure \<sigma> a)) (pp_pure \<tau> (App F a))" by (simp add: subst0_def pp_pure_def pp_Pure_def)
  have ui2: "\<Gamma> \<turnstile>\<^sub>U Imp (Forall \<sigma> (?A2 (shift F))) (Imp (Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) (pp_pure \<sigma> a)) (pp_pure \<tau> (App F a)))" unfolding e2[symmetric] using t3 a by (intro U_proves.H H_proves.UI)
  have tr: "\<Gamma> \<turnstile> Imp (Conj (pp_pure (\<sigma> \<rightarrow>\<^sub>o \<tau>) F) (pp_pure \<sigma> a)) (pp_pure \<tau> (App F a)) : Prop" using subst0_preserves_typing[OF t3 a] unfolding e2 .
  show ?thesis by (rule u_rc_pc2[OF ui1 ui2 has_type.Imp[OF ty tr]]) (unfold prop_eval.simps, blast) qed

lemma u_rc_piP:
  "\<Gamma> \<turnstile>\<^sub>U Imp (pp_application_closure rc_c rc_u) (Imp (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_P) (Imp (pp_pure rc_c rc_p) (App rc_p rcP)))" proof -
  note a1 = u_rc_ac[OF rc_P_ty rc_p_ty, of \<Gamma>]
  have ty: "\<Gamma> \<turnstile> pp_application_closure rc_c rc_u : Prop" using U_formula[OF a1] by (auto elim: has_type.cases)
  show ?thesis by (rule u_rc_pc1[OF a1]) (insert ty typed_pp_pure[OF rc_P_ty] typed_pp_pure[OF rc_p_ty] rc_pure_ty[OF rcP_ty], (unfold rcP_def pp_pure_def prop_eval.simps)?, blast+) qed

lemma u_rc_piPp:
  "\<Gamma> \<turnstile>\<^sub>U Imp (pp_application_closure rc_c rc_u) (Imp (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_Pp) (Imp (pp_pure rc_c rc_p) (App rc_p rcPp)))" proof -
  note a1 = u_rc_ac[OF rc_Pp_ty rc_p_ty, of \<Gamma>]
  have ty: "\<Gamma> \<turnstile> pp_application_closure rc_c rc_u : Prop" using U_formula[OF a1] by (auto elim: has_type.cases)
  show ?thesis by (rule u_rc_pc1[OF a1]) (insert ty typed_pp_pure[OF rc_Pp_ty] typed_pp_pure[OF rc_p_ty] rc_pure_ty[OF rcPp_ty], (unfold rcPp_def pp_pure_def prop_eval.simps)?, blast+) qed

lemma u_rcW_iff: assumes Y: "\<Gamma> \<turnstile> Y : rc_u" and x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U (App (rcW Y) x \<longleftrightarrow>\<^sub>o App Y (rcQ x))" proof -
  let ?B = "\<lambda>q. Lam Prop (App (Var 1) (App (App rc_Q q) (Var 0)))"
  have s0: "beta_eta_equiv \<Gamma> (rc_u \<rightarrow>\<^sub>o rc_u) (App rc_W rc_p) (Lam rc_u (?B rc_p))" using rc_be1[OF has_type.App[OF rc_W_ty rc_p_ty, unfolded rc_W_def]] unfolding rc_W_def by (simp add: subst0_def eval_nat_numeral)
  have s1: "beta_eta_equiv \<Gamma> rc_u (rcW Y) (App (Lam rc_u (?B rc_p)) Y)" unfolding rcW_def by (rule rc_be_app[OF s0 refl Y])
  have s2: "beta_eta_equiv \<Gamma> rc_u (rcW Y) (Lam Prop (App (shift Y) (App (App rc_Q rc_p) (Var 0))))" using beta_eta_equiv.Trans[OF s1 rc_be1[OF beta_eta_equiv_right_type[OF s1]]] by (simp add: subst0_def flip: shift_def)
  have s3: "beta_eta_equiv \<Gamma> Prop (App (rcW Y) x) (App (Lam Prop (App (shift Y) (App (App rc_Q rc_p) (Var 0)))) x)" by (rule rc_be_app[OF s2 refl x])
  have s4: "beta_eta_equiv \<Gamma> Prop (App (rcW Y) x) (App Y (rcQ x))" using beta_eta_equiv.Trans[OF s3 rc_be1[OF beta_eta_equiv_right_type[OF s3]]] by (simp add: rcQ_def subst0_def)
  show ?thesis by (rule U_beta_eta_equiv[OF s4]) qed

lemma u_rcUni_inst: assumes s: "\<Gamma> \<turnstile> s : Prop" and y: "\<Gamma> \<turnstile> y : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Imp (rcUni s) (rcR s y)" proof -
  have t: "Prop # \<Gamma> \<turnstile> rcR (shift s) (Var 0) : Prop" by (rule rcR_ty[OF weaken_shift_type_ok[OF s]]) simp
  have e: "subst0 y (rcR (shift s) (Var 0)) = rcR s y" by (simp add: rcR_def subst0_def)
  show ?thesis unfolding rcUni_def e[symmetric] using t y by (intro U_proves.H H_proves.UI) qed

lemma u_rc_stepU: assumes r: "\<Gamma> \<turnstile> r : Prop" and Y: "\<Gamma> \<turnstile> Y : rc_u" shows "\<Gamma> \<turnstile>\<^sub>U Imp rcHU (Imp (rcUni r) (Imp (rcF (rcQ r)) (Imp (App rc_p Y) (Imp (App Y (Neg (rcQ r))) (Neg (\<box>\<^sub>o (Neg (App Y (rcQ r)))))))))" proof -
  let ?e = "rcQ r" let ?n = "Neg (rcQ r)" let ?W = "rcW Y"
  have te: "\<Gamma> \<turnstile> ?e : Prop" by (rule rcQ_ty[OF r])
  have tn: "\<Gamma> \<turnstile> ?n : Prop" using te by blast
  have tW: "\<Gamma> \<turnstile> ?W : rc_u" by (rule rcW_ty[OF Y])
  have tQn: "\<Gamma> \<turnstile> rcQ ?n : Prop" by (rule rcQ_ty[OF tn])
  note a1 = u_rc_ac[OF rc_W_ty rc_p_ty, of \<Gamma>] and a2 = u_rc_ac[OF has_type.App[OF rc_W_ty rc_p_ty] Y]
  note w1 = u_rcW_iff[OF Y r] and w2 = u_rcW_iff[OF Y tn]
  have tYe: "\<Gamma> \<turnstile> App Y ?e : Prop" and tYn: "\<Gamma> \<turnstile> App Y ?n : Prop" and tYQ: "\<Gamma> \<turnstile> App Y (rcQ ?n) : Prop" by (rule has_type.App[OF Y te], rule has_type.App[OF Y tn], rule has_type.App[OF Y tQn])
  have tWr: "\<Gamma> \<turnstile> App ?W r : Prop" and tWn: "\<Gamma> \<turnstile> App ?W ?n : Prop" by (rule has_type.App[OF tW r], rule has_type.App[OF tW tn])
  have k0: "\<Gamma> \<turnstile>\<^sub>U Imp (Neg (App Y ?e)) (Neg (App ?W r))" by (rule u_rc_pc1[OF w1]) (insert tYe tWr, (unfold prop_eval.simps)?, blast+)
  note k = u_rc_K[OF k0]
  have s1: "\<Gamma> \<turnstile>\<^sub>U Imp (rcF ?e) (Imp (App Y ?n) (App Y (rcQ ?n)))" by (rule u_rc_pc4[OF u_rc1b[OF tn] u_rc1c[OF te] U_eq_sym[OF tQn tn] u_rc_LL[OF tn tQn Y]]) (insert rcF_ty[OF te] tYn tYQ, (unfold prop_eval.simps)?, blast+)
  have t1: "\<Gamma> \<turnstile>\<^sub>U Imp (rcF ?e) (Imp (App Y ?n) (App ?W ?n))" by (rule u_rc_pc2[OF s1 w2]) (insert rcF_ty[OF te] tYn tWn, (unfold prop_eval.simps)?, blast+)
  have tH: "\<Gamma> \<turnstile> rcHU : Prop" by (rule rcHU_ty)
  have s3: "\<Gamma> \<turnstile>\<^sub>U Imp rcHU (Imp (App rc_p Y) (App rc_p ?W))" by (rule u_rc_pc2[OF a1 a2]) (insert tH rc_pure_ty[OF Y] rc_pure_ty[OF tW], (unfold rcHU_def rcW_def pp_pure_def prop_eval.simps)?, blast+)
  have tU: "\<Gamma> \<turnstile> rcUni r : Prop" by (rule rcUni_ty[OF r])
  have tGoal: "\<Gamma> \<turnstile> Imp rcHU (Imp (rcUni r) (Imp (rcF ?e) (Imp (App rc_p Y) (Imp (App Y ?n) (Neg (\<box>\<^sub>o (Neg (App Y ?e)))))))) : Prop" using tH tU rcF_ty[OF te] rc_pure_ty[OF Y] tYn typed_ObjBox[OF has_type.Neg[OF tYe]] by blast
  show ?thesis by (rule u_rc_pc5[OF s3 u_rcUni_inst[OF r tn] u_rcR_elim[OF r tn tW] t1 k tGoal]) (unfold prop_eval.simps, blast) qed

theorem u_rc_coreU: "[] \<turnstile>\<^sub>U Imp rcHU (Imp rcBP (Imp rcBQ (Neg rcExUni)))" proof -
  let ?G = "[Prop]" let ?G1 = "[rc_u, Prop]" let ?r = "Var 0"
  have r: "?G \<turnstile> ?r : Prop" by simp
  have r1: "?G1 \<turnstile> Var 1 : Prop" by simp
  have y1: "?G1 \<turnstile> Var 0 : rc_u" by simp
  let ?e = "rcQ ?r" let ?n = "Neg (rcQ ?r)" let ?P = "Conj rcHU (Conj (rcUni ?r) (rcF ?e))"
  have te: "?G \<turnstile> ?e : Prop" by (rule rcQ_ty[OF r])
  have tn: "?G \<turnstile> ?n : Prop" using te by blast
  have tf: "?G \<turnstile> rcUni ?r : Prop" by (rule rcUni_ty[OF r])
  have tP: "?G \<turnstile> ?P : Prop" using rcHU_ty[of ?G] rcF_ty[OF te] tf by blast
  have sh: "shift ?P = Conj rcHU (Conj (rcUni (Var 1)) (rcF (rcQ (Var 1))))" by (simp add: rc_sft rcUni_shift)
  have sh2: "shift ?n = Neg (rcQ (Var 1))" and sh3: "shift ?e = rcQ (Var 1)" by (simp_all add: rc_sft)
  note st = u_rc_stepU[OF r1 y1]
  have s: "?G1 \<turnstile>\<^sub>U Imp (shift ?P) (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift ?n)) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (shift ?e)))))))" unfolding sh sh2 sh3 proof (rule u_rc_pc1[OF st]) show "?G1 \<turnstile> Imp (Conj rcHU (Conj (rcUni (Var 1)) (rcF (rcQ (Var 1))))) (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (Neg (rcQ (Var 1)))) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (rcQ (Var 1)))))))) : Prop" using U_formula[OF st] rcHU_ty[of ?G1] rcUni_ty[OF r1] rcF_ty[OF rcQ_ty[OF r1]] by (auto elim!: has_type.cases[of _ "Imp _ _"]) qed (unfold prop_eval.simps, blast)
  note ri = u_rcR_intro[OF te tn tP s]
  note u = u_rcF_iff[OF te] and T = U_modal_T[OF rcB_ty[OF te], unfolded modal_T_def]
  have c: "?G \<turnstile>\<^sub>U Imp rcHU (Imp rcBP (Imp rcBQ (Neg (rcUni ?r))))" by (rule u_rc_pc4[OF ri u T u_rc2[OF r]]) (insert rcHU_ty[of ?G] rcBP_ty[of ?G] rcBQ_ty[of ?G] tf, (unfold prop_eval.simps)?, blast+)
  let ?Q = "Neg (Conj rcHU (Conj rcBP rcBQ))"
  have tQ: "\<Gamma> \<turnstile> ?Q : Prop" for \<Gamma> using rcHU_ty[of \<Gamma>] rcBP_ty[of \<Gamma>] rcBQ_ty[of \<Gamma>] by blast
  have shq: "shift ?Q = ?Q" by (simp add: rc_sft rcP_def rcPp_def)
  have i: "?G \<turnstile>\<^sub>U Imp (rcUni ?r) (shift ?Q)" unfolding shq by (rule u_rc_pc1[OF c]) (insert tf tQ[of ?G], (unfold prop_eval.simps)?, blast+)
  note inst = U_proves.Inst[OF tf tQ i]
  have tE: "[] \<turnstile> rcExUni : Prop" unfolding rcExUni_def by (rule has_type.Exists[OF tf])
  show ?thesis by (rule u_rc_pc1[OF inst[folded rcExUni_def]]) (insert tE rcBP_ty[of "[]"] rcBQ_ty[of "[]"] rcHU_ty[of "[]"], (unfold prop_eval.simps)?, blast+) qed

definition zI :: "oterm \<Rightarrow> oterm" where "zI A = Imp (pp_pure Prop A) (Imp A (\<box>\<^sub>o A))"

definition rcS :: oterm where "rcS = Conj rcHU (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_P) (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_Pp) (Conj (pp_application_closure rc_c rc_u) (Conj (pp_application_closure rc_u Prop) (Conj (zI (App rc_p rcP)) (zI (App rc_p rcPp)))))))"

theorem u_S: "[] \<turnstile>\<^sub>U Imp rcS (Neg rcExUni)" proof -
  note p1 = u_rc_piP[of "[]"] and p2 = u_rc_piPp[of "[]"] and a1 = u_rc_ac[OF rc_p_ty rcP_ty, of "[]"] and a2 = u_rc_ac[OF rc_p_ty rcPp_ty, of "[]"]
  have tU: "[] \<turnstile> rcExUni : Prop" using U_formula[OF u_rc_coreU] by (auto elim!: has_type.cases[of _ "Imp _ _"] has_type.cases[of _ "Neg _"])
  have tH: "[] \<turnstile> rcHU : Prop" by (rule rcHU_ty)
  have tp: "[] \<turnstile> App rc_p rcP : Prop" and tq: "[] \<turnstile> App rc_p rcPp : Prop" by (rule rc_pure_ty[OF rcP_ty], rule rc_pure_ty[OF rcPp_ty])
  have tS: "[] \<turnstile> Imp rcS (Neg rcExUni) : Prop" unfolding rcS_def zI_def using tH tU tp tq U_formula[OF p1] U_formula[OF p2] U_formula[OF a1] U_formula[OF a2] typed_ObjBox[OF tp] typed_ObjBox[OF tq] typed_pp_pure[OF tp] typed_pp_pure[OF tq] by (auto elim!: has_type.cases[of _ "Imp _ _"] has_type.cases[of _ "Conj _ _"] intro!: has_type.Imp has_type.Conj has_type.Neg)
  show ?thesis by (rule u_rc_pc5[OF p1 p2 a1 a2 u_rc_coreU tS]) (unfold rcS_def zI_def rcHU_def pp_pure_def rcP_def rcPp_def prop_eval.simps, blast) qed

section \<open>6. Fundamental means universal, in U\<close>

text \<open>By Loupe, with Jacob, 2026-11-06; not Branden Fitelson's. T3 in U, which is the note's H-plus: LP at P, P', W and
  the negator; App at four type pairs; zE; Rec; EF as an existence claim alone; PP_u; as one implication to falsity.
  Each premise at a point. u_S gives No Universal Proposition; the new part is Fundamental Means Universal in U.\<close>

definition k_C :: oterm where "k_C = Lam rc_u (Lam Prop (Neg (App (Var 1) (Var 0))))"

definition kN :: "oterm \<Rightarrow> oterm" where "kN Y = App k_C Y"

definition k_EF :: oterm where "k_EF = Exists Prop (pp_fun Prop (Var 0))"

lemma k_C_ty: "\<Gamma> \<turnstile> k_C : rc_u \<rightarrow>\<^sub>o rc_u" by (rule infer_type_sound) (simp add: k_C_def lookup_def)

lemma k_C_consts: "consts_of k_C = {}" by (simp add: k_C_def)

lemma kN_ty: "\<Gamma> \<turnstile> Y : rc_u \<Longrightarrow> \<Gamma> \<turnstile> kN Y : rc_u" unfolding kN_def by (rule has_type.App[OF k_C_ty])

lemma u_kN_iff: assumes Y: "\<Gamma> \<turnstile> Y : rc_u" and x: "\<Gamma> \<turnstile> x : Prop" shows "\<Gamma> \<turnstile>\<^sub>U (App (kN Y) x \<longleftrightarrow>\<^sub>o Neg (App Y x))" proof -
  have s0: "beta_eta_equiv \<Gamma> rc_u (kN Y) (Lam Prop (Neg (App (shift Y) (Var 0))))" using rc_be1[OF has_type.App[OF k_C_ty Y, unfolded k_C_def]] unfolding kN_def k_C_def by (simp add: subst0_def flip: shift_def)
  have s1: "beta_eta_equiv \<Gamma> Prop (App (kN Y) x) (App (Lam Prop (Neg (App (shift Y) (Var 0)))) x)" by (rule rc_be_app[OF s0 refl x])
  have s2: "beta_eta_equiv \<Gamma> Prop (App (kN Y) x) (Neg (App Y x))" using beta_eta_equiv.Trans[OF s1 rc_be1[OF beta_eta_equiv_right_type[OF s1]]] by (simp add: subst0_def)
  show ?thesis by (rule U_beta_eta_equiv[OF s2]) qed

lemma u_rec: assumes X: "\<Gamma> \<turnstile> X : rc_u" and r: "\<Gamma> \<turnstile> r : Prop" and z: "\<Gamma> \<turnstile> z : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Imp pp_unary_recombination (Imp (Conj (pp_pure rc_u X) (pp_fun Prop r)) (Imp (\<box>\<^sub>o (App X r)) (App X z)))" proof -
  let ?A1 = "Forall Prop (Imp (Conj (pp_pure rc_u (Var 1)) (pp_fun Prop (Var 0))) (Imp (\<box>\<^sub>o (App (Var 1) (Var 0))) (Forall Prop (App (Var 2) (Var 0)))))"
  let ?A2 = "Imp (Conj (pp_pure rc_u (shift X)) (pp_fun Prop (Var 0))) (Imp (\<box>\<^sub>o (App (shift X) (Var 0))) (Forall Prop (App (shift (shift X)) (Var 0))))"
  let ?A3 = "Imp (Conj (pp_pure rc_u X) (pp_fun Prop r)) (Imp (\<box>\<^sub>o (App X r)) (Forall Prop (App (shift X) (Var 0))))"
  have ty: "\<Gamma> \<turnstile> pp_unary_recombination : Prop" by (rule infer_type_sound) (simp add: pp_unary_recombination_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)
  have d: "pp_unary_recombination = Forall rc_u ?A1" by (simp add: pp_unary_recombination_def)
  have t1: "rc_u # \<Gamma> \<turnstile> ?A1 : Prop" using ty unfolding d by (auto elim: has_type.cases)
  have e1: "subst0 X ?A1 = Forall Prop ?A2" by (simp add: subst0_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def eval_nat_numeral flip: shift_def)
  have ui1: "\<Gamma> \<turnstile>\<^sub>U Imp pp_unary_recombination (Forall Prop ?A2)" unfolding d e1[symmetric] using t1 X by (intro U_proves.H H_proves.UI)
  have t2: "\<Gamma> \<turnstile> Forall Prop ?A2 : Prop" using subst0_preserves_typing[OF t1 X] unfolding e1 .
  have t3: "Prop # \<Gamma> \<turnstile> ?A2 : Prop" using t2 by (auto elim: has_type.cases)
  have e2: "subst0 r ?A2 = ?A3" by (simp add: subst0_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def flip: shift_def)
  have ui2: "\<Gamma> \<turnstile>\<^sub>U Imp (Forall Prop ?A2) ?A3" unfolding e2[symmetric] using t3 r by (intro U_proves.H H_proves.UI)
  have t4: "\<Gamma> \<turnstile> ?A3 : Prop" using subst0_preserves_typing[OF t3 r] unfolding e2 .
  have t5: "\<Gamma> \<turnstile> Forall Prop (App (shift X) (Var 0)) : Prop" using t4 by (auto elim: has_type.cases simp: ObjBox_def)
  have t6: "Prop # \<Gamma> \<turnstile> App (shift X) (Var 0) : Prop" using t5 by (auto elim: has_type.cases)
  have ui3: "\<Gamma> \<turnstile>\<^sub>U Imp (Forall Prop (App (shift X) (Var 0))) (App X z)" using U_proves.H[OF H_proves.UI[OF t6 z]] by (simp add: subst0_def)
  have tz: "\<Gamma> \<turnstile> App X z : Prop" by (rule has_type.App[OF X z])
  have tc: "\<Gamma> \<turnstile> Conj (pp_pure rc_u X) (pp_fun Prop r) : Prop" using typed_pp_pure[OF X] typed_pp_fun[OF r] by auto
  have tb: "\<Gamma> \<turnstile> \<box>\<^sub>o (App X r) : Prop" by (rule typed_ObjBox[OF has_type.App[OF X r]])
  show ?thesis by (rule u_rc_pc3[OF ui1 ui2 ui3]) (insert ty tc tb tz, (unfold prop_eval.simps)?, blast+) qed

lemma u_zI: assumes A: "\<Gamma> \<turnstile> A : Prop" shows "\<Gamma> \<turnstile>\<^sub>U Imp pp_zeroary_exhaustion (zI A)" proof -
  let ?B = "Imp (pp_pure Prop (Var 0)) (Imp (Var 0) (\<box>\<^sub>o (Var 0)))"
  have ty: "\<Gamma> \<turnstile> pp_zeroary_exhaustion : Prop" by (rule infer_type_sound) (simp add: pp_zeroary_exhaustion_def pp_pure_def pp_Pure_def ObjBox_def ObjTrue_def lookup_def)
  have d: "pp_zeroary_exhaustion = Forall Prop ?B" by (simp add: pp_zeroary_exhaustion_def)
  have t1: "Prop # \<Gamma> \<turnstile> ?B : Prop" using ty unfolding d by (auto elim: has_type.cases)
  have e: "subst0 A ?B = zI A" by (simp add: zI_def subst0_def pp_pure_def pp_Pure_def)
  show ?thesis unfolding d e[symmetric] using t1 A by (intro U_proves.H H_proves.UI) qed

definition rcH5 :: oterm where "rcH5 = Conj (pp_pure (rc_u \<rightarrow>\<^sub>o rc_u) k_C) (Conj (pp_application_closure rc_u rc_u) pp_unary_recombination)"

lemma rcH5_ty: "\<Gamma> \<turnstile> rcH5 : Prop" by (rule infer_type_sound) (simp add: rcH5_def k_C_def pp_application_closure_def pp_unary_recombination_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)

lemma rcH5_shift[simp]: "shift rcH5 = rcH5" by (simp add: rcH5_def k_C_def pp_application_closure_def pp_unary_recombination_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def shift_def ObjBox_def ObjTrue_def eval_nat_numeral)

lemma u_fun_step: assumes r: "\<Gamma> \<turnstile> r : Prop" and y: "\<Gamma> \<turnstile> y : Prop" and Y: "\<Gamma> \<turnstile> Y : rc_u" shows "\<Gamma> \<turnstile>\<^sub>U Imp rcH5 (Imp (pp_fun Prop r) (Imp (App rc_p Y) (Imp (App Y y) (Neg (\<box>\<^sub>o (Neg (App Y r)))))))" proof -
  let ?X = "kN Y"
  have tX: "\<Gamma> \<turnstile> ?X : rc_u" by (rule kN_ty[OF Y])
  have tYr: "\<Gamma> \<turnstile> App Y r : Prop" and tYy: "\<Gamma> \<turnstile> App Y y : Prop" by (rule has_type.App[OF Y r], rule has_type.App[OF Y y])
  have tXr: "\<Gamma> \<turnstile> App ?X r : Prop" and tXy: "\<Gamma> \<turnstile> App ?X y : Prop" by (rule has_type.App[OF tX r], rule has_type.App[OF tX y])
  note a = u_rc_ac[OF k_C_ty Y] and xi1 = u_kN_iff[OF Y r] and xi2 = u_kN_iff[OF Y y]
  have k0: "\<Gamma> \<turnstile>\<^sub>U Imp (Neg (App Y r)) (App ?X r)" by (rule u_rc_pc1[OF xi1]) (insert tYr tXr, (unfold prop_eval.simps)?, blast+)
  note k = u_rc_K[OF k0] and rc = u_rec[OF tX r y]
  have tGoal: "\<Gamma> \<turnstile> Imp rcH5 (Imp (pp_fun Prop r) (Imp (App rc_p Y) (Imp (App Y y) (Neg (\<box>\<^sub>o (Neg (App Y r))))))) : Prop" using rcH5_ty[of \<Gamma>] typed_pp_fun[OF r] rc_pure_ty[OF Y] tYy typed_ObjBox[OF has_type.Neg[OF tYr]] by blast
  show ?thesis by (rule u_rc_pc4[OF a k rc xi2 tGoal]) (unfold rcH5_def kN_def pp_pure_def prop_eval.simps, blast) qed

lemma k_fun_shift: "shift (pp_fun Prop (Var n)) = pp_fun Prop (Var (Suc n))" by (simp add: pp_fun_def pp_Fun_def shift_def)

lemma u_uni_ctx: "[Prop] \<turnstile>\<^sub>U Imp rcH5 (Imp (pp_fun Prop (Var 0)) (rcUni (Var 0)))" proof -
  let ?G0 = "[Prop]" let ?G1 = "[Prop, Prop]" let ?G2 = "[rc_u, Prop, Prop]"
  let ?P0 = "Conj rcH5 (pp_fun Prop (Var 0))" let ?P1 = "Conj rcH5 (pp_fun Prop (Var 1))"
  have r0: "?G0 \<turnstile> Var 0 : Prop" by simp
  have r1: "?G1 \<turnstile> Var 1 : Prop" and y1: "?G1 \<turnstile> Var 0 : Prop" by simp_all
  have r2: "?G2 \<turnstile> Var 2 : Prop" and y2: "?G2 \<turnstile> Var 1 : Prop" and Y2: "?G2 \<turnstile> Var 0 : rc_u" by (simp_all add: eval_nat_numeral lookup_def)
  have tF0: "?G0 \<turnstile> pp_fun Prop (Var 0) : Prop" by (rule typed_pp_fun[OF r0])
  have tF1: "?G1 \<turnstile> pp_fun Prop (Var 1) : Prop" by (rule typed_pp_fun[OF r1])
  have tF2: "?G2 \<turnstile> pp_fun Prop (Var 2) : Prop" by (rule typed_pp_fun[OF r2])
  have tP0: "?G0 \<turnstile> ?P0 : Prop" using rcH5_ty[of ?G0] tF0 by blast
  have tP1: "?G1 \<turnstile> ?P1 : Prop" using rcH5_ty[of ?G1] tF1 by blast
  have sh0: "shift ?P0 = ?P1" by (simp add: rc_sft k_fun_shift)
  have sh1: "shift ?P1 = Conj rcH5 (pp_fun Prop (Var 2))" by (simp add: rc_sft k_fun_shift numeral_2_eq_2)
  have e1: "shift (Var 0) = Var 1" and e2: "shift (Var 1) = Var 2" by (simp_all add: shift_def)
  note st = u_fun_step[OF r2 y2 Y2]
  have tYy: "?G2 \<turnstile> App (Var 0) (Var 1) : Prop" and tYr: "?G2 \<turnstile> App (Var 0) (Var 2) : Prop" by (rule has_type.App[OF Y2 y2], rule has_type.App[OF Y2 r2])
  have s: "?G2 \<turnstile>\<^sub>U Imp (shift ?P1) (Imp (App rc_p (Var 0)) (Imp (App (Var 0) (shift (Var 0))) (Neg (\<box>\<^sub>o (Neg (App (Var 0) (shift (Var 1))))))))" unfolding sh1 e1 e2
    by (rule u_rc_pc1[OF st]) (insert rcH5_ty[of ?G2] tF2 rc_pure_ty[OF Y2] tYy typed_ObjBox[OF has_type.Neg[OF tYr]], (unfold prop_eval.simps)?, blast+)
  have ri: "?G1 \<turnstile>\<^sub>U Imp ?P1 (rcR (Var 1) (Var 0))" by (rule u_rcR_intro[OF r1 y1 tP1 s])
  have ty: "?G1 \<turnstile> rcR (Var 1) (Var 0) : Prop" by (rule rcR_ty[OF r1 y1])
  have g: "?G0 \<turnstile>\<^sub>U Imp ?P0 (Forall Prop (rcR (Var 1) (Var 0)))" by (rule U_proves.Gen[OF tP0 ty]) (unfold sh0, rule ri)
  have e: "rcUni (Var 0) = Forall Prop (rcR (Var 1) (Var 0))" by (simp add: rcUni_def shift_def)
  have tU: "?G0 \<turnstile> rcUni (Var 0) : Prop" by (rule rcUni_ty[OF r0])
  show ?thesis by (rule u_rc_pc1[OF g[folded e]]) (insert rcH5_ty[of ?G0] tF0 tU, (unfold prop_eval.simps)?, blast+) qed

lemma k_ExUni_shift: "shift rcExUni = rcExUni" by (simp add: rcExUni_def rcUni_def rcR_def shift_def rc_rename_R)

lemma k_ExUni_ty: "\<Gamma> \<turnstile> rcExUni : Prop" proof -
  have "[] \<turnstile> rcExUni : Prop" unfolding rcExUni_def by (rule has_type.Exists, rule rcUni_ty) simp
  then show ?thesis using k_ExUni_shift by (induction \<Gamma>) (simp_all add: rcUni_def, metis weaken_shift_type_ok) qed

lemma u_EG: "[Prop] \<turnstile>\<^sub>U Imp (rcUni (Var 0)) rcExUni" proof -
  have A: "[Prop, Prop] \<turnstile> rcUni (Var 0) : Prop" by (rule rcUni_ty) simp
  have T: "[Prop] \<turnstile> Var 0 : Prop" by simp
  have e: "subst0 (Var 0) (rcUni (Var 0)) = rcUni (Var 0)" by (simp add: rcUni_def rcR_def subst0_def shift_def)
  have "[Prop] \<turnstile>\<^sub>U Imp (subst0 (Var 0) (rcUni (Var 0))) (Exists Prop (rcUni (Var 0)))" using A T by (intro U_proves.H H_proves.EG)
  then show ?thesis unfolding e rcExUni_def . qed

theorem u_fun_ExUni: "[] \<turnstile>\<^sub>U Imp k_EF (Imp rcH5 rcExUni)" proof -
  let ?Q = "Imp rcH5 rcExUni"
  have tP: "[Prop] \<turnstile> pp_fun Prop (Var 0) : Prop" by (rule typed_pp_fun) simp
  have tQ: "\<Gamma> \<turnstile> ?Q : Prop" for \<Gamma> using rcH5_ty[of \<Gamma>] k_ExUni_ty[of \<Gamma>] by blast
  have shq: "shift ?Q = ?Q" by (simp add: shift_def k_ExUni_shift[unfolded shift_def] rcH5_shift[unfolded shift_def])
  have tU: "[Prop] \<turnstile> rcUni (Var 0) : Prop" by (rule rcUni_ty) simp
  have i: "[Prop] \<turnstile>\<^sub>U Imp (pp_fun Prop (Var 0)) (shift ?Q)" unfolding shq by (rule u_rc_pc2[OF u_uni_ctx u_EG]) (insert tP tQ[of "[Prop]"] rcH5_ty[of "[Prop]"] k_ExUni_ty[of "[Prop]"] tU, (unfold prop_eval.simps)?, blast+)
  show ?thesis unfolding k_EF_def by (rule U_proves.Inst[OF tP tQ i]) qed

definition rcT3 :: oterm where "rcT3 = Conj (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_P) (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_Pp) (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) rc_W) (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o rc_u) k_C)
  (Conj (pp_application_closure rc_c rc_u) (Conj (pp_application_closure rc_c (rc_u \<rightarrow>\<^sub>o rc_u)) (Conj (pp_application_closure rc_u Prop) (Conj (pp_application_closure rc_u rc_u)
  (Conj pp_zeroary_exhaustion (Conj pp_unary_recombination (Conj k_EF (pp_pure rc_c rc_p)))))))))))"

theorem u_T3: "[] \<turnstile>\<^sub>U Imp rcT3 ObjFalse" proof -
  note f = u_fun_ExUni and s = u_S and z1 = u_zI[OF rc_pure_ty[OF rcP_ty], of "[]"] and z2 = u_zI[OF rc_pure_ty[OF rcPp_ty], of "[]"]
  have tE: "[] \<turnstile> k_EF : Prop" unfolding k_EF_def by (rule has_type.Exists, rule typed_pp_fun) simp
  have tS: "[] \<turnstile> rcT3 : Prop" unfolding rcT3_def using typed_pp_pure[OF rc_P_ty, of "[]"] typed_pp_pure[OF rc_Pp_ty, of "[]"] typed_pp_pure[OF rc_W_ty, of "[]"] typed_pp_pure[OF k_C_ty, of "[]"] typed_pp_application_closure[of rc_c rc_u] typed_pp_application_closure[of rc_c "rc_u \<rightarrow>\<^sub>o rc_u"] typed_pp_application_closure[of rc_u Prop] typed_pp_application_closure[of rc_u rc_u] typed_pp_zeroary_exhaustion typed_pp_unary_recombination tE typed_pp_pure[OF rc_p_ty, of "[]"] by blast
  have tG: "[] \<turnstile> Imp rcT3 ObjFalse : Prop" using tS typed_ObjFalse[of "[]"] by blast
  show ?thesis by (rule u_rc_pc5[OF f s z1 z2 U_true tG]) (unfold rcT3_def rcS_def rcHU_def rcH5_def zI_def ObjFalse_def pp_pure_def prop_eval.simps, blast)
qed

section \<open>7. T3 in CEV, and its conjuncts\<close>

text \<open>By Loupe, with Jacob: a check of u_T3. Its CEV form; each conjunct past EF a member of the package; EF from UF in U; oracles; closure.\<close>

lemma lo_T3_CEV: "[] \<turnstile>\<^sub>CEV Imp rcT3 ObjFalse" by (rule U_sub_CEV[OF u_T3])

lemma lo_EF_of_UF: "[] \<turnstile>\<^sub>U Imp (pp_unique_fundamental Prop) k_EF" proof -
  let ?K = "Forall Prop (Imp (pp_fun Prop (Var 0)) (Eq Prop (Var 0) (Var 1)))" let ?P = "Conj (pp_fun Prop (Var 0)) ?K"
  have uf: "pp_unique_fundamental Prop = Exists Prop ?P" by (simp add: pp_unique_fundamental_def)
  have tU: "[] \<turnstile> pp_unique_fundamental Prop : Prop" by (rule typed_pp_unique_fundamental)
  have tP: "[Prop] \<turnstile> ?P : Prop" using tU unfolding uf by (auto elim: has_type.cases)
  have tF: "[Prop] \<turnstile> pp_fun Prop (Var 0) : Prop" by (rule typed_pp_fun) simp
  have tE: "[] \<turnstile> k_EF : Prop" unfolding k_EF_def by (rule has_type.Exists[OF tF])
  have tA: "[Prop, Prop] \<turnstile> pp_fun Prop (Var 0) : Prop" by (rule typed_pp_fun) simp
  have e: "subst0 (Var 0) (pp_fun Prop (Var 0)) = pp_fun Prop (Var 0)" by (simp add: pp_fun_def pp_Fun_def subst0_def)
  have g: "[Prop] \<turnstile>\<^sub>U Imp (pp_fun Prop (Var 0)) k_EF" unfolding k_EF_def using U_proves.H[OF H_proves.EG[OF tA, of "Var 0"]] unfolding e by simp
  have s: "shift k_EF = k_EF" by (simp add: k_EF_def pp_fun_def pp_Fun_def shift_def)
  have i: "[Prop] \<turnstile>\<^sub>U Imp ?P (shift k_EF)" unfolding s by (rule u_rc_pc1[OF g]) (insert tP tF weaken_shift_type_ok[OF tE], (unfold s prop_eval.simps)?, blast+)
  show ?thesis unfolding uf by (rule U_proves.Inst[OF tP tE i])
qed

section \<open>8. The paper theory C_FP and its proof\<close>

text \<open>By Dowel, with Jacob, 2026-11-07; not Branden Fitelson's. The paper theory C_FP (the main note's section 2) as
  a set of closed formulas, with Rec and Exhaustion at every n and every list of types, and the proof in it. The
  base's convention: X x1 ... xn is app_vec X (fresh_vars n), in context \<sigma>s @ \<Gamma>, so x1 is Var 0.\<close>

subsection \<open>8.1 Statement 1: the set\<close>

fun cfp_all :: "otype list \<Rightarrow> oterm \<Rightarrow> oterm" where
  "cfp_all [] A = A" | "cfp_all (\<sigma> # \<sigma>s) A = cfp_all \<sigma>s (Forall \<sigma> A)"

fun cfp_and :: "oterm list \<Rightarrow> oterm" where
  "cfp_and [] = ObjTrue" | "cfp_and [A] = A" | "cfp_and (A # B # As) = Conj A (cfp_and (B # As))"

definition cfp_Fun :: "otype list \<Rightarrow> oterm list" where
  "cfp_Fun \<sigma>s = [pp_fun (\<sigma>s ! i) (Var i). i \<leftarrow> [0..<length \<sigma>s]] @
    [Neg (Eq (\<sigma>s ! i) (Var i) (Var j)). i \<leftarrow> [0..<length \<sigma>s], j \<leftarrow> [0..<length \<sigma>s], i < j \<and> \<sigma>s ! i = \<sigma>s ! j]"

definition cfp_Pre :: "otype list \<Rightarrow> oterm" where
  "cfp_Pre \<sigma>s = cfp_and (pp_pure (arrow_type \<sigma>s Prop) (Var (length \<sigma>s)) # cfp_Fun \<sigma>s)"

definition cfp_Xz :: "otype list \<Rightarrow> oterm" where
  "cfp_Xz \<sigma>s = app_vec (Var (length \<sigma>s)) (fresh_vars (length \<sigma>s))"

definition cfp_Xx :: "otype list \<Rightarrow> oterm" where
  "cfp_Xx \<sigma>s = cfp_all \<sigma>s (app_vec (Var (length \<sigma>s + length \<sigma>s)) (fresh_vars (length \<sigma>s)))"

definition cfp_Rec :: "otype list \<Rightarrow> oterm" where
  "cfp_Rec \<sigma>s = Forall (arrow_type \<sigma>s Prop) (cfp_all \<sigma>s (Imp (cfp_Pre \<sigma>s) (Imp (\<box>\<^sub>o (cfp_Xz \<sigma>s)) (cfp_Xx \<sigma>s))))"

definition cfp_Exh :: "otype list \<Rightarrow> oterm" where
  "cfp_Exh \<sigma>s = Forall (arrow_type \<sigma>s Prop) (cfp_all \<sigma>s (Imp (cfp_Pre \<sigma>s) (Imp (cfp_Xx \<sigma>s) (\<box>\<^sub>o (cfp_Xz \<sigma>s)))))"

definition pp_CFP_axioms :: "oterm set" where
  "pp_CFP_axioms = pp_purity_schema \<union> pp_application_closure_schema \<union> {k_EF} \<union> range cfp_Rec \<union> range cfp_Exh"

lemma cfp_lit: "cfp_Rec [] = pp_zeroary_recombination" "cfp_Exh [] = pp_zeroary_exhaustion"
    "cfp_Rec [Prop] = pp_unary_recombination" "cfp_Exh [Prop] = pp_unary_exhaustion"
  by (simp_all add: cfp_Rec_def cfp_Exh_def cfp_Pre_def cfp_Fun_def cfp_Xz_def cfp_Xx_def fresh_vars_def
    pp_zeroary_recombination_def pp_zeroary_exhaustion_def pp_unary_recombination_def pp_unary_exhaustion_def)

lemma cfp_all_ty: "\<sigma>s @ \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> cfp_all \<sigma>s A : Prop" by (induction \<sigma>s arbitrary: A) auto

lemma cfp_and_ty: "(\<And>A. A \<in> set L \<Longrightarrow> \<Gamma> \<turnstile> A : Prop) \<Longrightarrow> \<Gamma> \<turnstile> cfp_and L : Prop" by (induction L rule: cfp_and.induct) (auto intro: typed_ObjTrue)

lemma cfp_and_mem: "A \<in> set L \<Longrightarrow> prop_eval v (cfp_and L) \<Longrightarrow> prop_eval v A" by (induction L rule: cfp_and.induct) auto

lemma cfp_Fun_set: "set (cfp_Fun \<sigma>s) = {pp_fun (\<sigma>s ! i) (Var i) | i. i < length \<sigma>s} \<union> {Neg (Eq (\<sigma>s ! i) (Var i) (Var j)) | i j. i < j \<and> j < length \<sigma>s \<and> \<sigma>s ! i = \<sigma>s ! j}"
  by (auto simp: cfp_Fun_def)

lemma cfp_var: "i < length \<sigma>s \<Longrightarrow> \<sigma>s @ \<Gamma> \<turnstile> Var i : \<sigma>s ! i" by (auto simp: lookup_def nth_append)

lemma cfp_Fun_ty: "A \<in> set (cfp_Fun \<sigma>s) \<Longrightarrow> \<sigma>s @ \<Gamma> \<turnstile> A : Prop" unfolding cfp_Fun_set
  by (auto intro!: typed_pp_fun cfp_var) (metis cfp_var has_type.Eq has_type.Neg order.strict_trans)

lemma cfp_Xv: assumes "\<Delta> \<turnstile> Var k : arrow_type \<sigma>s Prop" shows "\<sigma>s @ \<Delta> \<turnstile> app_vec (Var (length \<sigma>s + k)) (fresh_vars (length \<sigma>s)) : Prop"
  using typed_app_fresh_vars[OF assms] by (simp add: shift_by_def shift_ren_def add.commute)

lemma cfp_top: "[arrow_type \<sigma>s Prop] \<turnstile> Var 0 : arrow_type \<sigma>s Prop" by (simp add: lookup_def)

lemma cfp_Pre_ty: "\<sigma>s @ [arrow_type \<sigma>s Prop] \<turnstile> cfp_Pre \<sigma>s : Prop" unfolding cfp_Pre_def
  by (rule cfp_and_ty) (auto intro: cfp_Fun_ty typed_pp_pure simp: lookup_def nth_append)

lemma cfp_Xz_ty: "\<sigma>s @ [arrow_type \<sigma>s Prop] \<turnstile> cfp_Xz \<sigma>s : Prop" unfolding cfp_Xz_def using cfp_Xv[OF cfp_top] by simp

lemma cfp_Xx_ty: "\<sigma>s @ [arrow_type \<sigma>s Prop] \<turnstile> cfp_Xx \<sigma>s : Prop" proof -
  have v: "\<sigma>s @ [arrow_type \<sigma>s Prop] \<turnstile> Var (length \<sigma>s) : arrow_type \<sigma>s Prop" by (simp add: lookup_def nth_append)
  show ?thesis unfolding cfp_Xx_def using cfp_all_ty[OF cfp_Xv[OF v]] by simp qed

lemma cfp_Rec_ty: "[] \<turnstile> cfp_Rec \<sigma>s : Prop" unfolding cfp_Rec_def using cfp_Pre_ty[of \<sigma>s] cfp_Xz_ty[of \<sigma>s] cfp_Xx_ty[of \<sigma>s]
  by (intro has_type.Forall cfp_all_ty) (auto intro: typed_ObjBox)

lemma cfp_Exh_ty: "[] \<turnstile> cfp_Exh \<sigma>s : Prop" unfolding cfp_Exh_def using cfp_Pre_ty[of \<sigma>s] cfp_Xz_ty[of \<sigma>s] cfp_Xx_ty[of \<sigma>s]
  by (intro has_type.Forall cfp_all_ty) (auto intro: typed_ObjBox)

lemma cfp_EF_ty: "[] \<turnstile> k_EF : Prop" unfolding k_EF_def by (rule has_type.Exists, rule typed_pp_fun) simp

theorem pp_CFP_closed: "A \<in> pp_CFP_axioms \<Longrightarrow> [] \<turnstile> A : Prop" unfolding pp_CFP_axioms_def
  using pp_purity_schema_typed pp_application_closure_schema_typed cfp_EF_ty cfp_Rec_ty cfp_Exh_ty by blast

subsection \<open>8.2 Statement 2: the proof in C_FP, with the n-ary forms used at n = 0 and n = 1 alone\<close>

definition cfp_S2 :: "oterm list" where "cfp_S2 = [pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_P, pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_Pp, pp_pure (rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) rc_W,
  pp_pure (rc_u \<rightarrow>\<^sub>o rc_u) k_C, pp_application_closure rc_c rc_u, pp_application_closure rc_c (rc_u \<rightarrow>\<^sub>o rc_u), pp_application_closure rc_u Prop,
  pp_application_closure rc_u rc_u, cfp_Exh [], cfp_Rec [Prop], k_EF]"

lemma cfp_LP: "[] \<turnstile> M : \<sigma> \<Longrightarrow> consts_of M = {} \<Longrightarrow> pp_pure \<sigma> M \<in> pp_CFP_axioms"
  unfolding pp_CFP_axioms_def pp_purity_schema_def pp_logical_vocabulary_def by blast

lemma cfp_AC: "pp_application_closure \<sigma> \<tau> \<in> pp_CFP_axioms" unfolding pp_CFP_axioms_def pp_application_closure_schema_def by blast

lemma cfp_mem: "cfp_Rec \<sigma>s \<in> pp_CFP_axioms" "cfp_Exh \<sigma>s \<in> pp_CFP_axioms" "k_EF \<in> pp_CFP_axioms" unfolding pp_CFP_axioms_def by blast+

lemma cfp_S2_sub: "set cfp_S2 \<subseteq> pp_CFP_axioms" unfolding cfp_S2_def
  using cfp_LP[OF rc_P_ty rc_consts(4)] cfp_LP[OF rc_Pp_ty rc_consts(5)] cfp_LP[OF rc_W_ty rc_W_consts] cfp_LP[OF k_C_ty k_C_consts] cfp_AC cfp_mem by simp

lemma cfp_and_local: "(\<And>A. A \<in> set L \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A) \<Longrightarrow> \<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s cfp_and L" proof (induction L rule: cfp_and.induct)
  case 1 show ?case using CEV_set_derivable.Theorem[OF CEV_proves_ObjTrue] by simp
next
  case (2 A) then show ?case by simp
next
  case (3 A B As)
  have a: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s A" and b: "\<Gamma> ; T \<turnstile>\<^sub>CEV\<^sub>s cfp_and (B # As)" using 3 by auto
  have ta: "\<Gamma> \<turnstile> A : Prop" and tb: "\<Gamma> \<turnstile> cfp_and (B # As) : Prop" using CEV_set_derivable_formula[OF a] CEV_set_derivable_formula[OF b] by blast+
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp A (Imp (cfp_and (B # As)) (Conj A (cfp_and (B # As))))" by (rule CEV_prop_tautology) (use ta tb in \<open>auto simp: prop_tautology_def\<close>)
  then show ?case using CEV_set_derivable.Derive_MP[OF b CEV_set_derivable.Derive_MP[OF a CEV_set_derivable.Theorem]] by simp
qed

theorem cfp2_thm: "[] \<turnstile>\<^sub>CEV Imp (cfp_and cfp_S2) (Neg pp_target_PP)" proof -
  have t: "[] \<turnstile> Imp (cfp_and cfp_S2) (Neg pp_target_PP) : Prop"
    by (rule has_type.Imp[OF cfp_and_ty has_type.Neg[OF typed_pp_target_PP]]) (use cfp_S2_sub pp_CFP_closed in blast)
  show ?thesis by (rule rc_pc2[OF lo_T3_CEV CEV_proves_ObjTrue t]) (simp only: cfp_S2_def cfp_lit cfp_and.simps rcT3_def ObjFalse_def pp_target_PP_def pp_purity_of_pure_def pp_pure_def prop_eval.simps, blast)
qed

theorem cfp2: "[] ; pp_CFP_axioms \<turnstile>\<^sub>CEV\<^sub>s Neg pp_target_PP" proof -
  have "[] ; pp_CFP_axioms \<turnstile>\<^sub>CEV\<^sub>s cfp_and cfp_S2" by (rule cfp_and_local) (use cfp_S2_sub pp_CFP_closed in blast)
  then show ?thesis by (rule CEV_set_derivable.Derive_MP[OF _ CEV_set_derivable.Theorem[OF cfp2_thm]])
qed

subsection \<open>8.3 Statement 3: the step to B_Q\<close>

lemma cfp_gen: assumes H: "\<And>\<Delta>. \<Delta> \<turnstile> H : Prop" and s: "shift H = H" shows "\<sigma>s @ \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV Imp H A \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV Imp H (cfp_all \<sigma>s A)"
proof (induction \<sigma>s arbitrary: A)
  case Nil then show ?case by simp
next
  case (Cons \<sigma> \<sigma>s)
  have "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV Imp H (Forall \<sigma> A)" by (rule CEV_proves.Gen[OF H]) (use Cons.prems s in simp_all)
  then show ?case using Cons.IH[of "Forall \<sigma> A"] Cons.prems(1) by auto
qed

lemma cfp_vac: assumes H: "\<And>\<Delta>. \<Delta> \<turnstile> H : Prop" and s: "shift H = H" and C: "\<sigma>s @ [arrow_type \<sigma>s Prop] \<turnstile> C : Prop"
    and n: "\<sigma>s @ [arrow_type \<sigma>s Prop] \<turnstile>\<^sub>CEV Imp H (Neg (cfp_Pre \<sigma>s))"
  shows "[] \<turnstile>\<^sub>CEV Imp H (Forall (arrow_type \<sigma>s Prop) (cfp_all \<sigma>s (Imp (cfp_Pre \<sigma>s) C)))" proof -
  let ?G = "\<sigma>s @ [arrow_type \<sigma>s Prop]"
  have t: "?G \<turnstile> Imp (cfp_Pre \<sigma>s) C : Prop" using cfp_Pre_ty[of \<sigma>s] C by blast
  have i: "?G \<turnstile>\<^sub>CEV Imp H (Imp (cfp_Pre \<sigma>s) C)" by (rule rc_pc1[OF n has_type.Imp[OF H t]]) (unfold prop_eval.simps, blast)
  show ?thesis by (rule CEV_proves.Gen[OF H cfp_all_ty[OF t]]) (use cfp_gen[OF H s t i] s in simp)
qed

lemma cfp_uf: assumes a: "\<Gamma> \<turnstile> a : Prop" and b: "\<Gamma> \<turnstile> b : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (pp_unique_fundamental Prop) (Imp (pp_fun Prop a) (Imp (pp_fun Prop b) (Eq Prop a b)))" proof -
  let ?B = "Imp (pp_fun Prop (Var 0)) (Eq Prop (Var 0) (Var 1))" let ?K = "Forall Prop ?B" let ?P = "Conj (pp_fun Prop (Var 0)) ?K"
  let ?Q = "Imp (pp_fun Prop a) (Imp (pp_fun Prop b) (Eq Prop a b))" let ?G = "Prop # \<Gamma>"
  have uf: "pp_unique_fundamental Prop = Exists Prop ?P" by (simp add: pp_unique_fundamental_def)
  have tP: "?G \<turnstile> ?P : Prop" using typed_pp_unique_fundamental[of Prop] typed_pp_fun[of "[Prop]" "Var 0" Prop] by (rule_tac infer_type_sound) (simp add: pp_fun_def pp_Fun_def lookup_def)
  have tB: "Prop # ?G \<turnstile> ?B : Prop" using tP by (auto elim: has_type.cases)
  have tQ: "\<Gamma> \<turnstile> ?Q : Prop" using typed_pp_fun[OF a] typed_pp_fun[OF b] a b by auto
  have sa: "?G \<turnstile> shift a : Prop" and sb: "?G \<turnstile> shift b : Prop" and r: "?G \<turnstile> Var 0 : Prop" by (rule weaken_shift_type_ok[OF a], rule weaken_shift_type_ok[OF b]) simp
  have e: "subst0 c ?B = Imp (pp_fun Prop c) (Eq Prop c (Var 0))" for c by (simp add: subst0_def pp_fun_def pp_Fun_def)
  have ui: "?G \<turnstile>\<^sub>CEV Imp ?K (Imp (pp_fun Prop c) (Eq Prop c (Var 0)))" if "?G \<turnstile> c : Prop" for c
    unfolding e[symmetric] using tB that by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)
  note u1 = ui[OF sa] and u2 = ui[OF sb] and tr = CEV_eq_trans[OF sa r sb] and sy = CEV_eq_sym[OF sb r]
  have sq: "shift ?Q = Imp (pp_fun Prop (shift a)) (Imp (pp_fun Prop (shift b)) (Eq Prop (shift a) (shift b)))" by (simp add: shift_def pp_fun_def pp_Fun_def)
  have g: "?G \<turnstile>\<^sub>CEV Imp ?P (shift ?Q)" by (rule rc_pc4[OF u1 u2 tr sy has_type.Imp[OF tP weaken_shift_type_ok[OF tQ]]]) (unfold sq prop_eval.simps, blast)
  show ?thesis unfolding uf by (rule CEV_proves.Inst[OF tP tQ g])
qed

lemma cfp_mem_Pre: "A \<in> set (cfp_Fun \<sigma>s) \<Longrightarrow> prop_eval v (cfp_Pre \<sigma>s) \<Longrightarrow> prop_eval v A"
  unfolding cfp_Pre_def by (rule cfp_and_mem) simp_all

lemma cfp_no: assumes i: "i < length \<sigma>s" shows "\<sigma>s @ \<Gamma> \<turnstile>\<^sub>CEV Imp (pp_no_fundamentals (\<sigma>s ! i)) (Neg (pp_fun (\<sigma>s ! i) (Var i)))" proof -
  let ?B = "Neg (pp_fun (\<sigma>s ! i) (Var 0))"
  have d: "pp_no_fundamentals (\<sigma>s ! i) = Forall (\<sigma>s ! i) ?B" by (simp add: pp_no_fundamentals_def)
  have e: "subst0 (Var i) ?B = Neg (pp_fun (\<sigma>s ! i) (Var i))" by (simp add: subst0_def pp_fun_def pp_Fun_def)
  have t: "(\<sigma>s ! i) # \<sigma>s @ \<Gamma> \<turnstile> ?B : Prop" by (intro has_type.Neg typed_pp_fun) simp
  show ?thesis unfolding d e[symmetric] using t cfp_var[OF i] by (intro CEV_proves.CE CE_proves.C C_proves.H H_proves.UI)
qed

lemma cfp_noH: "\<Delta> \<turnstile> pp_no_fundamentals \<tau> : Prop" "shift (pp_no_fundamentals \<tau>) = pp_no_fundamentals \<tau>"
  by (rule infer_type_sound, simp add: pp_no_fundamentals_def pp_fun_def pp_Fun_def lookup_def) (simp add: pp_no_fundamentals_def pp_fun_def pp_Fun_def shift_def)

lemma cfp_ufH: "\<Delta> \<turnstile> pp_unique_fundamental \<tau> : Prop" "shift (pp_unique_fundamental \<tau>) = pp_unique_fundamental \<tau>"
  by (rule infer_type_sound, simp add: pp_unique_fundamental_def pp_fun_def pp_Fun_def lookup_def) (simp add: pp_unique_fundamental_def pp_fun_def pp_Fun_def shift_def)

lemma cfp_Bm: "pp_zeroary_recombination \<in> pp_full_QLN_background_axioms" "pp_unary_recombination \<in> pp_full_QLN_background_axioms"
    "pp_zeroary_exhaustion \<in> pp_full_QLN_background_axioms" "pp_unary_exhaustion \<in> pp_full_QLN_background_axioms"
    "pp_unique_fundamental Prop \<in> pp_full_QLN_background_axioms" "\<tau> \<noteq> Prop \<Longrightarrow> pp_no_fundamentals \<tau> \<in> pp_full_QLN_background_axioms"
    "pp_purity_schema \<subseteq> pp_full_QLN_background_axioms" "pp_application_closure_schema \<subseteq> pp_full_QLN_background_axioms"
  unfolding pp_full_QLN_background_axioms_exact_scope pp_background_axioms_def pp_no_other_fundamentals_schema_def by blast+

lemma cfp_vac_H: assumes "\<sigma>s \<noteq> []" "\<sigma>s \<noteq> [Prop]"
  shows "\<exists>H. (\<forall>\<Delta>. \<Delta> \<turnstile> H : Prop) \<and> shift H = H \<and> H \<in> pp_full_QLN_background_axioms \<and> \<sigma>s @ [arrow_type \<sigma>s Prop] \<turnstile>\<^sub>CEV Imp H (Neg (cfp_Pre \<sigma>s))"
proof (cases "\<exists>i<length \<sigma>s. \<sigma>s ! i \<noteq> Prop")
  case True
  then obtain i where i: "i < length \<sigma>s" and ne: "\<sigma>s ! i \<noteq> Prop" by blast
  have m: "pp_fun (\<sigma>s ! i) (Var i) \<in> set (cfp_Fun \<sigma>s)" using i unfolding cfp_Fun_set by blast
  have n: "\<sigma>s @ [arrow_type \<sigma>s Prop] \<turnstile>\<^sub>CEV Imp (pp_no_fundamentals (\<sigma>s ! i)) (Neg (cfp_Pre \<sigma>s))"
    by (rule rc_pc1[OF cfp_no[OF i] has_type.Imp[OF cfp_noH(1) has_type.Neg[OF cfp_Pre_ty]]]) (use cfp_mem_Pre[OF m] in \<open>unfold prop_eval.simps, blast\<close>)
  show ?thesis using n cfp_noH cfp_Bm(6)[OF ne] by blast
next
  case False
  then have all: "\<And>i. i < length \<sigma>s \<Longrightarrow> \<sigma>s ! i = Prop" by blast
  have l: "2 \<le> length \<sigma>s" using assms all[of 0] by (cases \<sigma>s, simp, rename_tac ts, case_tac ts, auto)
  have ne: "0 < length \<sigma>s" "1 < length \<sigma>s" using l by linarith+
  have p0: "\<sigma>s ! 0 = Prop" and p1: "\<sigma>s ! 1 = Prop" by (rule all[OF ne(1)], rule all[OF ne(2)])
  have M: "pp_fun (\<sigma>s ! i) (Var i) \<in> set (cfp_Fun \<sigma>s)" if "i < length \<sigma>s" for i using that unfolding cfp_Fun_set by blast
  have D: "Neg (Eq (\<sigma>s ! 0) (Var 0) (Var 1)) \<in> set (cfp_Fun \<sigma>s)" unfolding cfp_Fun_set
    by (rule UnI2, rule CollectI, rule exI[of _ 0], rule exI[of _ 1]) (use ne(2) p0 p1 in simp)
  note m0 = M[OF ne(1), unfolded p0] and m1 = M[OF ne(2), unfolded p1] and md = D[unfolded p0]
  let ?G = "\<sigma>s @ [arrow_type \<sigma>s Prop]"
  note v0 = cfp_var[OF ne(1), of "[arrow_type \<sigma>s Prop]", unfolded p0] and v1 = cfp_var[OF ne(2), of "[arrow_type \<sigma>s Prop]", unfolded p1]
  have n: "?G \<turnstile>\<^sub>CEV Imp (pp_unique_fundamental Prop) (Neg (cfp_Pre \<sigma>s))"
    by (rule rc_pc1[OF cfp_uf[OF v0 v1] has_type.Imp[OF cfp_ufH(1) has_type.Neg[OF cfp_Pre_ty]]]) (use cfp_mem_Pre[OF m0] cfp_mem_Pre[OF m1] cfp_mem_Pre[OF md] in \<open>unfold prop_eval.simps, blast\<close>)
  show ?thesis using n cfp_ufH cfp_Bm(5) by blast
qed

lemma cfp_vac_local: assumes "\<sigma>s \<noteq> []" "\<sigma>s \<noteq> [Prop]" and C: "\<sigma>s @ [arrow_type \<sigma>s Prop] \<turnstile> C : Prop"
  shows "[] ; pp_full_QLN_background_axioms \<turnstile>\<^sub>CEV\<^sub>s Forall (arrow_type \<sigma>s Prop) (cfp_all \<sigma>s (Imp (cfp_Pre \<sigma>s) C))" proof -
  obtain H where H: "\<And>\<Delta>. \<Delta> \<turnstile> H : Prop" and s: "shift H = H" and m: "H \<in> pp_full_QLN_background_axioms" and n: "\<sigma>s @ [arrow_type \<sigma>s Prop] \<turnstile>\<^sub>CEV Imp H (Neg (cfp_Pre \<sigma>s))"
    using cfp_vac_H[OF assms(1,2)] by blast
  show ?thesis by (rule CEV_set_derivable.Derive_MP[OF CEV_set_derivable.Assumption[OF m H] CEV_set_derivable.Theorem[OF cfp_vac[OF H s C n]]])
qed

theorem cfp3: assumes A: "A \<in> pp_CFP_axioms" shows "[] ; pp_full_QLN_background_axioms \<turnstile>\<^sub>CEV\<^sub>s A" proof -
  let ?B = "pp_full_QLN_background_axioms"
  have ass: "[] ; ?B \<turnstile>\<^sub>CEV\<^sub>s D" if "D \<in> ?B" for D by (rule CEV_set_derivable.Assumption[OF that]) (use that pp_full_QLN_PP_axioms_typed in \<open>auto simp: pp_full_QLN_PP_axioms_def\<close>)
  note t = cfp_Xz_ty cfp_Xx_ty
  have N: "[] ; ?B \<turnstile>\<^sub>CEV\<^sub>s cfp_Rec \<sigma>s" "[] ; ?B \<turnstile>\<^sub>CEV\<^sub>s cfp_Exh \<sigma>s" if "\<sigma>s \<noteq> []" "\<sigma>s \<noteq> [Prop]" for \<sigma>s
    unfolding cfp_Rec_def cfp_Exh_def using that t[of \<sigma>s] by (auto intro!: cfp_vac_local typed_ObjBox)
  have R: "[] ; ?B \<turnstile>\<^sub>CEV\<^sub>s cfp_Rec \<sigma>s" for \<sigma>s using ass[OF cfp_Bm(1)] ass[OF cfp_Bm(2)] N(1)[of \<sigma>s] by (cases "\<sigma>s = [] \<or> \<sigma>s = [Prop]") (auto simp: cfp_lit)
  have E: "[] ; ?B \<turnstile>\<^sub>CEV\<^sub>s cfp_Exh \<sigma>s" for \<sigma>s using ass[OF cfp_Bm(3)] ass[OF cfp_Bm(4)] N(2)[of \<sigma>s] by (cases "\<sigma>s = [] \<or> \<sigma>s = [Prop]") (auto simp: cfp_lit)
  have F: "[] ; ?B \<turnstile>\<^sub>CEV\<^sub>s k_EF" by (rule CEV_set_derivable.Derive_MP[OF ass[OF cfp_Bm(5)] CEV_set_derivable.Theorem[OF U_sub_CEV[OF lo_EF_of_UF]]])
  show ?thesis using A ass cfp_Bm(7,8) R E F unfolding pp_CFP_axioms_def by blast
qed

subsection \<open>8.4 Statement 5: the footnote, by Rec at n = 2; and a control, Fun(z) with its distinctness clause dropped\<close>

abbreviation "cfp_c2 \<equiv> Prop \<rightarrow>\<^sub>o (Prop \<rightarrow>\<^sub>o Prop)"

definition cfp_B2 :: "bool \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm" where
  "cfp_B2 d X a b = Imp (cfp_and ([pp_pure cfp_c2 X, pp_fun Prop a, pp_fun Prop b] @ (if d then [Neg (Eq Prop a b)] else [])))
    (Imp (\<box>\<^sub>o (App (App X a) b)) (Forall Prop (Forall Prop (App (App (shift (shift X)) (Var 0)) (Var 1)))))"

definition cfp_R2 :: "bool \<Rightarrow> oterm" where "cfp_R2 d = Forall cfp_c2 (Forall Prop (Forall Prop (cfp_B2 d (Var 2) (Var 0) (Var 1))))"

lemma cfp_R2_ty: "\<Gamma> \<turnstile> cfp_R2 d : Prop" "shift (cfp_R2 d) = cfp_R2 d" unfolding cfp_R2_def
  by (cases d; rule infer_type_sound; simp add: cfp_B2_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def shift_def eval_nat_numeral)
    (cases d; simp add: cfp_B2_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def shift_def eval_nat_numeral)

lemma cfp_B2_ty: assumes X: "\<Gamma> \<turnstile> X : cfp_c2" and a: "\<Gamma> \<turnstile> a : Prop" and b: "\<Gamma> \<turnstile> b : Prop" shows "\<Gamma> \<turnstile> cfp_B2 d X a b : Prop" proof -
  have s: "Prop # Prop # \<Gamma> \<turnstile> shift (shift X) : cfp_c2" by (rule weaken_shift_type_ok[OF weaken_shift_type_ok[OF X]])
  have v: "Prop # Prop # \<Gamma> \<turnstile> Var 0 : Prop" "Prop # Prop # \<Gamma> \<turnstile> Var 1 : Prop" by (simp_all add: lookup_def)
  have f: "\<Gamma> \<turnstile> Forall Prop (Forall Prop (App (App (shift (shift X)) (Var 0)) (Var 1))) : Prop" using has_type.App[OF has_type.App[OF s v(1)] v(2)] by blast
  have c: "\<Gamma> \<turnstile> cfp_and ([pp_pure cfp_c2 X, pp_fun Prop a, pp_fun Prop b] @ (if d then [Neg (Eq Prop a b)] else [])) : Prop"
    by (rule cfp_and_ty) (use typed_pp_pure[OF X] typed_pp_fun[OF a] typed_pp_fun[OF b] a b in \<open>auto split: if_split_asm\<close>)
  show ?thesis unfolding cfp_B2_def using c f typed_ObjBox[OF has_type.App[OF has_type.App[OF X a] b]] by blast qed

lemma cfp_ui: "\<sigma> # \<Gamma> \<turnstile> A : Prop \<Longrightarrow> \<Gamma> \<turnstile> T : \<sigma> \<Longrightarrow> subst0 T A = B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>CEV Imp (Forall \<sigma> A) B"
  by (intro CEV_proves.CE CE_proves.C C_proves.H) (metis H_proves.UI)

lemma cfp_R2_inst: assumes X: "\<Gamma> \<turnstile> X : cfp_c2" and a: "\<Gamma> \<turnstile> a : Prop" and b: "\<Gamma> \<turnstile> b : Prop" and p: "\<Gamma> \<turnstile> p : Prop" and q: "\<Gamma> \<turnstile> q : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (cfp_R2 d) (Imp (cfp_and ([pp_pure cfp_c2 X, pp_fun Prop a, pp_fun Prop b] @ (if d then [Neg (Eq Prop a b)] else [])))
    (Imp (\<box>\<^sub>o (App (App X a) b)) (App (App X p) q)))" proof -
  let ?G1 = "Prop # \<Gamma>" let ?G2 = "Prop # ?G1" let ?S = "\<lambda>M. shift (shift M)" let ?A = "App (App (?S X) (Var 0)) (Var 1)"
  have sX: "?G1 \<turnstile> shift X : cfp_c2" and sa: "?G1 \<turnstile> shift a : Prop" and sb: "?G1 \<turnstile> shift b : Prop" and sq: "?G1 \<turnstile> shift q : Prop" using X a b q by (auto intro: weaken_shift_type_ok)
  have ssX: "?G2 \<turnstile> ?S X : cfp_c2" by (rule weaken_shift_type_ok[OF sX])
  have v: "?G2 \<turnstile> Var 0 : Prop" "?G2 \<turnstile> Var 1 : Prop" "?G1 \<turnstile> Var 0 : Prop" by (simp_all add: lookup_def)
  have t1: "?G2 \<turnstile> cfp_B2 d (?S X) (Var 0) (Var 1) : Prop" by (rule cfp_B2_ty[OF ssX v(1,2)])
  have t2: "?G1 \<turnstile> cfp_B2 d (shift X) (Var 0) (shift b) : Prop" by (rule cfp_B2_ty[OF sX v(3) sb])
  have t3: "\<Gamma> \<turnstile> cfp_B2 d X a b : Prop" by (rule cfp_B2_ty[OF X a b])
  have e1: "subst0 X (Forall Prop (Forall Prop (cfp_B2 d (Var 2) (Var 0) (Var 1)))) = Forall Prop (Forall Prop (cfp_B2 d (?S X) (Var 0) (Var 1)))"
    by (cases d; simp add: cfp_B2_def subst0_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def eval_nat_numeral shift_def)
  have e2: "subst0 b (Forall Prop (cfp_B2 d (?S X) (Var 0) (Var 1))) = Forall Prop (cfp_B2 d (shift X) (Var 0) (shift b))"
    by (cases d; simp add: cfp_B2_def subst0_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def eval_nat_numeral flip: shift_def)
  have e3: "subst0 a (cfp_B2 d (shift X) (Var 0) (shift b)) = cfp_B2 d X a b"
    by (cases d; simp add: cfp_B2_def subst0_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def eval_nat_numeral flip: shift_def)
  have i1: "\<Gamma> \<turnstile>\<^sub>CEV Imp (cfp_R2 d) (Forall Prop (Forall Prop (cfp_B2 d (?S X) (Var 0) (Var 1))))" unfolding cfp_R2_def
    by (rule cfp_ui[OF _ X e1]) (intro has_type.Forall cfp_B2_ty, simp_all add: lookup_def eval_nat_numeral)
  have i2: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Forall Prop (Forall Prop (cfp_B2 d (?S X) (Var 0) (Var 1)))) (Forall Prop (cfp_B2 d (shift X) (Var 0) (shift b)))" using t1 b e2 by (intro cfp_ui) auto
  have i3: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Forall Prop (cfp_B2 d (shift X) (Var 0) (shift b))) (cfp_B2 d X a b)" by (rule cfp_ui[OF t2 a e3])
  have tA: "?G2 \<turnstile> ?A : Prop" and tA1: "?G1 \<turnstile> App (App (shift X) (Var 0)) (shift q) : Prop" using has_type.App[OF has_type.App[OF ssX v(1)] v(2)] has_type.App[OF has_type.App[OF sX v(3)] sq] by blast+
  have u1: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Forall Prop (Forall Prop ?A)) (Forall Prop (App (App (shift X) (Var 0)) (shift q)))"
    by (rule cfp_ui[OF has_type.Forall[OF tA] q]) (simp add: subst0_def flip: shift_def)
  have u2: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Forall Prop (App (App (shift X) (Var 0)) (shift q))) (App (App X p) q)"
    by (rule cfp_ui[OF tA1 p]) (simp add: subst0_def flip: shift_def)
  have tC: "\<Gamma> \<turnstile> cfp_and ([pp_pure cfp_c2 X, pp_fun Prop a, pp_fun Prop b] @ (if d then [Neg (Eq Prop a b)] else [])) : Prop" and tB: "\<Gamma> \<turnstile> \<box>\<^sub>o (App (App X a) b) : Prop"
    using t3 unfolding cfp_B2_def by (auto elim: has_type.cases)
  show ?thesis by (rule rc_pc5[OF i1 i2 i3 u1 u2]) (use cfp_R2_ty(1)[of \<Gamma> d] tC tB has_type.App[OF has_type.App[OF X p] q] in blast, unfold cfp_B2_def prop_eval.simps, blast)
qed

definition cfp_X :: oterm where "cfp_X = Lam Prop (Lam Prop (Var 0 \<longleftrightarrow>\<^sub>o Neg (Var 1)))"

definition cfp_Xe :: oterm where "cfp_Xe = Lam Prop (Lam Prop (Var 0 \<longleftrightarrow>\<^sub>o Var 1))"

lemma cfp_X_ty: "\<Gamma> \<turnstile> cfp_X : cfp_c2" "\<Gamma> \<turnstile> cfp_Xe : cfp_c2" by (rule infer_type_sound, simp add: cfp_X_def cfp_Xe_def lookup_def)+

lemma cfp_X_closed: "consts_of cfp_X = {}" "consts_of cfp_Xe = {}" "shift (pp_pure cfp_c2 cfp_X) = pp_pure cfp_c2 cfp_X" "shift (pp_pure cfp_c2 cfp_Xe) = pp_pure cfp_c2 cfp_Xe"
  by (simp_all add: cfp_X_def cfp_Xe_def pp_pure_def pp_Pure_def shift_def)

lemma cfp_Xe_iff: assumes a: "\<Gamma> \<turnstile> a : Prop" and b: "\<Gamma> \<turnstile> b : Prop" shows "\<Gamma> \<turnstile>\<^sub>CEV (App (App cfp_Xe a) b \<longleftrightarrow>\<^sub>o (b \<longleftrightarrow>\<^sub>o a))"
  using CEV_beta_eta_equiv[OF rc_be2[OF has_type.App[OF cfp_X_ty(2) a, unfolded cfp_Xe_def] b]] by (simp add: cfp_Xe_def subst0_def flip: shift_def)

theorem cfp_ctl_dist: "[] \<turnstile>\<^sub>CEV Imp k_EF (Neg (Conj (cfp_R2 False) (pp_pure cfp_c2 cfp_Xe)))" proof -
  let ?H = "Conj (cfp_R2 False) (pp_pure cfp_c2 cfp_Xe)" let ?G = "[Prop]" let ?r = "Var 0" let ?T = "ObjTrue" let ?F = "Neg ObjTrue"
  have r: "?G \<turnstile> ?r : Prop" and T: "?G \<turnstile> ?T : Prop" and F: "?G \<turnstile> ?F : Prop" by (auto intro: typed_ObjTrue simp: lookup_def)
  note i = cfp_R2_inst[OF cfp_X_ty(2) r r T F, of False, simplified] and xr = cfp_Xe_iff[OF r r] and xt = cfp_Xe_iff[OF T F]
  have tX: "?G \<turnstile> App (App cfp_Xe ?r) ?r : Prop" and tT: "?G \<turnstile> Neg (App (App cfp_Xe ?T) ?F) : Prop" using has_type.App[OF has_type.App[OF cfp_X_ty(2) r] r] has_type.App[OF has_type.App[OF cfp_X_ty(2) T] F] by blast+
  have n: "?G \<turnstile>\<^sub>CEV \<box>\<^sub>o (App (App cfp_Xe ?r) ?r)" by (rule CEV_necessitation[OF rc_pc1[OF xr tX]]) (unfold prop_eval.simps, blast)
  have f: "?G \<turnstile>\<^sub>CEV Neg (App (App cfp_Xe ?T) ?F)" by (rule rc_pc1[OF xt tT]) (unfold prop_eval.simps, blast)
  have tH: "\<Delta> \<turnstile> ?H : Prop" for \<Delta> using cfp_R2_ty(1)[of \<Delta> False] typed_pp_pure[OF cfp_X_ty(2), of \<Delta>] by blast
  have sH: "shift ?H = ?H" by (simp add: rc_sft cfp_R2_ty(2) cfp_X_closed)
  have tF: "?G \<turnstile> pp_fun Prop ?r : Prop" by (rule typed_pp_fun[OF r])
  have g: "?G \<turnstile>\<^sub>CEV Imp (pp_fun Prop ?r) (Neg ?H)" by (rule rc_pc3[OF i n f]) (use tF tH in blast, unfold prop_eval.simps, blast)
  show ?thesis unfolding k_EF_def by (rule CEV_proves.Inst[OF tF has_type.Neg[OF tH]]) (unfold rc_sft(2) sH, rule g)
qed

subsection \<open>8.5 Statement 6: zE from Rec-free n = 1 Exhaustion, EF, LP and App\<close>

definition cfp_K :: oterm where "cfp_K = Lam Prop (Lam Prop (Var 1))"

lemma cfp_K_ty: "\<Gamma> \<turnstile> cfp_K : Prop \<rightarrow>\<^sub>o rc_u" by (rule infer_type_sound) (simp add: cfp_K_def lookup_def)

lemma cfp_K_closed: "consts_of cfp_K = {}" "shift cfp_K = cfp_K" by (simp_all add: cfp_K_def shift_def)

lemma cfp_K_iff: assumes p: "\<Gamma> \<turnstile> p : Prop" and q: "\<Gamma> \<turnstile> q : Prop" shows "\<Gamma> \<turnstile>\<^sub>CEV (App (App cfp_K p) q \<longleftrightarrow>\<^sub>o p)"
  using CEV_beta_eta_equiv[OF rc_be2[OF has_type.App[OF cfp_K_ty p, unfolded cfp_K_def] q]] by (simp add: cfp_K_def subst0_def flip: shift_def)

lemma cfp_exh1: assumes X: "\<Gamma> \<turnstile> X : rc_u" and r: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp pp_unary_exhaustion (Imp (Conj (pp_pure rc_u X) (pp_fun Prop r)) (Imp (Forall Prop (App (shift X) (Var 0))) (\<box>\<^sub>o (App X r))))" proof -
  let ?A1 = "Forall Prop (Imp (Conj (pp_pure rc_u (Var 1)) (pp_fun Prop (Var 0))) (Imp (Forall Prop (App (Var 2) (Var 0))) (\<box>\<^sub>o (App (Var 1) (Var 0)))))"
  let ?A2 = "Imp (Conj (pp_pure rc_u (shift X)) (pp_fun Prop (Var 0))) (Imp (Forall Prop (App (shift (shift X)) (Var 0))) (\<box>\<^sub>o (App (shift X) (Var 0))))"
  let ?A3 = "Imp (Conj (pp_pure rc_u X) (pp_fun Prop r)) (Imp (Forall Prop (App (shift X) (Var 0))) (\<box>\<^sub>o (App X r)))"
  have ty: "\<Gamma> \<turnstile> pp_unary_exhaustion : Prop" by (rule infer_type_sound) (simp add: pp_unary_exhaustion_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)
  have d: "pp_unary_exhaustion = Forall rc_u ?A1" by (simp add: pp_unary_exhaustion_def)
  have t1: "rc_u # \<Gamma> \<turnstile> ?A1 : Prop" using ty unfolding d by (auto elim: has_type.cases)
  have e1: "subst0 X ?A1 = Forall Prop ?A2" by (simp add: subst0_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def eval_nat_numeral flip: shift_def)
  have u1: "\<Gamma> \<turnstile>\<^sub>CEV Imp pp_unary_exhaustion (Forall Prop ?A2)" unfolding d by (rule cfp_ui[OF t1 X e1])
  have t3: "Prop # \<Gamma> \<turnstile> ?A2 : Prop" using subst0_preserves_typing[OF t1 X] unfolding e1 by (auto elim: has_type.cases)
  have e2: "subst0 r ?A2 = ?A3" by (simp add: subst0_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def flip: shift_def)
  have u2: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Forall Prop ?A2) ?A3" by (rule cfp_ui[OF t3 r e2])
  show ?thesis by (rule rc_pc2[OF u1 u2 has_type.Imp[OF ty subst0_preserves_typing[OF t3 r, unfolded e2]]]) (unfold prop_eval.simps, blast)
qed

definition cfp_H6 :: oterm where "cfp_H6 = Conj (pp_pure (Prop \<rightarrow>\<^sub>o rc_u) cfp_K) (Conj (pp_application_closure Prop rc_u) pp_unary_exhaustion)"

lemma cfp_H6_ty: "\<Gamma> \<turnstile> cfp_H6 : Prop" "shift cfp_H6 = cfp_H6"
  by (rule infer_type_sound, simp add: cfp_H6_def cfp_K_def pp_application_closure_def pp_unary_exhaustion_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)
    (simp add: cfp_H6_def cfp_K_def pp_application_closure_def pp_unary_exhaustion_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def shift_def eval_nat_numeral)

lemma cfp6_step: assumes p: "\<Gamma> \<turnstile> p : Prop" and r: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp cfp_H6 (Imp (pp_fun Prop r) (Imp (pp_pure Prop p) (Imp p (\<box>\<^sub>o p))))" proof -
  let ?X = "App cfp_K p"
  have tX: "\<Gamma> \<turnstile> ?X : rc_u" by (rule has_type.App[OF cfp_K_ty p])
  have sp: "Prop # \<Gamma> \<turnstile> shift p : Prop" and v: "Prop # \<Gamma> \<turnstile> Var 0 : Prop" by (rule weaken_shift_type_ok[OF p]) (simp add: lookup_def)
  have sX: "shift ?X = App cfp_K (shift p)" using cfp_K_closed(2) by (simp add: shift_def)
  have tA: "Prop # \<Gamma> \<turnstile> App (shift ?X) (Var 0) : Prop" unfolding sX by (rule has_type.App[OF has_type.App[OF cfp_K_ty sp] v])
  have a0: "Prop # \<Gamma> \<turnstile>\<^sub>CEV Imp (shift p) (App (shift ?X) (Var 0))" unfolding sX
    by (rule rc_pc1[OF cfp_K_iff[OF sp v] has_type.Imp[OF sp tA[unfolded sX]]]) (unfold prop_eval.simps, blast)
  have a1: "\<Gamma> \<turnstile>\<^sub>CEV Imp p (Forall Prop (App (shift ?X) (Var 0)))" by (rule CEV_proves.Gen[OF p tA a0])
  note x = cfp_K_iff[OF p r] have tXr: "\<Gamma> \<turnstile> App ?X r : Prop" by (rule has_type.App[OF tX r])
  have b0: "\<Gamma> \<turnstile>\<^sub>CEV Imp (App ?X r) p" by (rule rc_pc1[OF x has_type.Imp[OF tXr p]]) (unfold prop_eval.simps, blast)
  note ac = rc_ac[OF cfp_K_ty p] and ex = cfp_exh1[OF tX r] and bx = rc_K[OF b0]
  have tG: "\<Gamma> \<turnstile> Imp cfp_H6 (Imp (pp_fun Prop r) (Imp (pp_pure Prop p) (Imp p (\<box>\<^sub>o p)))) : Prop" using cfp_H6_ty(1)[of \<Gamma>] typed_pp_fun[OF r] typed_pp_pure[OF p] typed_ObjBox[OF p] p by blast
  show ?thesis by (rule rc_pc4[OF ac ex a1 bx tG]) (unfold cfp_H6_def prop_eval.simps, blast)
qed

theorem cfp6_thm: "[] \<turnstile>\<^sub>CEV Imp k_EF (Imp cfp_H6 pp_zeroary_exhaustion)" proof -
  let ?B = "Imp (pp_pure Prop (Var 0)) (Imp (Var 0) (\<box>\<^sub>o (Var 0)))" let ?G = "[Prop, Prop]" let ?Q = "Imp cfp_H6 pp_zeroary_exhaustion"
  have tF: "[Prop] \<turnstile> pp_fun Prop (Var 0) : Prop" by (rule typed_pp_fun) (simp add: lookup_def)
  have v0: "?G \<turnstile> Var 0 : Prop" and v1: "?G \<turnstile> Var 1 : Prop" by (simp_all add: lookup_def)
  note tF1 = typed_pp_fun[OF v1]
  have tB: "?G \<turnstile> ?B : Prop" by (rule infer_type_sound) (simp add: pp_pure_def pp_Pure_def ObjBox_def ObjTrue_def lookup_def)
  have tZ: "\<Gamma> \<turnstile> pp_zeroary_exhaustion : Prop" for \<Gamma> by (rule infer_type_sound) (simp add: pp_zeroary_exhaustion_def pp_pure_def pp_Pure_def ObjBox_def ObjTrue_def lookup_def)
  have sZ: "shift pp_zeroary_exhaustion = pp_zeroary_exhaustion" by (simp add: pp_zeroary_exhaustion_def pp_pure_def pp_Pure_def ObjBox_def ObjTrue_def shift_def)
  have st: "?G \<turnstile>\<^sub>CEV Imp (Conj cfp_H6 (pp_fun Prop (Var 1))) ?B"
    by (rule rc_pc1[OF cfp6_step[OF v0 v1]]) (use cfp_H6_ty(1)[of ?G] tF1 tB in blast, unfold prop_eval.simps, blast)
  have g: "[Prop] \<turnstile>\<^sub>CEV Imp (Conj cfp_H6 (pp_fun Prop (Var 0))) pp_zeroary_exhaustion" unfolding pp_zeroary_exhaustion_def
    by (rule CEV_proves.Gen[OF has_type.Conj[OF cfp_H6_ty(1) tF] tB]) (use st in \<open>simp add: rc_sft cfp_H6_ty(2) k_fun_shift\<close>)
  have sQ: "shift ?Q = ?Q" using cfp_H6_ty(2) sZ by (simp add: shift_def)
  have i: "[Prop] \<turnstile>\<^sub>CEV Imp (pp_fun Prop (Var 0)) (shift ?Q)" unfolding sQ
    by (rule rc_pc1[OF g]) (use tF cfp_H6_ty(1)[of "[Prop]"] tZ[of "[Prop]"] in blast, unfold prop_eval.simps, blast)
  show ?thesis unfolding k_EF_def by (rule CEV_proves.Inst[OF tF has_type.Imp[OF cfp_H6_ty(1) tZ] i])
qed

definition cfp_S6 :: "oterm list" where "cfp_S6 = [k_EF, pp_pure (Prop \<rightarrow>\<^sub>o rc_u) cfp_K, pp_application_closure Prop rc_u, cfp_Exh [Prop]]"

lemma cfp_S6_sub: "set cfp_S6 \<subseteq> pp_CFP_axioms" unfolding cfp_S6_def using cfp_LP[OF cfp_K_ty cfp_K_closed(1)] cfp_AC cfp_mem by simp

theorem cfp6: "[] ; set cfp_S6 \<turnstile>\<^sub>CEV\<^sub>s pp_zeroary_exhaustion" proof -
  have ass: "[] ; set cfp_S6 \<turnstile>\<^sub>CEV\<^sub>s A" if "A \<in> set cfp_S6" for A by (rule CEV_set_derivable.Assumption[OF that pp_CFP_closed]) (use that cfp_S6_sub in blast)
  have h: "[] ; set cfp_S6 \<turnstile>\<^sub>CEV\<^sub>s cfp_and (tl cfp_S6)" by (rule cfp_and_local) (use ass in \<open>auto simp: cfp_S6_def\<close>)
  have e: "[] ; set cfp_S6 \<turnstile>\<^sub>CEV\<^sub>s k_EF" by (rule ass) (simp add: cfp_S6_def)
  have c: "cfp_and (tl cfp_S6) = cfp_H6" by (simp add: cfp_S6_def cfp_H6_def cfp_lit)
  show ?thesis using h e CEV_set_derivable.Derive_MP[OF e CEV_set_derivable.Theorem[OF cfp6_thm]] CEV_set_derivable.Derive_MP unfolding c by blast
qed

section \<open>9. PP fails at every type built from t alone, other than t\<close>

text \<open>By Dowel, with Jacob, 2026-11-08; not Branden Fitelson's. For a type tau with closed logical g : u -> tau and h : tau
  -> u, h(g X) beta-eta X, C_FP refutes PP_tau at a point. Route: CEV_proves_subst_const on lo_T3_CEV, Pure at u replaced
  by pi_tau = lambda X. Pure_tau(g X); the five changed conjuncts are discharged from members of C_FP and PP_tau.\<close>

subsection \<open>9.1 Tools\<close>

lemma k7_be_arg: assumes "beta_eta_equiv \<Gamma> \<sigma> M M'" and "\<Gamma> \<turnstile> F : \<sigma> \<rightarrow>\<^sub>o \<tau>" shows "beta_eta_equiv \<Gamma> \<tau> (App F M) (App F M')"
  using assms proof (induction rule: beta_eta_equiv.induct)
  case (Refl \<Gamma> M \<sigma>) show ?case by (rule beta_eta_equiv.Refl[OF has_type.App[OF Refl.prems Refl.hyps]])
next
  case (Beta \<Gamma> M \<sigma> N) show ?case by (rule beta_eta_equiv.Beta[OF has_type.App[OF Beta.prems Beta.hyps(1)] has_type.App[OF Beta.prems Beta.hyps(2)] compatible_step.App_right[OF Beta.hyps(3)]])
next
  case (Eta \<Gamma> M \<sigma> N) show ?case by (rule beta_eta_equiv.Eta[OF has_type.App[OF Eta.prems Eta.hyps(1)] has_type.App[OF Eta.prems Eta.hyps(2)] compatible_step.App_right[OF Eta.hyps(3)]])
next
  case (Sym \<Gamma> \<sigma> M N) show ?case by (rule beta_eta_equiv.Sym[OF Sym.IH[OF Sym.prems]])
next
  case (Trans \<Gamma> \<sigma> M N P) show ?case by (rule beta_eta_equiv.Trans[OF Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed

lemma k7_pc6: assumes a1: "\<Gamma> \<turnstile>\<^sub>CEV A1" and a2: "\<Gamma> \<turnstile>\<^sub>CEV A2" and a3: "\<Gamma> \<turnstile>\<^sub>CEV A3" and a4: "\<Gamma> \<turnstile>\<^sub>CEV A4" and a5: "\<Gamma> \<turnstile>\<^sub>CEV A5" and a6: "\<Gamma> \<turnstile>\<^sub>CEV A6"
  and b: "\<Gamma> \<turnstile> B : Prop" and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow> prop_eval v A4 \<Longrightarrow> prop_eval v A5 \<Longrightarrow> prop_eval v A6 \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV B" proof -
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp A6 B" by (rule rc_pc5[OF a1 a2 a3 a4 a5 has_type.Imp[OF CEV_proves_formula[OF a6] b]]) (use t in simp)
  then show ?thesis by (rule CEV_proves.MP[OF a6]) qed

lemma k7_pc7: assumes a1: "\<Gamma> \<turnstile>\<^sub>CEV A1" and a2: "\<Gamma> \<turnstile>\<^sub>CEV A2" and a3: "\<Gamma> \<turnstile>\<^sub>CEV A3" and a4: "\<Gamma> \<turnstile>\<^sub>CEV A4" and a5: "\<Gamma> \<turnstile>\<^sub>CEV A5" and a6: "\<Gamma> \<turnstile>\<^sub>CEV A6"
  and a7: "\<Gamma> \<turnstile>\<^sub>CEV A7" and b: "\<Gamma> \<turnstile> B : Prop"
  and t: "\<And>v. prop_eval v A1 \<Longrightarrow> prop_eval v A2 \<Longrightarrow> prop_eval v A3 \<Longrightarrow> prop_eval v A4 \<Longrightarrow> prop_eval v A5 \<Longrightarrow> prop_eval v A6 \<Longrightarrow> prop_eval v A7 \<Longrightarrow> prop_eval v B"
  shows "\<Gamma> \<turnstile>\<^sub>CEV B" proof -
  have "\<Gamma> \<turnstile>\<^sub>CEV Imp A7 B" by (rule k7_pc6[OF a1 a2 a3 a4 a5 a6 has_type.Imp[OF CEV_proves_formula[OF a7] b]]) (use t in simp)
  then show ?thesis by (rule CEV_proves.MP[OF a7]) qed

lemma k7_AC: "\<Delta> \<turnstile> pp_application_closure \<sigma> \<tau> : Prop" by (rule infer_type_sound) (simp add: pp_application_closure_def pp_pure_def pp_Pure_def lookup_def)

lemma k7_rec2: assumes X: "\<Gamma> \<turnstile> X : rc_u" and r: "\<Gamma> \<turnstile> r : Prop"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp pp_unary_recombination (Imp (Conj (pp_pure rc_u X) (pp_fun Prop r)) (Imp (\<box>\<^sub>o (App X r)) (Forall Prop (App (shift X) (Var 0)))))" proof -
  let ?A1 = "Forall Prop (Imp (Conj (pp_pure rc_u (Var 1)) (pp_fun Prop (Var 0))) (Imp (\<box>\<^sub>o (App (Var 1) (Var 0))) (Forall Prop (App (Var 2) (Var 0)))))"
  let ?A2 = "Imp (Conj (pp_pure rc_u (shift X)) (pp_fun Prop (Var 0))) (Imp (\<box>\<^sub>o (App (shift X) (Var 0))) (Forall Prop (App (shift (shift X)) (Var 0))))"
  let ?A3 = "Imp (Conj (pp_pure rc_u X) (pp_fun Prop r)) (Imp (\<box>\<^sub>o (App X r)) (Forall Prop (App (shift X) (Var 0))))"
  have ty: "\<Gamma> \<turnstile> pp_unary_recombination : Prop" by (rule infer_type_sound) (simp add: pp_unary_recombination_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)
  have d: "pp_unary_recombination = Forall rc_u ?A1" by (simp add: pp_unary_recombination_def)
  have t1: "rc_u # \<Gamma> \<turnstile> ?A1 : Prop" using ty unfolding d by (auto elim: has_type.cases)
  have e1: "subst0 X ?A1 = Forall Prop ?A2" by (simp add: subst0_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def eval_nat_numeral flip: shift_def)
  have u1: "\<Gamma> \<turnstile>\<^sub>CEV Imp pp_unary_recombination (Forall Prop ?A2)" unfolding d by (rule cfp_ui[OF t1 X e1])
  have t3: "Prop # \<Gamma> \<turnstile> ?A2 : Prop" using subst0_preserves_typing[OF t1 X] unfolding e1 by (auto elim: has_type.cases)
  have e2: "subst0 r ?A2 = ?A3" by (simp add: subst0_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def flip: shift_def)
  have u2: "\<Gamma> \<turnstile>\<^sub>CEV Imp (Forall Prop ?A2) ?A3" by (rule cfp_ui[OF t3 r e2])
  show ?thesis by (rule rc_pc2[OF u1 u2 has_type.Imp[OF ty subst0_preserves_typing[OF t3 r, unfolded e2]]]) (unfold prop_eval.simps, blast)
qed

subsection \<open>9.2 The retraction and pi_tau\<close>

definition k7_retr :: "otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> bool" where
  "k7_retr \<tau> g h \<longleftrightarrow> (\<forall>\<Gamma>. \<Gamma> \<turnstile> g : rc_u \<rightarrow>\<^sub>o \<tau>) \<and> (\<forall>\<Gamma>. \<Gamma> \<turnstile> h : \<tau> \<rightarrow>\<^sub>o rc_u) \<and> consts_of g = {} \<and> consts_of h = {} \<and>
    (\<forall>s. subst s g = g) \<and> (\<forall>s. subst s h = h) \<and> (\<forall>\<rho>. rename \<rho> g = g) \<and> (\<forall>\<rho>. rename \<rho> h = h) \<and>
    (\<forall>\<Gamma> X. \<Gamma> \<turnstile> X : rc_u \<longrightarrow> beta_eta_equiv \<Gamma> rc_u (App h (App g X)) X)"

definition k7_N :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where "k7_N \<tau> g = Lam rc_u (pp_pure \<tau> (App g (Var 0)))"

definition k7_k :: "otype \<Rightarrow> oterm \<Rightarrow> oterm" where "k7_k \<tau> g = Lam (\<tau> \<rightarrow>\<^sub>o Prop) (Lam rc_u (App (Var 1) (App g (Var 0))))"

lemma k7_R: assumes "k7_retr \<tau> g h" shows "\<Gamma> \<turnstile> g : rc_u \<rightarrow>\<^sub>o \<tau>" "\<Gamma> \<turnstile> h : \<tau> \<rightarrow>\<^sub>o rc_u" "consts_of g = {}" "consts_of h = {}" "subst s g = g" "subst s h = h"
  "rename \<rho> g = g" "rename \<rho> h = h" "\<Gamma> \<turnstile> X : rc_u \<Longrightarrow> beta_eta_equiv \<Gamma> rc_u (App h (App g X)) X" using assms unfolding k7_retr_def by blast+

lemma k7_N_ty: assumes R: "k7_retr \<tau> g h" shows "\<Gamma> \<turnstile> k7_N \<tau> g : rc_c"
  unfolding k7_N_def by (rule has_type.Lam, rule typed_pp_pure, rule has_type.App[OF k7_R(1)[OF R]]) (simp add: lookup_def)

lemma k7_N_closed: assumes R: "k7_retr \<tau> g h" shows "shift (k7_N \<tau> g) = k7_N \<tau> g" by (simp add: k7_N_def pp_pure_def pp_Pure_def shift_def k7_R(7)[OF R])

lemma k7_N_iff: assumes R: "k7_retr \<tau> g h" and X: "\<Gamma> \<turnstile> X : rc_u" shows "\<Gamma> \<turnstile>\<^sub>CEV (App (k7_N \<tau> g) X \<longleftrightarrow>\<^sub>o pp_pure \<tau> (App g X))" proof -
  have t: "\<Gamma> \<turnstile> App (k7_N \<tau> g) X : Prop" by (rule has_type.App[OF k7_N_ty[OF R] X])
  show ?thesis using CEV_beta_eta_equiv[OF rc_be1[OF t[unfolded k7_N_def]]] by (simp add: k7_N_def subst0_def pp_pure_def pp_Pure_def k7_R(5)[OF R]) qed

lemma k7_to: assumes R: "k7_retr \<tau> g h" and X: "\<Gamma> \<turnstile> X : rc_u"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o \<tau>) g) (pp_application_closure rc_u \<tau>)) (Imp (pp_pure rc_u X) (App (k7_N \<tau> g) X))" proof -
  have t: "\<Gamma> \<turnstile> Imp (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o \<tau>) g) (pp_application_closure rc_u \<tau>)) (Imp (pp_pure rc_u X) (App (k7_N \<tau> g) X)) : Prop"
    using typed_pp_pure[OF k7_R(1)[OF R]] k7_AC typed_pp_pure[OF X] has_type.App[OF k7_N_ty[OF R] X] by blast
  show ?thesis by (rule rc_pc2[OF rc_ac[OF k7_R(1)[OF R] X] k7_N_iff[OF R X] t]) (unfold prop_eval.simps, blast) qed

lemma k7_from: assumes R: "k7_retr \<tau> g h" and X: "\<Gamma> \<turnstile> X : rc_u"
  shows "\<Gamma> \<turnstile>\<^sub>CEV Imp (Conj (pp_pure (\<tau> \<rightarrow>\<^sub>o rc_u) h) (pp_application_closure \<tau> rc_u)) (Imp (App (k7_N \<tau> g) X) (pp_pure rc_u X))" proof -
  have gX: "\<Gamma> \<turnstile> App g X : \<tau>" by (rule has_type.App[OF k7_R(1)[OF R] X])
  have c: "\<Gamma> \<turnstile>\<^sub>CEV (App (pp_Pure rc_u) (App h (App g X)) \<longleftrightarrow>\<^sub>o App (pp_Pure rc_u) X)" by (rule CEV_beta_eta_equiv[OF k7_be_arg[OF k7_R(9)[OF R X] typed_pp_Pure]])
  have t: "\<Gamma> \<turnstile> Imp (Conj (pp_pure (\<tau> \<rightarrow>\<^sub>o rc_u) h) (pp_application_closure \<tau> rc_u)) (Imp (App (k7_N \<tau> g) X) (pp_pure rc_u X)) : Prop"
    using typed_pp_pure[OF k7_R(2)[OF R]] k7_AC typed_pp_pure[OF X] has_type.App[OF k7_N_ty[OF R] X] by blast
  show ?thesis by (rule rc_pc3[OF rc_ac[OF k7_R(2)[OF R] gX] k7_N_iff[OF R X] c t]) (unfold pp_pure_def prop_eval.simps, blast) qed

subsection \<open>9.3 The five changed conjuncts, discharged\<close>

lemma k7_sc: assumes sN: "shift N = N" shows
  "subst_const pp_pure_name rc_c N (pp_application_closure rc_c rc_u) = Forall (rc_c \<rightarrow>\<^sub>o rc_u) (Forall rc_c (Imp (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) (Var 1)) (pp_pure rc_c (Var 0))) (App N (App (Var 1) (Var 0)))))"
  "subst_const pp_pure_name rc_c N (pp_application_closure rc_u Prop) = Forall (rc_u \<rightarrow>\<^sub>o Prop) (Forall rc_u (Imp (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o Prop) (Var 1)) (App N (Var 0))) (pp_pure Prop (App (Var 1) (Var 0)))))"
  "subst_const pp_pure_name rc_c N (pp_application_closure rc_u rc_u) = Forall (rc_u \<rightarrow>\<^sub>o rc_u) (Forall rc_u (Imp (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o rc_u) (Var 1)) (App N (Var 0))) (App N (App (Var 1) (Var 0)))))"
  "subst_const pp_pure_name rc_c N pp_unary_recombination = Forall rc_u (Forall Prop (Imp (Conj (App N (Var 1)) (pp_fun Prop (Var 0))) (Imp (\<box>\<^sub>o (App (Var 1) (Var 0))) (Forall Prop (App (Var 2) (Var 0))))))"
  "subst_const pp_pure_name rc_c N (pp_pure rc_c rc_p) = pp_pure rc_c N"
  "subst_const pp_pure_name rc_c N (pp_application_closure rc_c (rc_u \<rightarrow>\<^sub>o rc_u)) = pp_application_closure rc_c (rc_u \<rightarrow>\<^sub>o rc_u)"
  "subst_const pp_pure_name rc_c N (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_P) = pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_P"
  "subst_const pp_pure_name rc_c N (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_Pp) = pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_Pp"
  "subst_const pp_pure_name rc_c N (pp_pure (rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) rc_W) = pp_pure (rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) rc_W"
  "subst_const pp_pure_name rc_c N (pp_pure (rc_u \<rightarrow>\<^sub>o rc_u) k_C) = pp_pure (rc_u \<rightarrow>\<^sub>o rc_u) k_C"
  "subst_const pp_pure_name rc_c N pp_zeroary_exhaustion = pp_zeroary_exhaustion" "subst_const pp_pure_name rc_c N k_EF = k_EF"
  "subst_const pp_pure_name rc_c N ObjTrue = ObjTrue"
  using sN by (simp_all add: pp_application_closure_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def pp_unary_recombination_def pp_zeroary_exhaustion_def
    k_EF_def ObjBox_def ObjTrue_def pp_pure_name_def pp_fun_name_def rc_consts rc_W_consts k_C_consts)

lemma k7_gen2: assumes H: "\<And>\<Delta>. \<Delta> \<turnstile> H : Prop" and s: "shift H = H" and B: "[\<sigma>, \<rho>] \<turnstile> B : Prop" and i: "[\<sigma>, \<rho>] \<turnstile>\<^sub>CEV Imp H B"
  shows "[] \<turnstile>\<^sub>CEV Imp H (Forall \<rho> (Forall \<sigma> B))" using cfp_gen[OF H s, of "[\<sigma>, \<rho>]" "[]" B] B i by simp

lemma k7_D1: assumes R: "k7_retr \<tau> g h" shows "[] \<turnstile>\<^sub>CEV Imp (Conj (pp_application_closure rc_c rc_u) (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o \<tau>) g) (pp_application_closure rc_u \<tau>)))
    (Forall (rc_c \<rightarrow>\<^sub>o rc_u) (Forall rc_c (Imp (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) (Var 1)) (pp_pure rc_c (Var 0))) (App (k7_N \<tau> g) (App (Var 1) (Var 0))))))" (is "_ \<turnstile>\<^sub>CEV Imp ?H _") proof -
  have f: "[rc_c, rc_c \<rightarrow>\<^sub>o rc_u] \<turnstile> Var 1 : rc_c \<rightarrow>\<^sub>o rc_u" and x: "[rc_c, rc_c \<rightarrow>\<^sub>o rc_u] \<turnstile> Var 0 : rc_c" by (simp_all add: lookup_def)
  note fx = has_type.App[OF f x]
  have tH: "\<Delta> \<turnstile> ?H : Prop" for \<Delta> using k7_AC[of \<Delta> rc_c rc_u] k7_AC[of \<Delta> rc_u \<tau>] typed_pp_pure[OF k7_R(1)[OF R]] by blast
  have sH: "shift ?H = ?H" by (simp add: shift_def k7_R(7)[OF R] pp_application_closure_def pp_pure_def pp_Pure_def)
  have tB: "[rc_c, rc_c \<rightarrow>\<^sub>o rc_u] \<turnstile> Imp (Conj (pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) (Var 1)) (pp_pure rc_c (Var 0))) (App (k7_N \<tau> g) (App (Var 1) (Var 0))) : Prop"
    using typed_pp_pure[OF f] typed_pp_pure[OF x] has_type.App[OF k7_N_ty[OF R] fx] by blast
  show ?thesis by (rule k7_gen2[OF tH sH tB], rule rc_pc2[OF rc_ac[OF f x] k7_to[OF R fx] has_type.Imp[OF tH tB]]) (unfold prop_eval.simps, blast) qed

lemma k7_D2: assumes R: "k7_retr \<tau> g h" shows "[] \<turnstile>\<^sub>CEV Imp (Conj (pp_application_closure rc_u Prop) (Conj (pp_pure (\<tau> \<rightarrow>\<^sub>o rc_u) h) (pp_application_closure \<tau> rc_u)))
    (Forall (rc_u \<rightarrow>\<^sub>o Prop) (Forall rc_u (Imp (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o Prop) (Var 1)) (App (k7_N \<tau> g) (Var 0))) (pp_pure Prop (App (Var 1) (Var 0))))))" (is "_ \<turnstile>\<^sub>CEV Imp ?H _") proof -
  have f: "[rc_u, rc_u \<rightarrow>\<^sub>o Prop] \<turnstile> Var 1 : rc_u \<rightarrow>\<^sub>o Prop" and x: "[rc_u, rc_u \<rightarrow>\<^sub>o Prop] \<turnstile> Var 0 : rc_u" by (simp_all add: lookup_def)
  have tH: "\<Delta> \<turnstile> ?H : Prop" for \<Delta> using k7_AC[of \<Delta> rc_u Prop] k7_AC[of \<Delta> \<tau> rc_u] typed_pp_pure[OF k7_R(2)[OF R]] by blast
  have sH: "shift ?H = ?H" by (simp add: shift_def k7_R(8)[OF R] pp_application_closure_def pp_pure_def pp_Pure_def)
  have tB: "[rc_u, rc_u \<rightarrow>\<^sub>o Prop] \<turnstile> Imp (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o Prop) (Var 1)) (App (k7_N \<tau> g) (Var 0))) (pp_pure Prop (App (Var 1) (Var 0))) : Prop"
    using typed_pp_pure[OF f] has_type.App[OF k7_N_ty[OF R] x] typed_pp_pure[OF has_type.App[OF f x]] by blast
  show ?thesis by (rule k7_gen2[OF tH sH tB], rule rc_pc2[OF rc_ac[OF f x] k7_from[OF R x] has_type.Imp[OF tH tB]]) (unfold prop_eval.simps, blast) qed

lemma k7_D3: assumes R: "k7_retr \<tau> g h" shows "[] \<turnstile>\<^sub>CEV Imp (Conj (pp_application_closure rc_u rc_u) (Conj (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o \<tau>) g) (pp_application_closure rc_u \<tau>))
    (Conj (pp_pure (\<tau> \<rightarrow>\<^sub>o rc_u) h) (pp_application_closure \<tau> rc_u))))
    (Forall (rc_u \<rightarrow>\<^sub>o rc_u) (Forall rc_u (Imp (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o rc_u) (Var 1)) (App (k7_N \<tau> g) (Var 0))) (App (k7_N \<tau> g) (App (Var 1) (Var 0))))))" (is "_ \<turnstile>\<^sub>CEV Imp ?H _") proof -
  have f: "[rc_u, rc_u \<rightarrow>\<^sub>o rc_u] \<turnstile> Var 1 : rc_u \<rightarrow>\<^sub>o rc_u" and x: "[rc_u, rc_u \<rightarrow>\<^sub>o rc_u] \<turnstile> Var 0 : rc_u" by (simp_all add: lookup_def)
  note fx = has_type.App[OF f x]
  have tH: "\<Delta> \<turnstile> ?H : Prop" for \<Delta> using k7_AC[of \<Delta> rc_u rc_u] k7_AC[of \<Delta> rc_u \<tau>] k7_AC[of \<Delta> \<tau> rc_u] typed_pp_pure[OF k7_R(1)[OF R]] typed_pp_pure[OF k7_R(2)[OF R]] by blast
  have sH: "shift ?H = ?H" by (simp add: shift_def k7_R(7,8)[OF R] pp_application_closure_def pp_pure_def pp_Pure_def)
  have tB: "[rc_u, rc_u \<rightarrow>\<^sub>o rc_u] \<turnstile> Imp (Conj (pp_pure (rc_u \<rightarrow>\<^sub>o rc_u) (Var 1)) (App (k7_N \<tau> g) (Var 0))) (App (k7_N \<tau> g) (App (Var 1) (Var 0))) : Prop"
    using typed_pp_pure[OF f] has_type.App[OF k7_N_ty[OF R] x] has_type.App[OF k7_N_ty[OF R] fx] by blast
  show ?thesis by (rule k7_gen2[OF tH sH tB], rule rc_pc3[OF rc_ac[OF f x] k7_from[OF R x] k7_to[OF R fx] has_type.Imp[OF tH tB]]) (unfold prop_eval.simps, blast) qed

lemma k7_D4: assumes R: "k7_retr \<tau> g h" shows "[] \<turnstile>\<^sub>CEV Imp (Conj pp_unary_recombination (Conj (pp_pure (\<tau> \<rightarrow>\<^sub>o rc_u) h) (pp_application_closure \<tau> rc_u)))
    (Forall rc_u (Forall Prop (Imp (Conj (App (k7_N \<tau> g) (Var 1)) (pp_fun Prop (Var 0))) (Imp (\<box>\<^sub>o (App (Var 1) (Var 0))) (Forall Prop (App (Var 2) (Var 0)))))))" (is "_ \<turnstile>\<^sub>CEV Imp ?H _") proof -
  have X: "[Prop, rc_u] \<turnstile> Var 1 : rc_u" and r: "[Prop, rc_u] \<turnstile> Var 0 : Prop" by (simp_all add: lookup_def)
  have tR: "\<Delta> \<turnstile> pp_unary_recombination : Prop" for \<Delta> by (rule infer_type_sound) (simp add: pp_unary_recombination_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def lookup_def)
  have tH: "\<Delta> \<turnstile> ?H : Prop" for \<Delta> using tR[of \<Delta>] k7_AC[of \<Delta> \<tau> rc_u] typed_pp_pure[OF k7_R(2)[OF R]] by blast
  have sH: "shift ?H = ?H" by (simp add: shift_def k7_R(8)[OF R] pp_unary_recombination_def pp_application_closure_def pp_pure_def pp_Pure_def pp_fun_def pp_Fun_def ObjBox_def ObjTrue_def)
  have tB: "[Prop, rc_u] \<turnstile> Imp (Conj (App (k7_N \<tau> g) (Var 1)) (pp_fun Prop (Var 0))) (Imp (\<box>\<^sub>o (App (Var 1) (Var 0))) (Forall Prop (App (Var 2) (Var 0)))) : Prop"
    using has_type.App[OF k7_N_ty[OF R] X] typed_pp_fun[OF r] typed_ObjBox[OF has_type.App[OF X r]] has_type.App[of "[Prop, Prop, rc_u]" "Var 2" Prop Prop "Var 0"] by (auto simp: lookup_def eval_nat_numeral)
  have e: "shift (Var 1) = Var 2" by (simp add: shift_def)
  show ?thesis by (rule k7_gen2[OF tH sH tB], rule rc_pc2[OF k7_rec2[OF X r, unfolded e] k7_from[OF R X] has_type.Imp[OF tH tB]]) (unfold prop_eval.simps, blast) qed

lemma k7_D5: assumes R: "k7_retr \<tau> g h" shows "[] \<turnstile>\<^sub>CEV Imp (Conj (pp_pure ((\<tau> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o rc_c) (k7_k \<tau> g)) (Conj (pp_application_closure (\<tau> \<rightarrow>\<^sub>o Prop) rc_c) (pp_purity_of_pure \<tau>)))
    (pp_pure rc_c (k7_N \<tau> g))" proof -
  have k: "[] \<turnstile> k7_k \<tau> g : (\<tau> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o rc_c" unfolding k7_k_def
    by (intro has_type.Lam, rule has_type.App[of _ "Var 1" \<tau> Prop], simp add: lookup_def, rule has_type.App[OF k7_R(1)[OF R]], simp add: lookup_def)
  have e: "subst0 (pp_Pure \<tau>) (Lam rc_u (App (Var 1) (App g (Var 0)))) = k7_N \<tau> g" by (simp add: subst0_def k7_N_def pp_pure_def pp_Pure_def k7_R(5)[OF R])
  have st: "App (k7_k \<tau> g) (pp_Pure \<tau>) \<rightarrow>\<^sub>\<beta> k7_N \<tau> g" using beta_contract.beta[of "\<tau> \<rightarrow>\<^sub>o Prop" "Lam rc_u (App (Var 1) (App g (Var 0)))" "pp_Pure \<tau>"] unfolding e k7_k_def .
  have kP: "[] \<turnstile> App (k7_k \<tau> g) (pp_Pure \<tau>) : rc_c" by (rule has_type.App[OF k typed_pp_Pure])
  have b: "[] \<turnstile>\<^sub>CEV (pp_pure rc_c (App (k7_k \<tau> g) (pp_Pure \<tau>)) \<longleftrightarrow>\<^sub>o pp_pure rc_c (k7_N \<tau> g))" unfolding pp_pure_def
    by (rule CEV_beta_eta_equiv[OF beta_eta_equiv.Beta[OF has_type.App[OF typed_pp_Pure kP] has_type.App[OF typed_pp_Pure k7_N_ty[OF R]] compatible_step.App_right[OF compatible_step.root[of beta_contract, OF st]]]])
  have t: "[] \<turnstile> Imp (Conj (pp_pure ((\<tau> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o rc_c) (k7_k \<tau> g)) (Conj (pp_application_closure (\<tau> \<rightarrow>\<^sub>o Prop) rc_c) (pp_purity_of_pure \<tau>))) (pp_pure rc_c (k7_N \<tau> g)) : Prop"
    using typed_pp_pure[OF k] k7_AC typed_pp_purity_of_pure typed_pp_pure[OF k7_N_ty[OF R]] by blast
  show ?thesis by (rule rc_pc2[OF rc_ac[OF k typed_pp_Pure] b t]) (unfold pp_purity_of_pure_def prop_eval.simps, blast) qed

subsection \<open>9.4 The theorem, for a type with a retraction\<close>

lemma k7_k_ty: assumes R: "k7_retr \<tau> g h" shows "\<Gamma> \<turnstile> k7_k \<tau> g : (\<tau> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o rc_c" unfolding k7_k_def
  by (intro has_type.Lam, rule has_type.App[of _ "Var 1" \<tau> Prop], simp add: lookup_def, rule has_type.App[OF k7_R(1)[OF R]], simp add: lookup_def)

definition k7_S :: "otype \<Rightarrow> oterm \<Rightarrow> oterm \<Rightarrow> oterm list" where "k7_S \<tau> g h = [pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_P, pp_pure (rc_c \<rightarrow>\<^sub>o rc_u) rc_Pp,
  pp_pure (rc_c \<rightarrow>\<^sub>o (rc_u \<rightarrow>\<^sub>o rc_u)) rc_W, pp_pure (rc_u \<rightarrow>\<^sub>o rc_u) k_C, pp_pure (rc_u \<rightarrow>\<^sub>o \<tau>) g, pp_pure (\<tau> \<rightarrow>\<^sub>o rc_u) h, pp_pure ((\<tau> \<rightarrow>\<^sub>o Prop) \<rightarrow>\<^sub>o rc_c) (k7_k \<tau> g),
  pp_application_closure rc_c rc_u, pp_application_closure rc_c (rc_u \<rightarrow>\<^sub>o rc_u), pp_application_closure rc_u Prop, pp_application_closure rc_u rc_u,
  pp_application_closure rc_u \<tau>, pp_application_closure \<tau> rc_u, pp_application_closure (\<tau> \<rightarrow>\<^sub>o Prop) rc_c, cfp_Exh [], cfp_Rec [Prop], k_EF]"

lemma k7_S_sub: assumes R: "k7_retr \<tau> g h" shows "set (k7_S \<tau> g h) \<subseteq> pp_CFP_axioms" proof -
  have k: "consts_of (k7_k \<tau> g) = {}" by (simp add: k7_k_def k7_R(3)[OF R])
  show ?thesis unfolding k7_S_def using cfp_LP[OF rc_P_ty rc_consts(4)] cfp_LP[OF rc_Pp_ty rc_consts(5)] cfp_LP[OF rc_W_ty rc_W_consts] cfp_LP[OF k_C_ty k_C_consts]
    cfp_LP[OF k7_R(1)[OF R] k7_R(3)[OF R]] cfp_LP[OF k7_R(2)[OF R] k7_R(4)[OF R]] cfp_LP[OF k7_k_ty[OF R] k] cfp_AC cfp_mem by simp qed

theorem k7_thm: assumes R: "k7_retr \<tau> g h" shows "[] \<turnstile>\<^sub>CEV Imp (cfp_and (k7_S \<tau> g h)) (Neg (pp_purity_of_pure \<tau>))" proof -
  have sub: "[] \<turnstile>\<^sub>CEV subst_const pp_pure_name rc_c (k7_N \<tau> g) (Imp rcT3 ObjFalse)" by (rule CEV_proves_subst_const[OF lo_T3_CEV k7_N_ty[OF R]])
  have tG: "[] \<turnstile> Imp (cfp_and (k7_S \<tau> g h)) (Neg (pp_purity_of_pure \<tau>)) : Prop"
    by (rule has_type.Imp[OF cfp_and_ty has_type.Neg[OF typed_pp_purity_of_pure]]) (use k7_S_sub[OF R] pp_CFP_closed in blast)
  show ?thesis by (rule k7_pc7[OF sub k7_D1[OF R] k7_D2[OF R] k7_D3[OF R] k7_D4[OF R] k7_D5[OF R] CEV_proves_ObjTrue tG])
    (simp only: rcT3_def subst_const.simps k7_sc[OF k7_N_closed[OF R]] k7_S_def cfp_and.simps cfp_lit ObjFalse_def prop_eval.simps, blast)
qed

theorem k7: assumes R: "k7_retr \<tau> g h" shows "[] ; pp_CFP_axioms \<turnstile>\<^sub>CEV\<^sub>s Neg (pp_purity_of_pure \<tau>)" proof -
  have "[] ; pp_CFP_axioms \<turnstile>\<^sub>CEV\<^sub>s cfp_and (k7_S \<tau> g h)" by (rule cfp_and_local) (use k7_S_sub[OF R] pp_CFP_closed in blast)
  then show ?thesis by (rule CEV_set_derivable.Derive_MP[OF _ CEV_set_derivable.Theorem[OF k7_thm[OF R]]]) qed

subsection \<open>9.5 A retraction at every type built from t alone, other than t\<close>

lemma k7_be_lam: assumes "beta_eta_equiv \<Delta> \<tau> M M'" and "\<Delta> = \<sigma> # \<Gamma>" shows "beta_eta_equiv \<Gamma> (\<sigma> \<rightarrow>\<^sub>o \<tau>) (Lam \<sigma> M) (Lam \<sigma> M')"
  using assms proof (induction rule: beta_eta_equiv.induct)
  case (Refl \<Delta> M \<tau>) show ?case by (rule beta_eta_equiv.Refl[OF has_type.Lam]) (use Refl in simp)
next
  case (Beta \<Delta> M \<tau> N) show ?case by (rule beta_eta_equiv.Beta[OF has_type.Lam has_type.Lam compatible_step.Lam_body[OF Beta.hyps(3)]]) (use Beta in simp_all)
next
  case (Eta \<Delta> M \<tau> N) show ?case by (rule beta_eta_equiv.Eta[OF has_type.Lam has_type.Lam compatible_step.Lam_body[OF Eta.hyps(3)]]) (use Eta in simp_all)
next
  case (Sym \<Delta> \<tau> M N) show ?case by (rule beta_eta_equiv.Sym[OF Sym.IH[OF Sym.prems]])
next
  case (Trans \<Delta> \<tau> M N P) show ?case by (rule beta_eta_equiv.Trans[OF Trans.IH(1)[OF Trans.prems] Trans.IH(2)[OF Trans.prems]])
qed

fun k7_tonly :: "otype \<Rightarrow> bool" where "k7_tonly Prop = True" | "k7_tonly Ind = False" | "k7_tonly (\<alpha> \<rightarrow>\<^sub>o \<beta>) = (k7_tonly \<alpha> \<and> k7_tonly \<beta>)"

fun k7_c :: "otype \<Rightarrow> oterm" where "k7_c (\<alpha> \<rightarrow>\<^sub>o \<beta>) = Lam \<alpha> (k7_c \<beta>)" | "k7_c _ = ObjTrue"

fun k7_tg :: "otype \<Rightarrow> oterm" where "k7_tg (\<alpha> \<rightarrow>\<^sub>o \<beta>) = Lam Prop (Lam \<alpha> (App (k7_tg \<beta>) (Var 1)))" | "k7_tg _ = Lam Prop (Var 0)"

fun k7_th :: "otype \<Rightarrow> oterm" where "k7_th (\<alpha> \<rightarrow>\<^sub>o \<beta>) = Lam (\<alpha> \<rightarrow>\<^sub>o \<beta>) (App (k7_th \<beta>) (App (Var 0) (k7_c \<alpha>)))" | "k7_th _ = Lam Prop (Var 0)"

lemma k7_cl: "(\<forall>s. subst s (k7_c \<sigma>) = k7_c \<sigma>) \<and> (\<forall>s. subst s (k7_tg \<sigma>) = k7_tg \<sigma>) \<and> (\<forall>s. subst s (k7_th \<sigma>) = k7_th \<sigma>) \<and>
    (\<forall>\<rho>. rename \<rho> (k7_c \<sigma>) = k7_c \<sigma>) \<and> (\<forall>\<rho>. rename \<rho> (k7_tg \<sigma>) = k7_tg \<sigma>) \<and> (\<forall>\<rho>. rename \<rho> (k7_th \<sigma>) = k7_th \<sigma>) \<and>
    consts_of (k7_c \<sigma>) = {} \<and> consts_of (k7_tg \<sigma>) = {} \<and> consts_of (k7_th \<sigma>) = {}"
  by (induction \<sigma>) (simp_all add: ObjTrue_def)

lemma k7_tyc: "k7_tonly \<sigma> \<Longrightarrow> (\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_c \<sigma> : \<sigma>) \<and> (\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_tg \<sigma> : Prop \<rightarrow>\<^sub>o \<sigma>) \<and> (\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_th \<sigma> : \<sigma> \<rightarrow>\<^sub>o Prop)"
proof (induction \<sigma>)
  case (Arr \<alpha> \<beta>)
  then have a: "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_c \<alpha> : \<alpha>" and b: "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_c \<beta> : \<beta>" "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_tg \<beta> : Prop \<rightarrow>\<^sub>o \<beta>" "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_th \<beta> : \<beta> \<rightarrow>\<^sub>o Prop" by simp_all
  have c: "\<Gamma> \<turnstile> k7_c (\<alpha> \<rightarrow>\<^sub>o \<beta>) : \<alpha> \<rightarrow>\<^sub>o \<beta>" for \<Gamma> using b(1) by (auto intro: has_type.Lam)
  have g: "\<Gamma> \<turnstile> k7_tg (\<alpha> \<rightarrow>\<^sub>o \<beta>) : Prop \<rightarrow>\<^sub>o (\<alpha> \<rightarrow>\<^sub>o \<beta>)" for \<Gamma> by (simp, rule has_type.Lam, rule has_type.Lam, rule has_type.App[OF b(2)[rule_format]]) (simp add: lookup_def)
  have h: "\<Gamma> \<turnstile> k7_th (\<alpha> \<rightarrow>\<^sub>o \<beta>) : (\<alpha> \<rightarrow>\<^sub>o \<beta>) \<rightarrow>\<^sub>o Prop" for \<Gamma>
    by (simp, rule has_type.Lam, rule has_type.App[OF b(3)[rule_format]], rule has_type.App[OF _ a[rule_format]]) (simp add: lookup_def)
  show ?case using c g h by blast
qed (auto intro: has_type.Lam typed_ObjTrue simp: lookup_def)

lemma k7_s0: "subst0 a (App M N) = App (subst0 a M) (subst0 a N)" "subst0 a (Var 0) = a" "subst0 a (k7_tg \<sigma>) = k7_tg \<sigma>" "subst0 a (k7_th \<sigma>) = k7_th \<sigma>"
  "subst0 a (k7_c \<sigma>) = k7_c \<sigma>" by (simp_all add: subst0_def k7_cl)

lemma k7_be_t: "k7_tonly \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> p : Prop \<Longrightarrow> beta_eta_equiv \<Gamma> Prop (App (k7_th \<sigma>) (App (k7_tg \<sigma>) p)) p"
proof (induction \<sigma> arbitrary: \<Gamma> p)
  case (Arr \<alpha> \<beta>)
  have ta: "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_c \<alpha> : \<alpha>" and tb: "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_tg \<beta> : Prop \<rightarrow>\<^sub>o \<beta>" "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_th \<beta> : \<beta> \<rightarrow>\<^sub>o Prop"
    and ts: "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_tg (\<alpha> \<rightarrow>\<^sub>o \<beta>) : Prop \<rightarrow>\<^sub>o (\<alpha> \<rightarrow>\<^sub>o \<beta>)" "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_th (\<alpha> \<rightarrow>\<^sub>o \<beta>) : (\<alpha> \<rightarrow>\<^sub>o \<beta>) \<rightarrow>\<^sub>o Prop"
    using k7_tyc[of \<alpha>] k7_tyc[of \<beta>] k7_tyc[of "\<alpha> \<rightarrow>\<^sub>o \<beta>"] Arr.prems(1) by simp_all
  let ?P1 = "Lam \<alpha> (App (k7_tg \<beta>) (shift p))"
  have sp: "\<alpha> # \<Gamma> \<turnstile> shift p : Prop" by (rule weaken_shift_type_ok[OF Arr.prems(2)])
  have P1: "\<Gamma> \<turnstile> ?P1 : \<alpha> \<rightarrow>\<^sub>o \<beta>" by (rule has_type.Lam, rule has_type.App[OF tb(1)[rule_format] sp])
  have t0: "\<Gamma> \<turnstile> App (k7_th (\<alpha> \<rightarrow>\<^sub>o \<beta>)) (App (k7_tg (\<alpha> \<rightarrow>\<^sub>o \<beta>)) p) : Prop" by (rule has_type.App[OF ts(2)[rule_format] has_type.App[OF ts(1)[rule_format] Arr.prems(2)]])
  have t1: "\<Gamma> \<turnstile> App (k7_th (\<alpha> \<rightarrow>\<^sub>o \<beta>)) ?P1 : Prop" by (rule has_type.App[OF ts(2)[rule_format] P1])
  have t2: "\<Gamma> \<turnstile> App (k7_th \<beta>) (App ?P1 (k7_c \<alpha>)) : Prop" by (rule has_type.App[OF tb(2)[rule_format] has_type.App[OF P1 ta[rule_format]]])
  have t3: "\<Gamma> \<turnstile> App (k7_th \<beta>) (App (k7_tg \<beta>) p) : Prop" by (rule has_type.App[OF tb(2)[rule_format] has_type.App[OF tb(1)[rule_format] Arr.prems(2)]])
  have e1: "subst0 p (Lam \<alpha> (App (k7_tg \<beta>) (Var 1))) = ?P1" by (simp add: subst0_def shift_def k7_cl)
  have b1: "App (k7_tg (\<alpha> \<rightarrow>\<^sub>o \<beta>)) p \<rightarrow>\<^sub>\<beta> ?P1" using beta_contract.beta[of Prop "Lam \<alpha> (App (k7_tg \<beta>) (Var 1))" p] unfolding e1 by simp
  have e2: "subst0 ?P1 (App (k7_th \<beta>) (App (Var 0) (k7_c \<alpha>))) = App (k7_th \<beta>) (App ?P1 (k7_c \<alpha>))" by (simp only: k7_s0)
  have b2: "App (k7_th (\<alpha> \<rightarrow>\<^sub>o \<beta>)) ?P1 \<rightarrow>\<^sub>\<beta> App (k7_th \<beta>) (App ?P1 (k7_c \<alpha>))" using beta_contract.beta[of "\<alpha> \<rightarrow>\<^sub>o \<beta>" "App (k7_th \<beta>) (App (Var 0) (k7_c \<alpha>))" ?P1] unfolding e2 by simp
  have e3: "subst0 (k7_c \<alpha>) (App (k7_tg \<beta>) (shift p)) = App (k7_tg \<beta>) p" by (simp only: k7_s0 subst0_shift)
  have b3: "App ?P1 (k7_c \<alpha>) \<rightarrow>\<^sub>\<beta> App (k7_tg \<beta>) p" using beta_contract.beta[of \<alpha> "App (k7_tg \<beta>) (shift p)" "k7_c \<alpha>"] unfolding e3 .
  note r = compatible_step.root[of beta_contract]
  have s1: "beta_eta_equiv \<Gamma> Prop (App (k7_th (\<alpha> \<rightarrow>\<^sub>o \<beta>)) (App (k7_tg (\<alpha> \<rightarrow>\<^sub>o \<beta>)) p)) (App (k7_th (\<alpha> \<rightarrow>\<^sub>o \<beta>)) ?P1)"
    by (rule beta_eta_equiv.Beta[OF t0 t1 compatible_step.App_right[OF r[OF b1]]])
  have s2: "beta_eta_equiv \<Gamma> Prop (App (k7_th (\<alpha> \<rightarrow>\<^sub>o \<beta>)) ?P1) (App (k7_th \<beta>) (App ?P1 (k7_c \<alpha>)))" by (rule beta_eta_equiv.Beta[OF t1 t2 r[OF b2]])
  have s3: "beta_eta_equiv \<Gamma> Prop (App (k7_th \<beta>) (App ?P1 (k7_c \<alpha>))) (App (k7_th \<beta>) (App (k7_tg \<beta>) p))" by (rule beta_eta_equiv.Beta[OF t2 t3 compatible_step.App_right[OF r[OF b3]]])
  show ?case using beta_eta_equiv.Trans[OF s1 beta_eta_equiv.Trans[OF s2 beta_eta_equiv.Trans[OF s3 Arr.IH(2)[of \<Gamma> p]]]] Arr.prems by simp
next
  case Prop
  let ?I = "Lam Prop (Var 0)"
  have I: "\<Gamma> \<turnstile> ?I : Prop \<rightarrow>\<^sub>o Prop" by (rule has_type.Lam) (simp add: lookup_def)
  have t0: "\<Gamma> \<turnstile> App ?I (App ?I p) : Prop" and t1: "\<Gamma> \<turnstile> App ?I p : Prop" by (rule has_type.App[OF I has_type.App[OF I Prop.prems(2)]], rule has_type.App[OF I Prop.prems(2)])
  have b1: "App ?I (App ?I p) \<rightarrow>\<^sub>\<beta> App ?I p" using beta_contract.beta[of Prop "Var 0" "App ?I p"] by (simp add: k7_s0(2))
  have b2: "App ?I p \<rightarrow>\<^sub>\<beta> p" using beta_contract.beta[of Prop "Var 0" p] by (simp add: k7_s0(2))
  show ?case using beta_eta_equiv.Trans[OF beta_eta_equiv.Beta[OF t0 t1 compatible_step.root[of beta_contract, OF b1]] beta_eta_equiv.Beta[OF t1 Prop.prems(2) compatible_step.root[of beta_contract, OF b2]]] by simp
qed simp

definition k7_G :: "otype \<Rightarrow> otype \<Rightarrow> oterm" where "k7_G \<alpha> \<beta> = Lam rc_u (Lam \<alpha> (App (k7_tg \<beta>) (App (Var 1) (App (k7_th \<alpha>) (Var 0)))))"

definition k7_H :: "otype \<Rightarrow> otype \<Rightarrow> oterm" where "k7_H \<alpha> \<beta> = Lam (\<alpha> \<rightarrow>\<^sub>o \<beta>) (Lam Prop (App (k7_th \<beta>) (App (Var 1) (App (k7_tg \<alpha>) (Var 0)))))"

lemma k7_GH: assumes "k7_tonly \<alpha>" "k7_tonly \<beta>" shows "\<Gamma> \<turnstile> k7_G \<alpha> \<beta> : rc_u \<rightarrow>\<^sub>o (\<alpha> \<rightarrow>\<^sub>o \<beta>)" "\<Gamma> \<turnstile> k7_H \<alpha> \<beta> : (\<alpha> \<rightarrow>\<^sub>o \<beta>) \<rightarrow>\<^sub>o rc_u" proof -
  have a: "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_tg \<alpha> : Prop \<rightarrow>\<^sub>o \<alpha>" "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_th \<alpha> : \<alpha> \<rightarrow>\<^sub>o Prop" and b: "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_tg \<beta> : Prop \<rightarrow>\<^sub>o \<beta>" "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_th \<beta> : \<beta> \<rightarrow>\<^sub>o Prop"
    using k7_tyc assms by blast+
  show "\<Gamma> \<turnstile> k7_G \<alpha> \<beta> : rc_u \<rightarrow>\<^sub>o (\<alpha> \<rightarrow>\<^sub>o \<beta>)" unfolding k7_G_def
    by (rule has_type.Lam, rule has_type.Lam, rule has_type.App[OF b(1)[rule_format]], rule has_type.App[of _ "Var 1" Prop], simp add: lookup_def, rule has_type.App[OF a(2)[rule_format]], simp add: lookup_def)
  show "\<Gamma> \<turnstile> k7_H \<alpha> \<beta> : (\<alpha> \<rightarrow>\<^sub>o \<beta>) \<rightarrow>\<^sub>o rc_u" unfolding k7_H_def
    by (rule has_type.Lam, rule has_type.Lam, rule has_type.App[OF b(2)[rule_format]], rule has_type.App[of _ "Var 1" \<alpha>], simp add: lookup_def, rule has_type.App[OF a(1)[rule_format]], simp add: lookup_def)
qed

lemma k7_be_u: assumes ta: "k7_tonly \<alpha>" and tb: "k7_tonly \<beta>" and X: "\<Gamma> \<turnstile> X : rc_u" shows "beta_eta_equiv \<Gamma> rc_u (App (k7_H \<alpha> \<beta>) (App (k7_G \<alpha> \<beta>) X)) X" proof -
  have a: "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_tg \<alpha> : Prop \<rightarrow>\<^sub>o \<alpha>" "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_th \<alpha> : \<alpha> \<rightarrow>\<^sub>o Prop" and b: "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_tg \<beta> : Prop \<rightarrow>\<^sub>o \<beta>" "\<forall>\<Gamma>. \<Gamma> \<turnstile> k7_th \<beta> : \<beta> \<rightarrow>\<^sub>o Prop"
    using k7_tyc ta tb by blast+
  let ?G = "k7_G \<alpha> \<beta>" let ?A = "App (k7_tg \<alpha>) (Var 0)" let ?q = "App (k7_th \<alpha>) ?A"
  let ?GX = "Lam \<alpha> (App (k7_tg \<beta>) (App (shift (shift X)) (App (k7_th \<alpha>) (Var 0))))"
  let ?M1 = "Lam Prop (App (k7_th \<beta>) (App (App ?G (shift X)) ?A))" let ?M2 = "Lam Prop (App (k7_th \<beta>) (App ?GX ?A))"
  let ?M3 = "Lam Prop (App (k7_th \<beta>) (App (k7_tg \<beta>) (App (shift X) ?q)))" let ?M4 = "Lam Prop (App (shift X) ?q)" let ?M5 = "Lam Prop (App (shift X) (Var 0))"
  have sX: "Prop # \<Gamma> \<turnstile> shift X : rc_u" by (rule weaken_shift_type_ok[OF X])
  have ssX: "\<alpha> # Prop # \<Gamma> \<turnstile> shift (shift X) : rc_u" by (rule weaken_shift_type_ok[OF sX])
  have v0: "Prop # \<Gamma> \<turnstile> Var 0 : Prop" "\<alpha> # Prop # \<Gamma> \<turnstile> Var 0 : \<alpha>" by (simp_all add: lookup_def)
  have A: "Prop # \<Gamma> \<turnstile> ?A : \<alpha>" by (rule has_type.App[OF a(1)[rule_format] v0(1)])
  have q: "Prop # \<Gamma> \<turnstile> ?q : Prop" by (rule has_type.App[OF a(2)[rule_format] A])
  have GX: "Prop # \<Gamma> \<turnstile> ?GX : \<alpha> \<rightarrow>\<^sub>o \<beta>" by (rule has_type.Lam, rule has_type.App[OF b(1)[rule_format] has_type.App[OF ssX has_type.App[OF a(2)[rule_format] v0(2)]]])
  have t0: "\<Gamma> \<turnstile> App (k7_H \<alpha> \<beta>) (App ?G X) : rc_u" by (rule has_type.App[OF k7_GH(2)[OF ta tb] has_type.App[OF k7_GH(1)[OF ta tb] X]])
  have t1: "\<Gamma> \<turnstile> ?M1 : rc_u" by (rule has_type.Lam, rule has_type.App[OF b(2)[rule_format] has_type.App[OF has_type.App[OF k7_GH(1)[OF ta tb] sX] A]])
  have t2: "\<Gamma> \<turnstile> ?M2 : rc_u" by (rule has_type.Lam, rule has_type.App[OF b(2)[rule_format] has_type.App[OF GX A]])
  have t3: "\<Gamma> \<turnstile> ?M3 : rc_u" by (rule has_type.Lam, rule has_type.App[OF b(2)[rule_format] has_type.App[OF b(1)[rule_format] has_type.App[OF sX q]]])
  have e1: "subst0 (App ?G X) (Lam Prop (App (k7_th \<beta>) (App (Var 1) ?A))) = ?M1" by (simp add: subst0_def shift_def k7_G_def k7_cl)
  have b1: "App (k7_H \<alpha> \<beta>) (App ?G X) \<rightarrow>\<^sub>\<beta> ?M1" using beta_contract.beta[of "\<alpha> \<rightarrow>\<^sub>o \<beta>" "Lam Prop (App (k7_th \<beta>) (App (Var 1) ?A))" "App ?G X"] unfolding e1 k7_H_def .
  have e2: "subst0 (shift X) (Lam \<alpha> (App (k7_tg \<beta>) (App (Var 1) (App (k7_th \<alpha>) (Var 0))))) = ?GX" by (simp add: subst0_def shift_def k7_cl)
  have b2: "App ?G (shift X) \<rightarrow>\<^sub>\<beta> ?GX" using beta_contract.beta[of rc_u "Lam \<alpha> (App (k7_tg \<beta>) (App (Var 1) (App (k7_th \<alpha>) (Var 0))))" "shift X"] unfolding e2 k7_G_def .
  have e3: "subst0 ?A (App (k7_tg \<beta>) (App (shift (shift X)) (App (k7_th \<alpha>) (Var 0)))) = App (k7_tg \<beta>) (App (shift X) ?q)" by (simp only: k7_s0 subst0_shift)
  have b3: "App ?GX ?A \<rightarrow>\<^sub>\<beta> App (k7_tg \<beta>) (App (shift X) ?q)" using beta_contract.beta[of \<alpha> "App (k7_tg \<beta>) (App (shift (shift X)) (App (k7_th \<alpha>) (Var 0)))" ?A] unfolding e3 .
  note r = compatible_step.root[of beta_contract]
  have s1: "beta_eta_equiv \<Gamma> rc_u (App (k7_H \<alpha> \<beta>) (App ?G X)) ?M1" by (rule beta_eta_equiv.Beta[OF t0 t1 r[OF b1]])
  have s2: "beta_eta_equiv \<Gamma> rc_u ?M1 ?M2" by (rule beta_eta_equiv.Beta[OF t1 t2 compatible_step.Lam_body[OF compatible_step.App_right[OF compatible_step.App_left[OF r[OF b2]]]]])
  have s3: "beta_eta_equiv \<Gamma> rc_u ?M2 ?M3" by (rule beta_eta_equiv.Beta[OF t2 t3 compatible_step.Lam_body[OF compatible_step.App_right[OF r[OF b3]]]])
  have s4: "beta_eta_equiv \<Gamma> rc_u ?M3 ?M4" by (rule k7_be_lam[OF k7_be_t[OF tb has_type.App[OF sX q]] refl])
  have s5: "beta_eta_equiv \<Gamma> rc_u ?M4 ?M5" by (rule k7_be_lam[OF k7_be_arg[OF k7_be_t[OF ta v0(1)] sX] refl])
  have s6: "beta_eta_equiv \<Gamma> rc_u ?M5 X" by (rule beta_eta_equiv.Eta[OF beta_eta_equiv_right_type[OF s5] X compatible_step.root[of eta_contract, OF eta_contract.eta[of Prop X]]])
  show ?thesis by (rule beta_eta_equiv.Trans[OF s1 beta_eta_equiv.Trans[OF s2 beta_eta_equiv.Trans[OF s3 beta_eta_equiv.Trans[OF s4 beta_eta_equiv.Trans[OF s5 s6]]]]])
qed

lemma k7_rB: assumes "k7_tonly \<alpha>" "k7_tonly \<beta>" shows "k7_retr (\<alpha> \<rightarrow>\<^sub>o \<beta>) (k7_G \<alpha> \<beta>) (k7_H \<alpha> \<beta>)"
  unfolding k7_retr_def using k7_GH[OF assms] k7_be_u[OF assms] by (simp add: k7_G_def k7_H_def k7_cl)

theorem k7_HT1: assumes t: "k7_tonly \<tau>" and n: "\<tau> \<noteq> Prop" shows "[] ; pp_CFP_axioms \<turnstile>\<^sub>CEV\<^sub>s Neg (pp_purity_of_pure \<tau>)"
  using t n by (cases \<tau>) (auto intro: k7[OF k7_rB])

section \<open>10. U's theorem S, carried to C\<close>

lemma u_S_C: "[] \<turnstile>\<^sub>CEV Imp rcS (Neg rcExUni)" by (rule U_sub_CEV[OF u_S])

end
